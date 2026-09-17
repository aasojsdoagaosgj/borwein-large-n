#!/usr/bin/env python3
"""Rebuild and audit the Lean sources in an unpacked release.

This file is intended to be installed as ``tools/rebuild.py``.  It uses only
the Python standard library, never invokes Lake, and writes solely below
``.release-build``.  Run ``python tools/rebuild.py --check-only`` first.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "SOURCES.json"
BUILD = ROOT / ".release-build"
LIB = BUILD / "lib" / "lean"
LOGS = BUILD / "logs"
SETUPS = BUILD / "setup"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IMPORT_RE = re.compile(r"^(?:public\s+)?import\s+(all\s+)?([A-Za-z_][\w.]*)", re.M)
FORBIDDEN_RE = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")
QUALIFIED_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


class ReleaseError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise ReleaseError(message)


def relpath(value: Any, label: str) -> Path:
    if not isinstance(value, str) or not value:
        fail(f"{label} must be a non-empty relative path")
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        fail(f"{label} escapes the release root: {value!r}")
    return path


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def load_manifest() -> dict[str, Any]:
    if not MANIFEST.is_file():
        fail("SOURCES.json is missing from the release root")
    try:
        value = json.loads(MANIFEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read SOURCES.json: {exc}")
    if not isinstance(value, dict):
        fail("SOURCES.json must contain a JSON object")
    return value


def names_list(raw: Any, label: str) -> list[str]:
    if not isinstance(raw, list):
        fail(f"{label} must be an array")
    values = raw
    if not all(isinstance(v, str) and QUALIFIED_RE.fullmatch(v) for v in values):
        fail(f"{label} contains an invalid qualified name")
    return values


def read_sources(manifest: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], list[str], list[str]]:
    order = names_list(manifest.get("build_order"), "build_order")
    targets = names_list(manifest.get("targets"), "targets")
    if len(order) != len(set(order)):
        fail("build_order contains a duplicate module")
    if not set(targets) <= set(order):
        fail("every target module must occur in build_order")
    modules = {name: {"name": name,
                      "source": Path(name.replace(".", "/") + ".lean"),
                      "mode": None} for name in order}
    audits = names_list(manifest.get("audit_theorems"), "audit_theorems")
    return modules, order, audits


def strip_comments_and_strings(text: str) -> str:
    """Blank Lean comments and strings while preserving newlines and token gaps."""
    out: list[str] = []
    index, depth = 0, 0
    in_line, in_string, escaped = False, False, False
    while index < len(text):
        char = text[index]
        pair = text[index:index + 2]
        if in_line:
            if char == "\n":
                in_line = False
                out.append(char)
            else:
                out.append(" ")
            index += 1
        elif depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            out.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif pair == "--":
            in_line = True
            out.extend("  ")
            index += 2
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            index += 2
        elif char == '"':
            in_string = True
            out.append(" ")
            index += 1
        else:
            out.append(char)
            index += 1
    if depth or in_string:
        fail("unterminated block comment or string literal in Lean source")
    return "".join(out)


def source_info(modules: dict[str, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    info = {}
    for name, spec in modules.items():
        source = ROOT / spec["source"]
        if not source.is_file():
            fail(f"missing source for {name}: {spec['source'].as_posix()}")
        text = source.read_text(encoding="utf-8-sig")
        first = text.splitlines()[0].strip() if text.splitlines() else ""
        inferred = "module" if first == "module" else "legacy"
        if spec["mode"] not in (None, "module", "legacy"):
            fail(f"invalid mode for {name}: {spec['mode']!r}")
        if spec["mode"] and spec["mode"] != inferred:
            fail(f"declared mode for {name} disagrees with its first line")
        scanned = strip_comments_and_strings(text)
        if FORBIDDEN_RE.search(scanned):
            fail(f"forbidden proof placeholder or declaration in {spec['source'].as_posix()}")
        imports = [(bool(all_kw), dep) for all_kw, dep in IMPORT_RE.findall(scanned)]
        for _, dep in imports:
            if dep.startswith("Borwein.") and dep not in modules:
                fail(f"local import is absent from build_order: {name} imports {dep}")
        info[name] = {"path": source, "text": text, "mode": inferred, "imports": imports}
    return info


def check_data_references(manifest: dict[str, Any]) -> None:
    raw = manifest.get("data_files")
    hashes = manifest.get("data_sha256")
    if not isinstance(raw, list) or not all(isinstance(v, str) for v in raw):
        fail("data_files must be an array of relative paths")
    if not isinstance(hashes, dict) or set(hashes) != set(raw):
        fail("data_sha256 must map every data_files path exactly once")
    for value in raw:
        path = ROOT / relpath(value, "data file")
        if not path.is_file():
            fail(f"referenced file is missing: {value}")
        expected = hashes[value]
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-fA-F]{64}", expected):
            fail(f"invalid SHA-256 in data_sha256: {value}")
        if digest(path).lower() != expected.lower():
            fail(f"SHA-256 mismatch: {value}")


def check_source_hashes(manifest: dict[str, Any], modules: dict[str, Any]) -> None:
    hashes = manifest.get("source_sha256")
    expected_paths = {spec["source"].as_posix() for spec in modules.values()}
    if not isinstance(hashes, dict) or set(hashes) != expected_paths:
        fail("source_sha256 must map every build_order source path exactly once")
    for value, expected in hashes.items():
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-fA-F]{64}", expected):
            fail(f"invalid SHA-256 in source_sha256: {value}")
        if digest(ROOT / relpath(value, "source_sha256 path")).lower() != expected.lower():
            fail(f"SHA-256 mismatch: {value}")


def validate_graph(modules: dict[str, Any], order: list[str], info: dict[str, Any]) -> None:
    positions = {name: i for i, name in enumerate(order)}
    for name in order:
        for _, dep in info[name]["imports"]:
            if dep in modules and positions[dep] >= positions[name]:
                fail(f"build_order places {dep} after its importer {name}")


def find_lean() -> Path:
    candidate = os.environ.get("BORWEIN_LEAN") or shutil.which("lean")
    if not candidate:
        fail("Lean was not found; put lean on PATH or set BORWEIN_LEAN")
    path = Path(candidate).expanduser().resolve()
    if not path.is_file():
        fail(f"Lean executable does not exist: {candidate}")
    return path


def lean_prefix(lean: Path) -> Path:
    proc = subprocess.run([str(lean), "--print-prefix"], cwd=ROOT, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if proc.returncode:
        fail("lean --print-prefix failed: " + proc.stderr.strip())
    return Path(proc.stdout.strip()).resolve()


def library_roots(prefix: Path) -> list[Path]:
    roots = [LIB, ROOT / ".lake" / "build" / "lib" / "lean"]
    packages = ROOT / ".lake" / "packages"
    if packages.is_dir():
        roots.extend(sorted(p / ".lake" / "build" / "lib" / "lean" for p in packages.iterdir() if p.is_dir()))
    roots.append(prefix / "lib" / "lean")
    return [p for p in roots if p.is_dir()]


def artifact_inventory(roots: list[Path], private_names: set[str]) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    for root in roots:
        for obj in root.rglob("*.olean"):
            name = ".".join(obj.relative_to(root).with_suffix("").parts)
            if name in result:
                continue
            files = [str(obj.resolve())]
            ir, server, private = obj.with_suffix(".ir"), Path(str(obj) + ".server"), Path(str(obj) + ".private")
            if ir.is_file():
                files.append(str(ir.resolve()))
                if server.is_file():
                    files.append(str(server.resolve()))
            if name in private_names:
                if not private.is_file():
                    fail(f"import all requires a missing private sidecar for {name}")
                if len(files) != 3:
                    fail(f"import all requires public IR and server artifacts for {name}")
                files.append(str(private.resolve()))
            result[name] = files
    return result


def closure(selected: set[str], modules: dict[str, Any], info: dict[str, Any]) -> set[str]:
    pending = list(selected)
    while pending:
        name = pending.pop()
        if name not in modules:
            fail(f"unknown selected module: {name}")
        for _, dep in info[name]["imports"]:
            if dep in modules and dep not in selected:
                selected.add(dep)
                pending.append(dep)
    return selected


def run_logged(command: list[str], log: Path, env: dict[str, str]) -> tuple[int, float]:
    start = time.perf_counter()
    with log.open("wb") as stream:
        kwargs: dict[str, Any] = {}
        if os.name == "nt":
            kwargs["creationflags"] = subprocess.CREATE_NO_WINDOW
        proc = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                              stderr=subprocess.STDOUT, **kwargs)
    return proc.returncode, time.perf_counter() - start


def compile_release(lean: Path, prefix: Path, modules: dict[str, Any], order: list[str],
                    info: dict[str, Any], targets: list[str], chosen: set[str]) -> None:
    if BUILD.exists():
        fail(".release-build already exists; move it aside before a fresh rebuild so prior evidence is preserved")
    for directory in (LIB, LOGS, SETUPS):
        directory.mkdir(parents=True, exist_ok=True)
    roots = library_roots(prefix)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p.resolve()) for p in roots[:-1])
    state: dict[str, Any] = {"status": "building", "modules": []}
    write_json(BUILD / "state.json", state)
    for name in order:
        if name not in chosen:
            continue
        source = info[name]["path"]
        obj = LIB / Path(*name.split(".")).with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        log = LOGS / (name.replace(".", "_") + ".log")
        args = [str(lean)]
        setup_path = None
        if info[name]["mode"] == "module":
            private_names = {dep for all_kw, dep in info[name]["imports"] if all_kw}
            arts = artifact_inventory(library_roots(prefix), private_names)
            setup_path = SETUPS / (name.replace(".", "_") + ".json")
            write_json(setup_path, {"name": name, "isModule": True, "imports": None,
                       "importArts": arts, "dynlibs": [], "plugins": [], "options": {}})
            args.append("--setup=" + str(setup_path))
        args += ["-o", str(obj), str(source)]
        source_hash = digest(source)
        print(f"building {name}", flush=True)
        code, seconds = run_logged(args, log, env)
        if digest(source) != source_hash:
            fail(f"source changed during compilation: {source.relative_to(ROOT).as_posix()}")
        row = {"module": name, "source_sha256": source_hash, "exit_code": code,
               "seconds": round(seconds, 3), "log": log.relative_to(ROOT).as_posix()}
        if code == 0 and obj.is_file():
            row["output_sha256"] = digest(obj)
        state["modules"].append(row)
        write_json(BUILD / "state.json", state)
        if code:
            state.update({"status": "failed", "failed_module": name})
            write_json(BUILD / "state.json", state)
            sys.stderr.write(log.read_text(encoding="utf-8-sig", errors="replace"))
            fail(f"Lean failed while compiling {name}")
    # Qualified theorem namespaces need not mirror their source filenames.
    # A complete rebuild therefore audits the manifest verbatim.  For a partial
    # diagnostic build, include only names whose prefix unambiguously matches a
    # selected module name.
    audit_targets = (targets if chosen == set(order) else
                     [t for t in targets if any(t == n or t.startswith(n + ".") for n in chosen)])
    audit_is_module = bool(chosen) and all(info[name]["mode"] == "module" for name in chosen)
    audit_text = ("module\n" if audit_is_module else "")
    audit_text += "".join(f"import {name}\n" for name in order if name in chosen)
    audit_text += "\n" + "".join(f"#print axioms {name}\n" for name in audit_targets)
    audit = BUILD / "audit.lean"
    audit.write_text(audit_text, encoding="utf-8")
    audit_log = LOGS / "axioms.log"
    audit_args = [str(lean)]
    if audit_is_module:
        audit_setup = SETUPS / "audit.json"
        write_json(audit_setup, {"name": "ReleaseAxiomAudit", "isModule": True, "imports": None,
                   "importArts": artifact_inventory(library_roots(prefix), set()),
                   "dynlibs": [], "plugins": [], "options": {}})
        audit_args.append("--setup=" + str(audit_setup))
    audit_args.append(str(audit))
    code, seconds = run_logged(audit_args, audit_log, env)
    if code:
        state.update({"status": "failed", "failed_stage": "axiom_audit"})
        write_json(BUILD / "state.json", state)
        sys.stderr.write(audit_log.read_text(encoding="utf-8-sig", errors="replace"))
        fail("final axiom audit failed to compile")
    records = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
                         audit_log.read_text(encoding="utf-8-sig", errors="replace"))
    if [name for name, _ in records] != audit_targets:
        state.update({"status": "failed", "failed_stage": "axiom_audit_targets"})
        write_json(BUILD / "state.json", state)
        fail("final axiom audit did not report every requested target in order")
    for name, raw in records:
        axioms = {v.strip() for v in raw.split(",") if v.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            state.update({"status": "failed", "failed_stage": "axiom_audit_dependencies"})
            write_json(BUILD / "state.json", state)
            fail(f"non-standard axiom dependency for {name}: {sorted(axioms - ALLOWED_AXIOMS)}")
    state.update({"status": "passed", "audit_seconds": round(seconds, 3),
                  "audited_targets": audit_targets, "allowed_axioms": sorted(ALLOWED_AXIOMS)})
    write_json(BUILD / "state.json", state)
    print(f"rebuilt {len(state['modules'])} modules; audited {len(audit_targets)} targets", flush=True)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true", help="validate the release without invoking Lean")
    parser.add_argument("--only", action="append", default=[], metavar="MODULE",
                        help="build this module and its local dependencies (repeatable)")
    parser.add_argument("--limit", type=int, metavar="N", help="build at most the first N selected modules")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    manifest = load_manifest()
    modules, order, targets = read_sources(manifest)
    info = source_info(modules)
    validate_graph(modules, order, info)
    check_source_hashes(manifest, modules)
    check_data_references(manifest)
    if args.limit is not None and args.limit < 0:
        fail("--limit must be non-negative")
    selected = closure(set(args.only) if args.only else set(order), modules, info)
    selected_order = [name for name in order if name in selected]
    if args.limit is not None:
        selected_order = selected_order[:args.limit]
        selected = set(selected_order)
    if args.check_only:
        print(f"SOURCES.json is consistent: {len(modules)} modules, {len(targets)} audit targets")
        return 0
    lean = find_lean()
    prefix = lean_prefix(lean)
    compile_release(lean, prefix, modules, order, info, targets, selected)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ReleaseError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
