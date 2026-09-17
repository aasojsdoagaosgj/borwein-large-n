"""Verify the distribution's bytes and references; this is not a Lean proof check."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(4*1024*1024), b''):
            h.update(block)
    return h.hexdigest()

def main():
    manifest = json.loads((ROOT/'MANIFEST.sha256.json').read_text(encoding='utf-8'))
    assert manifest['algorithm'] == 'sha256'
    files = manifest['files']
    for relative, expected in files.items():
        p = (ROOT/relative).resolve()
        assert ROOT in p.parents, 'Unsafe manifest path'
        assert p.is_file() and sha(p) == expected, 'Changed or missing: '+relative
    sources = json.loads((ROOT/'SOURCES.json').read_text(encoding='utf-8'))
    modules = set(sources['build_order'])
    data = set(sources['data_files'])
    for name in modules:
        rel = name.replace('.', '/')+'.lean'
        assert files[rel] == sources['source_sha256'][rel]
        text = (ROOT/rel).read_text(encoding='utf-8-sig')
        for dep in re.findall(r'^(?:public\s+)?import\s+(?:all\s+)?(Borwein(?:\.[A-Za-z0-9_]+)+)', text, re.M):
            assert dep in modules, 'Missing import: '+dep
        for ref in re.findall(r'(?:window_nat_file(?:_u64)?|packed_nat_file)\s+"(notes/[A-Za-z0-9_./-]+\.bin)"', text):
            assert ref in data and ref in files, 'Missing numerical input: '+ref
    for rel in data:
        assert files[rel] == sources['data_sha256'][rel]
    for rel in files:
        assert not any(part in {'.git', '.lake', '.local-deps', '__pycache__'} for part in Path(rel).parts)
        if rel.endswith('.bin'):
            continue
        text = (ROOT/rel).read_text(encoding='utf-8-sig')
        assert not re.search(r'(?i)\b[A-Z]:[\\/](?:Users|Documents and Settings)[\\/][^\s\\/"<>]+', text), rel
        assert not re.search(r'/(?:home|Users)/[A-Za-z0-9_.-]+', text), rel
        assert not re.search(r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b', text), rel
    print(f'PASS: {len(files)} files; {len(modules)} local Lean modules; {len(data)} numerical inputs.')
    print('File integrity and static references checked. No Lean compilation performed.')

if __name__ == '__main__':
    try:
        main()
    except (AssertionError, ValueError, OSError, KeyError) as e:
        print('FAIL:', e, file=sys.stderr)
        raise SystemExit(1)
