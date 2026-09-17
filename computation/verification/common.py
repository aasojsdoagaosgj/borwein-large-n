"""Reconstructed verification utilities; OpenAI Codex, 2026-09-08."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if not __debug__:
    raise RuntimeError('Verification must run without Python -O / PYTHONOPTIMIZE.')
# Optional workspace-local installation; ordinary pip installations work as well.
local_dependencies = ROOT.parent / '.local-deps'
if local_dependencies.is_dir():
    sys.path.insert(0, str(local_dependencies))


def write_result(name, data, output_dir=None):
    directory = Path(output_dir) if output_dir else ROOT / 'results'
    directory.mkdir(parents=True, exist_ok=True)
    target = directory / name
    target.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(f'{target.name}: {data.get("status", "written")}', flush=True)


def metadata(kind):
    import mpmath
    return {'kind': kind, 'implementation': 'reconstructed_20260908',
            'python': sys.version.split()[0], 'mpmath': mpmath.__version__}
