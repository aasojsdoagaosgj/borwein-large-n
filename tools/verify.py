"""Check the published bytes and Markdown file links; not a mathematical proof."""
from pathlib import Path
import hashlib
import json
import re
from urllib.parse import unquote

ROOT=Path(__file__).resolve().parents[1]

def require(condition,message):
    if not condition: raise RuntimeError(message)

def main():
    manifest=json.loads((ROOT/'manifest.json').read_text(encoding='utf-8'))
    require(manifest['algorithm']=='sha256','Unsupported manifest algorithm')
    files=manifest['files']
    for relative,expected in files.items():
        path=(ROOT/relative).resolve()
        require(ROOT in path.parents,'Unsafe relative path: '+relative)
        require(path.is_file(),'Missing file: '+relative)
        require(hashlib.sha256(path.read_bytes()).hexdigest()==expected,'Changed file: '+relative)
        if path.suffix=='.md':
            text=path.read_text(encoding='utf-8')
            for target in re.findall(r'\]\(([^)]+)\)',text):
                if re.match(r'^[A-Za-z][A-Za-z0-9+.-]*:',target) or target.startswith('#'): continue
                target=unquote(target.split('#')[0].strip('<>'))
                linked=(path.parent/target).resolve()
                require((linked==ROOT or ROOT in linked.parents) and linked.exists(),
                    'Broken local Markdown link in '+relative+': '+target)
    print('PASS:',len(files),'payload hashes and local Markdown file links.')
    print('No Lean compilation or interval calculation performed.')

if __name__=='__main__': main()
