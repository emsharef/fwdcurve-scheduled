"""Check local guide links, TeX dependencies, source integrity, and packaging."""
from pathlib import Path
import hashlib
import json
import re
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]


def main():
    guides = list(ROOT.glob('*.md')) + list((ROOT/'docs').glob('*.md'))
    guides += list((ROOT/'papers').glob('*/README.md'))
    for p in guides:
        for link in re.findall(r'\]\(([^)]+)\)',p.read_text()):
            if '://' in link or link.startswith(('#','mailto:')):
                continue
            target = unquote(link.split('#')[0])
            assert (p.parent/target).exists(), f'Broken link in {p.relative_to(ROOT)}: {link}'
    for folder in ['structure','identification','lab']:
        directory = ROOT/'papers'/folder
        assert (directory/'paper.pdf').read_bytes().startswith(b'%PDF'), f'Missing PDF: {folder}'
        for p in directory.rglob('*.tex'):
            if 'build' in p.parts:
                continue
            for kind, name in re.findall(r'\\(input|includegraphics)(?:\[[^\]]*\])?\{([^}]+)\}',p.read_text()):
                target = directory/name
                if kind=='input' and not target.suffix:
                    target = target.with_suffix('.tex')
                assert target.exists(), f'Missing TeX dependency: {folder}/{name}'
    source = json.loads((ROOT/'docs/source-snapshot.json').read_text())
    unchanged = 0
    for row in source['files']:
        if row['path'].startswith('lean/') or row['path'] in [
            'papers/lab/PAPER.md','papers/lab/main.tex','papers/lab/refs.bib']:
            sha = hashlib.sha256((ROOT/row['path']).read_bytes()).hexdigest()
            assert sha==row['source_sha256'], f'Archived source changed: {row["path"]}'
            unchanged += 1
    forbidden = ['board','agents','ops','.claude','.codex','.env']
    assert not any((ROOT/x).exists() for x in forbidden), 'Internal lab/config files in package'
    for p in (ROOT/'lean').rglob('*.lean'):
        if '.lake' in p.parts:
            continue
        # Lean's Audit provides the semantic check; this catches obvious unfinished source.
        text = re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S)
        text = re.sub(r'--[^\n]*','',text)
        text = re.sub(r'"(?:\\.|[^"\\])*"','',text)
        assert not re.search(r'\b(sorry|admit|axiom)\b',text), f'Unfinished proof or global axiom: {p}'
    print(f'Package checked: {len(guides)} guides, TeX dependencies, {unchanged} unchanged archived/formal sources.')


if __name__=='__main__':
    main()
