"""Render/check publication-to-lab-to-Lean correspondence; no lab tooling."""
from pathlib import Path
import argparse
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
KINDS = 'theorem|proposition|lemma|corollary'


def read(name):
    return json.loads((ROOT/'docs'/name).read_text())


def declaration_link(name):
    module, decl = name.rsplit('.', 1)
    path = 'lean/' + module.replace('.', '/') + '.lean'
    text = (ROOT/path).read_text()
    match = re.search(r'\b(?:theorem|lemma|def|abbrev)\s+'+re.escape(decl)+r'\b', text)
    if not match:
        raise ValueError(f'Declaration not found: {name} in {path}')
    line = text.count('\n', 0, match.start()) + 1
    return f'[`{name}`](../{path}#L{line})'


def lab_link(label):
    path = ROOT/'papers/lab/PAPER.md'
    text = path.read_text()
    # Original statements have bold result headings; first bold occurrence is the target.
    match = re.search(r'\*\*'+re.escape(label)+r'(?:\.|\s|\*)', text)
    if not match:
        raise ValueError(f'Original result not found: {label}')
    line = text.count('\n', 0, match.start()) + 1
    return f'[{label}](../papers/lab/PAPER.md#L{line})'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--lean', action='store_true', help='also elaborate every mapped declaration')
    args = parser.parse_args()
    entries = read('proof-map.json')
    lab = read('lab-results.json')
    found = {}
    for paper in ['structure', 'identification']:
        for path in sorted((ROOT/'papers'/paper/'sections').glob('*.tex')):
            text = path.read_text()
            for m in re.finditer(r'\\begin\{('+KINDS+r')\}(?:\[[^\]]*\])?\s*\\label\{([^}]+)\}', text):
                found[(paper, m[2])] = (path, m[1].title(), text.count('\n', 0, m.start())+1)
    mapped = {(r['paper'], r['label']) for r in entries}
    if set(found) != mapped:
        raise ValueError(f'Coverage mismatch: unmapped={set(found)-mapped}; missing={mapped-set(found)}')

    header = '''# Publication results and formal proofs

Every numbered theorem, proposition, lemma, and corollary in the two edited
papers appears below. Follow a publication link to its statement, an original
result link to the full research manuscript, and a Lean link to the exact
declaration. Definition and example environments are not theorem claims.

**Coverage is result-specific.** A corresponding Lean proof can cover a source
result without covering every extension in the edited paper. Read the scope
column and the hypotheses of the linked statement. In particular, general
American exercise, the sharper approximation constants, and numerical fits
are not fully formalized. See the [formalization guide](formalization.md).

The map is generated from [proof-map.json](proof-map.json) and
[lab-results.json](lab-results.json). `python scripts/proof_map.py --check`
checks statement coverage and declaration locations; add `--lean` after the
Lean build to elaborate every linked declaration.
'''
    lines = [header]
    for paper, title in [('structure','Forward-curve structure'), ('identification','Identification and factor restrictions')]:
        lines += [f'\n## {title}\n', '| Publication result | Original result | Lean entry points | Scope |',
                  '|---|---|---|---|']
        aux = ROOT/'papers'/paper/'build/main.aux'
        numbers = dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)', aux.read_text())) if aux.exists() else {}
        for r in (r for r in entries if r['paper']==paper):
            path, kind, line = found[(paper,r['label'])]
            number = numbers.get(r['label'], r.get('number'))
            if not number:
                raise ValueError('Build the paper once to get its numbering: '+r['label'])
            if args.check and r.get('number') != number:
                raise ValueError(f'Stale number for {r["label"]}: {r.get("number")} vs {number}')
            r['number'] = number
            statement = f'[{kind} {number}](../{path.relative_to(ROOT)}#L{line})'
            originals = '<br>'.join(lab_link(x) for x in r['lab_results']) or 'Publication proof'
            lean = '<br>'.join(declaration_link(x) for x in r['declarations']) or 'No matching Lean theorem'
            lines.append(f'| {statement} | {originals} | {lean} | {r["scope"]} |')
    lines += ['''
## Further results used in the exposition

The first paper also uses original Theorem 1 (the pure-step obstruction),
Proposition 10 and Theorem 11 (combined diffusion/announcements), and Propositions 38 and
45 (polynomial and Nelson–Siegel blocks). The second uses original Proposition
19 (designed futures windows), Proposition 24 (listed calendar), Corollaries
21–22 (specialized exercise), and Proposition 23 (futures-style exercise).
Their declarations and the remaining original results are in the complete
[lab-result index](lab-results.md). Results appearing only in the original
manuscript have not thereby been added to the edited papers.

Empirical LP endpoints, smile fits, loading selection, numerical ranks and
conditioning, discrete-outcome examples, and hedge calculations are checked
by the Python programs. They are not Lean theorems. A fit to listed American
settlements using a European diagnostic is not a formal listed-American
pricing result.
''']
    lab_lines = ['# Original research results and Lean declarations\n',
                 'This index preserves the original coverage qualifications. Historical claim numbers identify source entries; they are not publication theorem numbers. The original Markdown and PDF are in [papers/lab](../papers/lab/).\n',
                 '| Original result | Lean statement and proof | Recorded formal scope |', '|---|---|---|']
    for r in lab:
        originals = '<br>'.join(lab_link(x) for x in r['lab_results'])
        lean = '<br>'.join(declaration_link(x) for x in r['declarations'])
        lab_lines.append(f'| {originals} | {lean} | {r["scope"]} |')
    outputs = {'proof-map.md':'\n'.join(lines).rstrip()+'\n', 'lab-results.md':'\n'.join(lab_lines).rstrip()+'\n',
               'proof-map.json':json.dumps(entries,indent=2)+'\n'}
    for name, text in outputs.items():
        path = ROOT/'docs'/name
        if args.check:
            if not path.exists() or path.read_text()!=text:
                raise ValueError('Generated map is stale: '+name)
        else:
            path.write_text(text)
    if args.lean:
        declarations = sorted({d for r in entries+lab for d in r['declarations']})
        target = ROOT/'lean/.lake/ProofMapCheck.lean'
        target.parent.mkdir(exist_ok=True)
        target.write_text('import Novel\nimport Standalone\n'+''.join(f'#check {d}\n' for d in declarations))
        subprocess.run(['lake','env','lean',str(target)], cwd=ROOT/'lean',check=True)
    print(f'Map checked: {len(entries)} publication statements, {len(lab)} source entries.')


if __name__ == '__main__':
    main()
