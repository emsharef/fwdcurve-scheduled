"""Check prepared-input hashes, sample counts, and saved numerical benchmarks."""
from pathlib import Path
import hashlib
import json
import math

ROOT = Path(__file__).resolve().parents[1]


def compare(expected, actual, path):
    if isinstance(expected, dict):
        assert set(expected)==set(actual), f'Keys differ: {path}'
        for key, value in expected.items():
            compare(value, actual[key], path+'/'+key)
    elif isinstance(expected, list):
        assert len(expected)==len(actual), f'Length differs: {path}'
        for i, (a,b) in enumerate(zip(expected,actual)):
            compare(a,b,path+f'/{i}')
    elif isinstance(expected, float):
        assert math.isfinite(actual), f'Nonfinite result: {path}'
        assert math.isclose(expected,actual,rel_tol=1e-5,abs_tol=1e-3), (path,expected,actual)
    else:
        assert expected==actual, (path,expected,actual)


def main():
    data = ROOT/'papers/identification/data/processed'
    hashes = json.loads((ROOT/'papers/identification/analysis/input_hashes.json').read_text())
    # The independent release snapshot prevents a regenerated hash file hiding changed inputs.
    source = json.loads((ROOT/'docs/source-snapshot.json').read_text())
    recorded = {r['path']:r['source_sha256'] for r in source['files']}
    for name, sha in hashes.items():
        path = data/name
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        assert actual==sha==recorded[str(path.relative_to(ROOT))], f'Input changed: {name}'
    expected = json.loads((ROOT/'docs/expected-results.json').read_text())
    for name, value in expected.items():
        compare(value,json.loads((ROOT/name).read_text()),name)
    summary = json.loads((ROOT/'papers/identification/analysis/summary.json').read_text())
    assert summary['dates']==78 and summary['chains']==555 and summary['selected_strikes']==4100
    print(f'Checked {len(hashes)} input hashes and {len(expected)} numerical benchmark files; '
          '78 dates, 555 chains, 4,100 strikes.')


if __name__ == '__main__':
    main()
