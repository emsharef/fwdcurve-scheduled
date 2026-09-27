"""Standalone, offline paper reproduction. Run from any directory."""
from pathlib import Path
import argparse
import json
import os
import platform
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('target', choices=['examples', 'analysis', 'papers', 'all'])
    p.add_argument('--refit', action='store_true',
                   help='refit all mixture chains instead of using supplied fits')
    a = p.parse_args()
    build = ROOT / 'build'
    build.mkdir(exist_ok=True)
    env = os.environ.copy()
    env['MPLCONFIGDIR'] = str(build / 'matplotlib')
    os.environ['MPLCONFIGDIR'] = env['MPLCONFIGDIR']
    report = {'python': sys.version, 'platform': platform.platform(),
              'target': a.target, 'refit': a.refit, 'steps': []}
    if a.target != 'papers':
        import numpy, scipy, matplotlib
        report['versions'] = {m.__name__: m.__version__ for m in (numpy, scipy, matplotlib)}

    def run(name, cmd, cwd=ROOT):
        log = build / (name + '.log')
        print(f'Running {name}; log: {log.relative_to(ROOT)}', flush=True)
        start = time.monotonic()
        with log.open('w') as f:
            result = subprocess.run(cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT)
        report['steps'].append({'name': name, 'seconds': round(time.monotonic()-start, 2),
                                'exit_code': result.returncode})
        (build / 'reproduction.json').write_text(json.dumps(report, indent=2)+'\n')
        if result.returncode:
            print(log.read_text()[-6000:], file=sys.stderr)
            raise SystemExit(result.returncode)

    if a.target in ['examples', 'all']:
        for name, path in [
            ('structure-figures', 'papers/structure/examples/make_figures.py'),
            ('structure-checks', 'papers/structure/examples/check_structural_additions.py'),
            ('identification-examples', 'papers/identification/examples/make_examples.py'),
            ('calendar-examples', 'papers/identification/analysis/calendar_examples.py')]:
            run(name, [sys.executable, str(ROOT/path)])
    if a.target in ['analysis', 'all']:
        for name in ['run_analysis', 'decompose_fit', 'extend_empirics',
                     'calendar_examples', 'round2_analysis', 'round3_analysis']:
            cmd = [sys.executable, str(ROOT/'papers/identification/analysis'/f'{name}.py')]
            if name == 'extend_empirics' and a.refit:
                cmd.append('--refit')
            run(name, cmd)
        run('check-results', [sys.executable, str(ROOT/'scripts/check_results.py')])
    if a.target in ['papers', 'all']:
        if not shutil.which('tectonic'):
            raise SystemExit('Install Tectonic and put it on PATH to compile the papers.')
        for folder, entry, output in [('structure','main','paper'),
                                       ('structure','verification','verification'),
                                       ('identification','main','paper'), ('lab','main','paper')]:
            directory = ROOT/'papers'/folder
            (directory/'build').mkdir(exist_ok=True)
            run(f'{folder}-{entry}', ['tectonic','--keep-logs','--keep-intermediates',
                                      '--outdir','build',f'{entry}.tex'], directory)
            shutil.copy2(directory/'build'/f'{entry}.pdf', directory/f'{output}.pdf')
        run('proof-map', [sys.executable, str(ROOT/'scripts/proof_map.py'), '--check'])
    print('Completed:', a.target, flush=True)


if __name__ == '__main__':
    main()
