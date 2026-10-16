"""Translate PlusCal and run reproducible checks using the course's TLC 1.7.4."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
JAR = Path(os.environ.get('TLA_JAR', ROOT.parent / '.tools/tla-1.7.4/tla2tools.jar'))
LOCAL_JAVA = Path('C:/Program Files (x86)/Java/jre1.8.0_503/bin/java.exe')
JAVA = os.environ.get('JAVA', str(LOCAL_JAVA) if LOCAL_JAVA.exists() else 'java')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dependencies(module):
    """Record local EXTENDS dependencies, including wrappers' production model."""
    found = {}
    def visit(path):
        for line in path.read_text(encoding='utf-8').splitlines():
            if not line.startswith('EXTENDS '):
                continue
            for name in line[8:].split(','):
                name = name.strip().split()[0]
                target = path.parent / (name + '.tla')
                if not target.exists():
                    target = ROOT / (name + '.tla')
                if target.exists():
                    key = target.relative_to(ROOT).as_posix()
                    if key not in found:
                        found[key] = digest(target)
                        visit(target)
    visit(ROOT / (module + '.tla'))
    return found


def current_result(check):
    path = ROOT / 'verification' / (check['name'] + '.run.json')
    if not path.exists():
        return False
    result = json.loads(path.read_text())
    return (result.get('expectedResultObserved') and result.get('expected') == check['expected']
            and result.get('modelSha256') == digest(ROOT / (check['module'] + '.tla'))
            and result.get('configSha256') == digest(ROOT / check['config'])
            and result.get('dataSha256') == digest(ROOT / 'trash_data.tla')
            and all(result.get('dependencies', {}).get(k, result.get('dataSha256') if k == 'trash_data.tla' else None) == v
                    for k, v in dependencies(check['module']).items()))


def translate(module):
    path = ROOT / (module + '.tla')
    source = path.read_text(encoding='utf-8')
    if '--algorithm' not in source and '--fair algorithm' not in source:
        # Investigation wrappers reuse the translated production algorithm.
        if 'EXTENDS trash_multiple' in source:
            translate('trash_multiple')
        return
    result = subprocess.run([JAVA, '-cp', str(JAR), 'pcal.trans', str(path)],
                            cwd=ROOT, capture_output=True, text=True)
    if result.returncode or 'Translation completed.' not in result.stdout:
        raise RuntimeError(result.stdout + result.stderr)


def run(check):
    name, module, config, expected = (check[k] for k in ('name', 'module', 'config', 'expected'))
    output = ROOT / 'verification'
    output.mkdir(exist_ok=True)
    states = (ROOT / 'states' / name).resolve()
    states.mkdir(parents=True, exist_ok=True)
    module_path = ROOT / (module + '.tla')
    command = [JAVA, '-Xmx768m', '-DTLA-Library=' + str(ROOT), '-cp', str(JAR), 'tlc2.TLC', '-workers', '1',
               '-fp', '0', '-metadir', str(states), '-config', str(ROOT / config), module_path.stem]
    log = output / (name + '.log')
    started = time.monotonic()
    timed_out = False
    with log.open('w', encoding='utf-8') as stream:
        process = subprocess.Popen(command, cwd=module_path.parent, stdout=stream, stderr=subprocess.STDOUT)
        try:
            code = process.wait(timeout=check.get('timeout', 300))
        except subprocess.TimeoutExpired:
            if os.name == 'nt':
                subprocess.run(['taskkill', '/PID', str(process.pid), '/T', '/F'], capture_output=True)
            else:
                process.kill()
            process.wait()
            timed_out = True
            code = -1
    elapsed = round(time.monotonic() - started, 3)
    content = log.read_text(encoding='utf-8')
    if expected == 'pass':
        matched = code == 0 and 'Model checking completed. No error has been found.' in content
    elif expected == 'temporal':
        matched = code != 0 and 'Temporal properties were violated' in content
    elif expected.startswith('invariant:'):
        matched = code != 0 and ('Invariant ' + expected.split(':')[1] + ' is violated') in content
    elif expected == 'assertion':
        matched = code != 0 and 'Failure of assertion' in content
    else:
        raise ValueError(expected)
    counts = re.findall(r'([\d,]+) states generated, ([\d,]+) distinct states found, ([\d,]+) states left on queue', content)
    summary = dict(check, exitCode=code, wallSeconds=elapsed, timedOut=timed_out,
                   expectedResultObserved=matched and not timed_out,
                   modelSha256=digest(ROOT / (module + '.tla')),
                   configSha256=digest(ROOT / config), dataSha256=digest(ROOT / 'trash_data.tla'),
                   dependencies=dependencies(module),
                   toolsSha256=digest(JAR), command=command)
    if counts:
        summary.update(zip(('generatedStates', 'distinctStates', 'queuedStates'),
                           (int(x.replace(',', '')) for x in counts[-1])))
    (output / (name + '.run.json')).write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    print(f"{name}: {'OK' if matched and not timed_out else 'UNEXPECTED'}; {elapsed}s; "
          f"{summary.get('distinctStates', '?')} distinct states; expected {expected}", flush=True)
    # Delete only this check's resolved state directory, never logs or sources.
    if states.is_relative_to((ROOT / 'states').resolve()) and states.name == name:
        try:
            shutil.rmtree(states)
        except OSError as error:
            print(f'Could not remove temporary checker states: {error}', flush=True)
    if not matched or timed_out:
        print(content[-6000:], flush=True)
    return summary['expectedResultObserved']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mode', default='suite', choices=['suite', 'all', 'single', 'multiple', 'unfair', 'investigations'])
    parser.add_argument('--check', help='Run one check by its manifest name')
    parser.add_argument('--failed', action='store_true', help='Rerun missing, failed, or stale results')
    args = parser.parse_args()
    checks = json.loads((ROOT / 'checks.json').read_text())
    selected = [c for c in checks if c['name'] == args.check] if args.check else [
        c for c in checks if args.mode == 'suite' or c['group'] == args.mode
        or (args.mode == 'all' and c['group'] in ('single', 'multiple'))]
    if args.failed:
        selected = [c for c in selected if not current_result(c)]
    if not selected:
        raise SystemExit('No checks selected')
    for module in dict.fromkeys(c['module'] for c in selected):
        translate(module)
    outcomes = [run(c) for c in selected]
    raise SystemExit(0 if all(outcomes) else 1)


if __name__ == '__main__':
    main()
