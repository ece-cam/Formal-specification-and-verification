"""Replay a TLC starvation counterexample under original strong process fairness.

Every replay edge is conjoined with the original Next, and the initial state
with Init. This finite restriction supplies a counterexample, not a proof for
the unrestricted state space. It makes the strong-fairness experiment small.
"""
import json
import hashlib
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
log = (ROOT / 'verification/users_weak_UserTrashDeposited.log').read_text(encoding='utf-8')
metadata = json.loads((ROOT / 'verification/users_weak_UserTrashDeposited.run.json').read_text())
if metadata['modelSha256'] != hashlib.sha256((ROOT / 'trash_multiple.tla').read_bytes()).hexdigest():
    raise SystemExit('Rerun users_weak_UserTrashDeposited before regenerating its witness: the model changed.')
loop = int(re.search(r'Back to state (\d+):', log)[1])
model = (ROOT / 'trash_multiple.tla').read_text()
variables = re.search(r'vars == <<(.*?)>>', model, re.S)[1].replace('\n', '').split(',')
variables = [v.strip() for v in variables]
states = []
for number, body in re.findall(r'^State (\d+): (.*?)(?=^State \d+:|^Back to state|\Z)', log, re.M | re.S):
    data = {k: v.strip() for k, v in re.findall(r'^/\\ (\w+) = (.*?)(?=^/\\|\Z)', body, re.M | re.S)}
    states.append('<<' + ',\n'.join(data[v] for v in variables) + '>>')
source = '---------------- MODULE trash_fair_cycle ----------------\nEXTENDS trash_multiple\nVARIABLE replayIndex\n'
source += 'Witness == <<\n' + ',\n'.join(states) + '\n>>\n'
source += f'''WitnessInit == /\\ Init /\\ replayIndex = 1 /\\ vars = Witness[1]
WitnessNext == /\\ Next
               /\\ replayIndex' = IF replayIndex = {len(states)} THEN {loop} ELSE replayIndex + 1
               /\\ vars' = Witness[replayIndex']
WitnessType == replayIndex \\in 1..{len(states)}
FairCycleSpec ==
  /\\ WitnessInit
  /\\ [][WitnessNext]_<<vars, replayIndex>>
  /\\ (\\A b \\in Bins: SF_vars(binProcess(b)))
  /\\ (\\A u \\in Users: SF_vars(userProcess(u)))
  /\\ SF_vars(serverProcess)
  /\\ (\\A t \\in Trucks: SF_vars(truckProcess(t)))
  /\\ SF_vars(controlProcess)
========================================================
'''
(ROOT / 'investigations/trash_fair_cycle.tla').write_text(source, encoding='utf-8')
checks = json.loads((ROOT / 'checks.json').read_text())
for check in checks:
    if not check['name'].startswith('users_strong_'):
        continue
    check['module'] = 'investigations/trash_fair_cycle'
    check['timeout'] = 300
    config = ROOT / check['config']
    config.write_text(config.read_text().replace('SPECIFICATION StrongSpec', 'SPECIFICATION FairCycleSpec'))
(ROOT / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
print(f'Prepared original-model witness: {len(states)} states, loop to state {loop}.')
