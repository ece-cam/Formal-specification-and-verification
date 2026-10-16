"""Regenerate isolated section 5.4 variants and fairness check configurations.

The submitted production algorithms and trash_data.tla are never changed.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'investigations'
OUT.mkdir(exist_ok=True)
checks = [c for c in json.loads((ROOT / 'checks.json').read_text())
          if c['group'] in ('single', 'multiple')]
INVARIANTS = ['TypeOK', 'MessagesOK', 'CapacitiesRespected', 'TrapNotDestroyed',
              'CapacityNotExceeded', 'OuterDoorLocked', 'RamOuterDoor', 'AuthorizedOpenOnly']
PROPERTIES = ['TrashEmptied', 'UserTrash', 'UserTrashDeposited', 'TruckEmpties']


def config(name, module, values, properties=(), invariants=INVARIANTS,
           spec='Spec', expected='pass', extra='', group='investigations'):
    content = ('INIT Init\nNEXT Next\n' if spec is None else 'SPECIFICATION ' + spec + '\n')
    content += '\nCONSTANTS\n' + ''.join(f'  {k} = {v}\n' for k, v in zip(
        ['NumBins', 'NumUsers', 'NumTrucks', 'MaxCapacity', 'MaxUserTrash'], values))
    content += '\nCHECK_DEADLOCK TRUE\n'
    if invariants:
        content += '\nINVARIANTS\n' + ''.join('  ' + x + '\n' for x in invariants)
    if properties:
        content += '\nPROPERTIES\n' + ''.join('  ' + x + '\n' for x in properties)
    content += '\n' + extra
    path = OUT / (name + '.cfg')
    path.write_text(content, encoding='utf-8')
    checks.append(dict(name=name, module=module, config=path.relative_to(ROOT).as_posix(),
                       expected=expected, group=group))


STRONG = r'''
StrongSpec == /\ Init /\ [][Next]_vars
              /\ \A self \in Bins: SF_vars(binProcess(self))
              /\ \A self \in Users: SF_vars(userProcess(self))
              /\ SF_vars(serverProcess)
              /\ \A self \in Trucks: SF_vars(truckProcess(self))
              /\ SF_vars(controlProcess)

\* Deliberately omit the strong fairness on the user close acknowledgement.
ProcessWeakSpec ==
  /\ Init /\ [][Next]_vars
  /\ (\A b \in Bins: WF_vars(binProcess(b)))
  /\ (\A u \in Users: WF_vars(userProcess(u)))
  /\ WF_vars(serverProcess)
  /\ (\A t \in Trucks: WF_vars(truckProcess(t)))
  /\ WF_vars(controlProcess)
'''
(OUT / 'trash_scenarios.tla').write_text('''---------------- MODULE trash_scenarios ----------------
EXTENDS trash_multiple
AnyCard(user) == {TRUE, FALSE}
NoCard(user) == {FALSE}
''' + STRONG + '\n========================================================\n', encoding='utf-8')

for prop in PROPERTIES:
    config('unfair_' + prop, 'trash_single', (1,1,1,7,4), [prop],
           spec=None, expected='temporal', group='unfair')
for prop in ('UserTrash', 'UserTrashDeposited'):
    config('users_weak_' + prop, 'investigations/trash_scenarios', (1,2,1,3,2), [prop],
           spec='ProcessWeakSpec', expected='temporal' if prop == 'UserTrash' else 'pass')
    config('declined_' + prop, 'investigations/trash_scenarios', (2,1,1,3,2), [prop],
           expected='temporal', extra='CONSTANT ValidCard <- AnyCard\n')
config('declined_other', 'investigations/trash_scenarios', (2,1,1,3,2), ['TrashEmptied', 'TruckEmpties'],
       extra='CONSTANT ValidCard <- AnyCard\n')
config('invalid_card_safety', 'investigations/trash_scenarios', (1,1,1,3,2),
       extra='CONSTANT ValidCard <- NoCard\n')

source = (ROOT / 'trash_multiple.tla').read_text().split('\\* BEGIN TRANSLATION')[0].rstrip()
# A newly generated variant has no translation yet; trim any module end marker.
source = source.split('\n=====')[0]
sensor = source.replace('MODULE trash_multiple', 'MODULE trash_no_sensor').replace(
    'await binSensor[currentScan.bin].sensor = "outer_door_closed"\n                /\\ binCommand[currentScan.bin].command = "finished";',
    'await binCommand[currentScan.bin].command = "finished";')
assert sensor != source and 'await binSensor[currentScan.bin].sensor' not in sensor
(OUT / 'trash_no_sensor.tla').write_text(sensor + '\n\n' + '=' * 77 + '\n', encoding='utf-8')
config('sensor_finished_only', 'investigations/trash_no_sensor', (1,1,1,3,2), expected='assertion')

maximum = source.replace('MODULE trash_multiple', 'MODULE trash_max_compressed').replace(
    'with amt \\in 1..MaxUserTrash do\n          userTrash[self] := amt;\n        end with;',
    'userTrash[self] := IF self = UserOffset THEN 4 ELSE 6;').replace(
    'TrashFitsCapacity(currentScan.bin, MaxUserTrash)',
    'TrashFitsCapacity(currentScan.bin, userTrash[currentScan.user])').replace(
    'write(pendingBins, currentScan.bin);',
    '\\* Collection is disabled only in this isolated investigation.\n            skip;')
assert 'userTrash[self] := IF' in maximum
maximum += '\n\nBelowFive == trashCompressed[1] < 5\nAtMostFive == trashCompressed[1] <= 5\n'
(OUT / 'trash_max_compressed.tla').write_text(maximum + '\n' + '=' * 77 + '\n', encoding='utf-8')
config('compressed_reach_five', 'investigations/trash_max_compressed', (1,2,1,7,6),
       invariants=INVARIANTS + ['BelowFive'], expected='invariant:BelowFive')
config('compressed_bound_five', 'investigations/trash_max_compressed', (1,2,1,7,6),
       invariants=INVARIANTS + ['AtMostFive'])
(ROOT / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n', encoding='utf-8')
print(f'Prepared {len(checks)} checks.')
