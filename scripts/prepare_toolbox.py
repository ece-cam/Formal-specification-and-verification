"""Create Toolbox models that select the correct module without editing EXTENDS."""
from pathlib import Path
import re
import shutil
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
models = [('trash_single', 'Model_formal', 'trash_single.cfg'),
          ('trash_multiple', 'Bins', 'multiple_bins.cfg'),
          ('trash_multiple', 'Users', 'multiple_users.cfg'),
          ('trash_multiple', 'Trucks', 'multiple_trucks.cfg')]
for module, name, config in models:
    content = (ROOT / config).read_text()
    launch = ET.Element('launchConfiguration', type='org.lamport.tla.toolbox.tool.tlc.modelCheck')
    for key, value in [('configurationName', name), ('specName', module),
                       ('modelBehaviorSpec', 'Spec'), ('modelBehaviorInit', ''), ('modelBehaviorNext', ''),
                       ('modelComments', 'See REPORT.md for expected Users liveness counterexamples.')]:
        ET.SubElement(launch, 'stringAttribute', key=key, value=value)
    for key, value in [('modelBehaviorSpecType', '1'), ('numberOfWorkers', '1'),
                       ('fpIndex', '0'), ('maxHeapSize', '25')]:
        ET.SubElement(launch, 'intAttribute', key=key, value=value)
    ET.SubElement(launch, 'booleanAttribute', key='modelCorrectnessCheckDeadlock', value='true')
    constants = ET.SubElement(launch, 'listAttribute', key='modelParameterConstants')
    for key, value in re.findall(r'^  (\w+) = (\d+)$', content, re.M):
        ET.SubElement(constants, 'listEntry', value=f'{key};;{value};0;0')
    for heading, key in [('INVARIANTS', 'modelCorrectnessInvariants'), ('PROPERTIES', 'modelCorrectnessProperties')]:
        element = ET.SubElement(launch, 'listAttribute', key=key)
        section = content.split(heading + '\n', 1)[1].split('\n\n')[0]
        for prop in section.split():
            ET.SubElement(element, 'listEntry', value='1' + prop)
    directory = ROOT / (module + '.toolbox')
    directory.mkdir(exist_ok=True)
    ET.indent(launch)
    ET.ElementTree(launch).write(directory / f'{module}___{name}.launch', encoding='utf-8', xml_declaration=True)
shutil.copyfile(ROOT / 'multiple_bins.cfg', ROOT / 'trash_multiple.cfg')
