"""Build the combined PDF and the TLA-only submission ZIP from verified inputs."""
from pathlib import Path
import hashlib
import html
import json
import re
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT.parent / '.tools/reporting'))
from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.platypus import Paragraph, Preformatted, SimpleDocTemplate, Spacer, Table, TableStyle


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


checks = json.loads((ROOT / 'checks.json').read_text())
runs = {}
for check in checks:
    run = json.loads((ROOT / 'verification' / (check['name'] + '.run.json')).read_text())
    if not run.get('expectedResultObserved'):
        raise RuntimeError('Unverified check: ' + check['name'])
    for field, path in [('modelSha256', ROOT / (check['module'] + '.tla')),
                        ('configSha256', ROOT / check['config']),
                        ('dataSha256', ROOT / 'trash_data.tla')]:
        if sha(path) != run[field]:
            raise RuntimeError(f'Stale verification for {check["name"]}: {path.name}')
    runs[check['name']] = run

main_table = '| Configuration (B,U,T,C,M) | Distinct states | Wall time (s) | Outcome |\n'
main_table += '| --- | --- | --- | --- |\n'
for name, label in [('trash_single', 'Single (1,1,1,7,4)'), ('multiple_bins', 'Bins (2,1,1,3,2)'),
                    ('multiple_users', 'Users (1,2,1,3,2)'), ('multiple_trucks', 'Trucks (2,1,2,2,1)')]:
    r = runs[name]
    result = 'Two user liveness failures' if name == 'multiple_users' else 'All checks pass'
    main_table += f'| {label} | {r["distinctStates"]:,} | {r["wallSeconds"]:.3f} | {result} |\n'
r = runs['multiple_users_other']
main_table += (f'\nThe additional complete Users safety/collection run visited {r["distinctStates"]:,} '
               f'distinct states in {r["wallSeconds"]:.3f} seconds. B, U and T are component counts; '
               'C is MaxCapacity and M is MaxUserTrash. Distinct-state counts do not include '
               'the multiplicity of temporal-checking branches.\n')

extra = '| Experiment | Visited states | Seconds | Observed result |\n| --- | --- | --- | --- |\n'
labels = {
    'users_weak_UserTrash': 'Users, weak fairness: UserTrash',
    'users_weak_UserTrashDeposited': 'Users, weak fairness: deposited',
    'users_strong_UserTrash': 'Strong-fair witness: UserTrash',
    'users_strong_UserTrashDeposited': 'Strong-fair witness: deposited',
    'declined_UserTrash': 'Declined cards: UserTrash',
    'declined_UserTrashDeposited': 'Declined cards: deposited',
    'declined_other': 'Declined cards: other checks',
    'invalid_card_safety': 'Always-invalid card: safety',
    'sensor_finished_only': 'Door wait uses finished only',
    'compressed_reach_five': 'Compressed amount < 5',
    'compressed_bound_five': 'Compressed amount <= 5',
}
for name, label in labels.items():
    r = runs[name]
    expected = r['expected']
    result = {'pass': 'Pass', 'temporal': 'Temporal counterexample', 'assertion': 'Assertion failure',
              'invariant:BelowFive': 'Invariant counterexample'}[expected]
    extra += f'| {label} | {r["distinctStates"]:,} | {r["wallSeconds"]:.3f} | {result} |\n'
extra += ('\nCounterexample searches may stop before exhausting the reachable graph. The 178-state '
          'strong-fairness results describe the restricted replay witness. All-pass experiments '
          'exhaust their finite graphs. The four no-fairness experiments each visited '
          '5,286 distinct states and produced the expected temporal violation; their timings '
          'are recorded in the corresponding JSON files.\n')

report_path = ROOT / 'REPORT.md'
content = report_path.read_text(encoding='utf-8')
for name, replacement in [('MEASUREMENTS', main_table), ('INVESTIGATION RESULTS', extra)]:
    pattern = f'<!-- BEGIN {name} -->.*?<!-- END {name} -->'
    content = re.sub(pattern, f'<!-- BEGIN {name} -->\n\n{replacement}\n<!-- END {name} -->', content, flags=re.S)
report_path.write_text(content, encoding='utf-8')

styles = getSampleStyleSheet()
styles.add(ParagraphStyle('ReportBody', fontName='Helvetica', fontSize=9.7, leading=13,
                          spaceAfter=6, textColor=colors.HexColor('#202b37')))
styles.add(ParagraphStyle('ReportCode', fontName='Courier', fontSize=7.6, leading=10.1,
                          spaceBefore=5, spaceAfter=9, leftIndent=7))
styles.add(ParagraphStyle('ReportCell', fontName='Helvetica', fontSize=8.1, leading=10.6,
                          splitLongWords=True, spaceAfter=0))
styles['Title'].fontSize = 21
styles['Title'].leading = 25
styles['Title'].alignment = TA_LEFT
styles['Title'].textColor = colors.HexColor('#143753')
for name in ('Heading1', 'Heading2'):
    styles[name].textColor = colors.HexColor('#143753')
    styles[name].spaceBefore = 14
    styles[name].spaceAfter = 7
styles['Heading1'].fontSize = 14
styles['Heading1'].leading = 18
styles['Heading2'].fontSize = 11.5
styles['Heading2'].leading = 15


def inline(text):
    text = html.escape(text)
    text = re.sub(r'`([^`]+)`', r'<font name="Courier" size="8.4">\1</font>', text)
    return re.sub(r'\*\*(.+?)\*\*', r'<b>\1</b>', text)


flow = []
lines = content.splitlines()
i = 0
width = A4[0] - 88
while i < len(lines):
    line = lines[i]
    if not line.strip() or line.startswith('<!--'):
        i += 1
        continue
    if line.startswith('```'):
        i += 1
        code = []
        while i < len(lines) and not lines[i].startswith('```'):
            code.append(lines[i])
            i += 1
        flow.append(Preformatted('\n'.join(code), styles['ReportCode']))
    elif line.startswith('|'):
        rows = []
        while i < len(lines) and lines[i].startswith('|'):
            cells = [c.strip() for c in lines[i].strip('|').split('|')]
            if not all(re.fullmatch(r'[-: ]+', c) for c in cells):
                rows.append([Paragraph(inline(c), styles['ReportCell']) for c in cells])
            i += 1
        n = len(rows[0])
        if n == 3:
            widths = [width * .24, width * .14, width * .62]
        elif n == 4:
            widths = [width * .43, width * .15, width * .12, width * .30]
        elif n == 5:
            widths = [width * .44] + [width * .14] * 4
        elif n == 2:
            widths = [width * .25, width * .75]
        else:
            widths = [width / n] * n
        table = Table(rows, colWidths=widths, repeatRows=1, hAlign='LEFT')
        table.setStyle(TableStyle([
            ('BACKGROUND', (0,0), (-1,0), colors.HexColor('#e2ecf3')),
            ('ROWBACKGROUNDS', (0,1), (-1,-1), [colors.white, colors.HexColor('#f5f7f9')]),
            ('VALIGN', (0,0), (-1,-1), 'TOP'),
            ('LEFTPADDING', (0,0), (-1,-1), 6), ('RIGHTPADDING', (0,0), (-1,-1), 6),
            ('TOPPADDING', (0,0), (-1,-1), 6), ('BOTTOMPADDING', (0,0), (-1,-1), 6),
            ('LINEBELOW', (0,0), (-1,0), .6, colors.HexColor('#91a7b7')),
        ]))
        flow.extend([table, Spacer(1, 10)])
        continue
    elif line.startswith('# '):
        flow.append(Paragraph(inline(line[2:]), styles['Title']))
    elif line.startswith('## '):
        flow.append(Paragraph(inline(line[3:]), styles['Heading1']))
    elif line.startswith('### '):
        flow.append(Paragraph(inline(line[4:]), styles['Heading2']))
    elif line.startswith('- '):
        flow.append(Paragraph(inline(line[2:]), styles['ReportBody'], bulletText='-'))
    else:
        flow.append(Paragraph(inline(line), styles['ReportBody']))
    i += 1


def page_furniture(canvas, document):
    canvas.saveState()
    canvas.setFont('Helvetica', 8)
    canvas.setFillColor(colors.HexColor('#607384'))
    canvas.drawString(44, 23, '2IX20 | Formal specification and verification | 15 October 2026')
    canvas.drawRightString(A4[0] - 44, 23, str(document.page))
    canvas.restoreState()


pdf = ROOT / 'REPORT.pdf'
document = SimpleDocTemplate(str(pdf), pagesize=A4, leftMargin=44, rightMargin=44,
                             topMargin=39, bottomMargin=43, title='2IX20 Assignment 2: Formal specification and verification',
                             author='Team details to be completed')
document.build(flow, onFirstPage=page_furniture, onLaterPages=page_furniture)

files = {ROOT / name for name in ('trash_data.tla', 'trash_bins.tla', 'trash_single.tla', 'trash_multiple.tla',
                                 'trash_single.cfg', 'trash_multiple.cfg')}
for check in checks:
    files.add(ROOT / (check['module'] + '.tla'))
    files.add(ROOT / check['config'])
for directory in ('trash_single.toolbox', 'trash_multiple.toolbox'):
    files.update((ROOT / directory).glob('*.launch'))
archive = ROOT / 'assignment2-tla-project.zip'
with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as zipped:
    for path in sorted(files):
        assert path.suffix in ('.tla', '.cfg', '.launch')
        zipped.write(path, path.relative_to(ROOT))
with zipfile.ZipFile(archive) as zipped:
    assert zipped.testzip() is None
    assert not any(name.lower().endswith('.pdf') for name in zipped.namelist())
assert archive.stat().st_size < 3_000_000
summary = {'checks': len(checks), 'allExpectedResultsObserved': True,
           'pdfBytes': pdf.stat().st_size, 'zipBytes': archive.stat().st_size,
           'zipEntries': len(files), 'coreSourceHashes': {p.name: sha(p) for p in files if p.parent == ROOT and p.suffix == '.tla'},
           'reflectionRequiresTeamInput': True}
(ROOT / 'verification/SUMMARY.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
