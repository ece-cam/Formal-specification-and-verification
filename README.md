# Assignment 2 — single-bin handoff

Sections 4.2 and 4.4 are implemented and checked. 

Open `../assignment2.code-workspace` in VS Code. Use **Terminal > Run Test Task** (or the Command Palette command **Tasks: Run Test Task**). The default task translates PlusCal and runs all required checks plus four expected failures demonstrating the need for fairness. Full logs and run metadata are saved in `verification/`. The task succeeds only when the normal model passes and every unfair test produces the expected temporal-property violation.

The course's TLA+ 1.7.4 tools are installed in `../.tools/tla-1.7.4/tla2tools.jar`. Java is already installed. No additional setup is needed on this computer for these tasks. They use Java directly in VS Code's integrated terminal. The TLA+ extension provides editing support; its current automated check command adds `-dumptrace`, which the course tools reject, so use the prepared tasks for reproducible course-version checks.

The combined passing check explored **12,232 distinct states** in **6.881 seconds** in the recorded run. All seven named properties, the five diagnostic invariants, deadlock checking and the environment assertions passed under weak process fairness. A passing authorization invariant has limited evidential value here because the only user is valid; see the separate review.

Files to read:

- `REPORT_4.2_4.4.pdf`: report sections to merge into the team's final report.
- `REPORT_4.2_4.4.md`: editable source of those sections.
- `trash_single.tla`: PlusCal source and automatically generated TLA+ translation.
- `trash_single.cfg`: all required single-bin checks, including fairness through `Spec`.
- `trash_bins.toolbox/trash_bins___model_single.launch`: matching Toolbox model configuration.
- `verification/single.log` and `single.run.json`: final successful check and input hashes.
- `verification/unfair_*.cfg`, `.log`, `.run.json`: one counterexample check per liveness property.

To run only the required passing verification in the VS Code terminal:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/verify.ps1 -Mode all
```

The scripts retranslate automatically. Do not manually edit the `BEGIN TRANSLATION` / `END TRANSLATION` block. On another machine, install Java, download the course jar from the [official 1.7.4 release](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.4), preserve the relative `.tools/tla-1.7.4/tla2tools.jar` location or adjust the script, and update the workspace's Java paths. See the [official extension documentation](https://github.com/tlaplus/vscode-tlaplus) for VS Code support.

`assignment2-single-bin.zip` contains only the single-bin TLA+ project/configuration files, including the supplied dependency. It is a handoff archive, not the complete Assignment 2 submission. The final assignment requires both single- and multiple-bin models and one combined PDF; PDFs must remain outside the ZIP. Add the team's actual personal reflection and per-section AI disclosure when merging the report, as required by section 6.2.
