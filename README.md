# Assignment 2: formal specification and verification

The project contains the reviewed single-bin model (4.1-4.4), the multiple-bin model (5.1-5.3), and reproducible investigations (5.4).

- `REPORT.pdf`: combined report, separate from the ZIP as required.
- `REPORT.md`: editable report, including results and counterexample explanations.
- `assignment2-tla-project.zip`: submission archive containing only TLA+ sources, configurations and Toolbox model files.
- `trash_single.tla` / `trash_single.cfg`: required single-bin model.
- `trash_multiple.tla`: multiple-bin model; `multiple_bins.cfg`, `multiple_users.cfg`, and `multiple_trucks.cfg` select the required configurations. `trash_multiple.cfg` defaults to Bins.
- `checks.json`: all checks and their expected outcomes.
- `verification/*.log` and `*.run.json`: full output, timings, state counts, input hashes and commands.
- `investigations/`: isolated fairness, declined-card, sensor and maximum-compression experiments. Production `trash_data.tla` is unchanged.

All required properties and deadlock checks pass for Single, Bins, Users and Trucks. The final multiple-bin model preserves FIFO admission turns across declined retries and adds strong fairness only to the user's close-acknowledgement action. Every main check expects a clean TLC success. Intentional failures are confined to the investigation checks.

The pre-repair Bins deadlock is preserved in `verification/deadlock_before_bins.log`; final verification logs use the `multiple_*` names. Old replay experiments are retained under `verification/previous-model` and are not part of the active suite or submission.

## Run the checks

Open `../assignment2.code-workspace` in VS Code and choose **Tasks: Run Test Task** to verify the required models. **Tasks: Run Task** also offers individual Bins, Users and Trucks checks and the complete investigation suite. Alternatively run:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/verify.ps1 -Mode all
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/verify.ps1 -Mode investigations
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/verify.ps1 -Mode unfair
```

`-Mode suite` runs all checks. `-Check multiple_bins` runs one. The script translates PlusCal, uses one worker and fingerprint index 0, then saves the results. Do not edit generated translation blocks. Each check has a five-minute timeout. Parsing errors, crashes and timeouts do not count as expected counterexamples.

Java and the course TLA+ 1.7.4 JAR are available at `../.tools/tla-1.7.4/tla2tools.jar`. Python 3.9+ is required; the launcher detects this computer's interpreter. On another computer set `PYTHON` to a working executable and `TLA_JAR` to the course JAR if necessary; set `JAVA` if Java is not on PATH. Verification uses only Python's standard library.

In Toolbox, open `trash_single.tla` or `trash_multiple.tla` as the specification root and use the corresponding `.toolbox` directory. The compatibility entry point `trash_bins.tla` currently extends `trash_multiple`; its `model_multiple` launcher matches Bins. Always open `trash_multiple.tla` as the specification root for multiple-bin Toolbox models; a model created under `trash_single.tla` still checks the single-bin algorithm. `trash_multiple.cfg` retains your selected Users constants, while the three named configuration files remain fixed to the assignment values.

After changing the production model, regenerate experiment sources with `scripts/prepare_investigations.py`, then run the suite. Refresh Toolbox launch files with `scripts/prepare_toolbox.py` and rebuild the report/ZIP with `scripts/build_report.py`. The runner's `--failed` option also detects stale input hashes; report generation rejects stale model, configuration or dependency hashes. Report generation requires ReportLab, installed locally in `../.tools/reporting` on this computer.

## Before submission

Complete the marked team reflection: the two members' names and actual contributions, and discussions with other groups. Review the per-section AI declaration and explanations. These personal statements cannot be inferred from the project. Submit `REPORT.pdf` and `assignment2-tla-project.zip` separately. No submission has been made automatically.
