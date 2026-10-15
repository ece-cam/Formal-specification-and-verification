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

The Users configuration is expected to violate `UserTrash` and `UserTrashDeposited`. Section 5.4 asks for this investigation; the report explains both counterexamples. `multiple_users_other.cfg` separately exhausts the same graph with every invariant, deadlock checking and the collection liveness properties enabled. Expected counterexamples count as successful experiment outcomes, not as passing properties.

## Run the checks

Open `../assignment2.code-workspace` in VS Code and choose **Tasks: Run Test Task**, or run:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/verify.ps1 -Mode all
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/verify.ps1 -Mode investigations
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/verify.ps1 -Mode unfair
```

`-Mode suite` runs all checks. `-Check multiple_bins` runs one. The script translates PlusCal, uses one worker and fingerprint index 0, then saves the results. Do not edit generated translation blocks. Each check has a five-minute timeout. Parsing errors, crashes and timeouts do not count as expected counterexamples.

Java and the course TLA+ 1.7.4 JAR are available at `../.tools/tla-1.7.4/tla2tools.jar`. Python 3.9+ is required; the launcher detects this computer's interpreter. On another computer set `PYTHON` to a working executable and `TLA_JAR` to the course JAR if necessary; set `JAVA` if Java is not on PATH. Verification uses only Python's standard library.

In Toolbox, open `trash_single.tla` or `trash_multiple.tla` as the specification root and use the corresponding `.toolbox` directory. The original `trash_bins.tla` remains a single-bin compatibility entry point; its old multiple-model launcher is not the canonical multiple-bin configuration.

After changing the production model, regenerate experiment sources with `scripts/prepare_investigations.py`; rerun `users_weak_UserTrashDeposited`; regenerate the strong-fairness witness with `scripts/prepare_fair_witness.py`; then run the full suite. The witness replays an actual TLC trace with original Init/Next and original strong process fairness; it is counterexample evidence, not exhaustive strong-fairness checking. Refresh Toolbox launch files with `scripts/prepare_toolbox.py` and rebuild the report/ZIP with `scripts/build_report.py`. Report generation requires ReportLab, installed locally in `../.tools/reporting` on this computer.

## Before submission

Complete the marked team reflection: the two members' names and actual contributions, and discussions with other groups. Review the per-section AI declaration and explanations. These personal statements cannot be inferred from the project. Submit `REPORT.pdf` and `assignment2-tla-project.zip` separately. No submission has been made automatically.
