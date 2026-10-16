# Pre-repair reproduction, 16 October 2026

These files preserve the model as it was when the deadlock was reported.
They are historical evidence and are excluded from the submission ZIP.

`trash_multiple.tla` with `multiple_bins.cfg` reaches a deadlock. The recorded
trace is `../deadlock_before_bins.log`: state 164 has bin 2 queued for collection,
an idle truck, and the controller blocked at `ControlAwaitBinReady`.

From this directory, reproduce it with the course JAR:

```powershell
java -Xmx768m -cp ../../../.tools/tla-1.7.4/tla2tools.jar tlc2.TLC -workers 1 -fp 0 -config multiple_bins.cfg trash_multiple
```

The root project contains the repaired model. Its Bins, Users and Trucks runs
all finish without errors, with every required property and deadlock checking
enabled. The original Users and Trucks configurations did not reproduce the
deadlock; their original-model logs are `../deadlock_before.log` and
`../deadlock_before_trucks.log`.
