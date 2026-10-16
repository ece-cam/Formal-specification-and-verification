# Direct strong-fairness attempt

On 15 October 2026, the unrestricted `trash_scenarios` module was checked with
`SPECIFICATION StrongSpec`, Users constants `(1,2,1,3,2)`, all standard invariants,
and `PROPERTY UserTrash`. TLC reached the full graph of 81,060 distinct states,
but did not complete its strong-fairness temporal search before the runner's
300-second limit (recorded wall time: 300.022 seconds). This was a timeout,
not a property result. Its JVM was stopped.

The final strong-fairness checks instead use `trash_fair_cycle`, generated from
the weak-fairness UserTrashDeposited counterexample. Every transition remains
constrained by the original `Next`; all original strong process-fairness clauses
are checked. Both properties fail on this 178-state witness, looping to state 93.
The final `.run.json` files describe these successful counterexample searches,
not an exhaustive unrestricted strong-fairness run.
