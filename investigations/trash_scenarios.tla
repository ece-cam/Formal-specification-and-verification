---------------- MODULE trash_scenarios ----------------
EXTENDS trash_multiple
AnyCard(user) == {TRUE, FALSE}
NoCard(user) == {FALSE}

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

========================================================
