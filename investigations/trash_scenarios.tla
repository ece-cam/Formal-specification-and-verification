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

========================================================
