--------------------------- MODULE trash_no_sensor ---------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bins
  outerDoorOpen = [b \in Bins |-> FALSE],
  outerDoorLocked = [b \in Bins |-> TRUE],
  trapDoorOpen = [b \in Bins |-> FALSE],
  ramExtended = [b \in Bins |-> FALSE],
  trashInTop = [b \in Bins |-> 0],
  trashCompressed = [b \in Bins |-> 0],
  trashUncompressed = [b \in Bins |-> 0],
  trashCapacity = [b \in Bins |-> MaxCapacity],
  trapDestroyed = [b \in Bins |-> FALSE],

  \* Variables for users
  userTrash = [u \in Users |-> 0],

  \* Observations of validated grants and actual door-opening users.
  grantedUser = [b \in Bins |-> 0],
  doorUser = [b \in Bins |-> 0],
  \* Full bins await a truck in FIFO order; each bin is queued once.
  pendingBins = << >>,

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]],
  \* Sensor from outer door of bin
  binSensor = [b \in Bins |-> [sensor |-> "idle"]],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = [u \in Users |-> << >>],
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Commands for the trucks
  truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]
\* Trucks currently idle
AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}
Collecting(bin) == \E t \in Trucks:
                    /\ truckCommand[t].bin = bin
                    /\ truckCommand[t].command /= "emptied"
Queued(bin) == \E i \in 1..Len(pendingBins): pendingBins[i] = bin
\* Smallest idle truck: deterministic selection reduces equivalent states.
FirstAvailableTruck == CHOOSE t \in AvailableTrucks:
                        \A other \in AvailableTrucks: t <= other


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A b \in Bins: /\ grantedUser[b] \in Users \cup {0}
                            /\ doorUser[b] \in Users \cup {0}
          /\ pendingBins \in Seq(Bins)
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= NumUsers
              /\ Len(pendingBins) <= NumBins
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.
\* Make sure your formalisations hold for every bin/user, not just one specific instance.

\* For each trash bin, the outer door can only be locked if it is closed.
OuterDoorLocked == \A b \in Bins: outerDoorLocked[b] => ~outerDoorOpen[b]
\* For each trash bin, the vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == \A b \in Bins:
                  ramExtended[b] => (~outerDoorOpen[b] /\ outerDoorLocked[b])
\* For each trash bin, every time it is full, it is eventually not full anymore.
TrashEmptied == \A b \in Bins:
                  ~TrashFitsCapacity(b, MaxUserTrash) ~> TrashFitsCapacity(b, MaxUserTrash)
\* No unauthorized user can open the outer door of any trash bin.
AuthorizedOpenOnly == \A b \in Bins:
                        outerDoorOpen[b] =>
                          /\ doorUser[b] \in Users
                          /\ doorUser[b] = grantedUser[b]
                          /\ TRUE \in ValidCard(doorUser[b])
\* Each user infinitely often has trash and infinitely often has no trash.
UserTrash == \A u \in Users:
               /\ []<>(userTrash[u] > 0)
               /\ []<>(userTrash[u] = 0)
\* For each user, every time they have trash they can deposit their trash.
UserTrashDeposited == \A u \in Users: userTrash[u] > 0 ~> userTrash[u] = 0
\* For each trash bin, every time a truck is requested for it, a truck has eventually emptied it.
TruckEmpties == \A b \in Bins: \A t \in Trucks:
                 (truckCommand[t].bin = b /\ truckCommand[t].command = "request")
                 ~> (truckCommand[t].bin = b /\ truckCommand[t].command = "emptied")

\* A queued bin is not already assigned, and trucks never share a bin.
CollectionExclusive ==
  /\ \A i, j \in 1..Len(pendingBins): pendingBins[i] = pendingBins[j] => i = j
  /\ \A b \in Bins: Queued(b) => ~Collecting(b)
  /\ \A t1, t2 \in Trucks:
       (truckCommand[t1].command /= "emptied" /\ truckCommand[t2].command /= "emptied"
        /\ truckCommand[t1].bin = truckCommand[t2].bin) => t1 = t2

end define;


\*****************************
\* Helper macros
\*****************************

\* Compress trash
macro compress(compressed, uncompressed) begin
  compressed := compressed + IF (uncompressed > 1) THEN uncompressed \div 2 ELSE uncompressed;
  uncompressed := 0;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro


\*****************************
\* Process for a bin
\*****************************
fair process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand[self].command /= "finished";
      if binCommand[self].command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked[self];
        outerDoorOpen[self] := binCommand[self].open;
        if ~outerDoorOpen[self] then
          binSensor[self] := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand[self].command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen[self];
        outerDoorLocked[self] := ~(binCommand[self].open);
      elsif binCommand[self].command = "change_trap_door" then
        assert outerDoorLocked[self];
        \* Open/Close trap door
        if ramExtended[self] \/ CapacityExceeded(self) then
            trapDestroyed[self] := TRUE;
        end if;
        trapDoorOpen[self] := binCommand[self].open;
        if trapDoorOpen[self] then
          \* Trash falls through
          trashUncompressed[self] := trashUncompressed[self] + trashInTop[self];
          trashInTop[self] := 0;
        end if
      elsif binCommand[self].command = "change_ram" then
        assert outerDoorLocked[self];
        \* Extend/Retract ram
        ramExtended[self] := binCommand[self].open;
        if ramExtended[self] then
          if ~trapDoorOpen[self] then
            trapDestroyed[self] := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed[self], trashUncompressed[self]);
        end if;
      elsif binCommand[self].command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked[self];
        assert ~trapDoorOpen[self];
        assert ~ramExtended[self];
        assert trashInTop[self] = 0;
        assert trashUncompressed[self] = 0;
        trashCompressed[self] := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand[self].command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE],
  selectedBin = 0
begin
  UserNextIteration:
    while TRUE do
      if userTrash[self] = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash[self] := amt;
        end with;
      end if;
  UserScanCard:
      \* Non-deterministically choose a bin
      with sBin \in Bins do
        selectedBin := sBin;
        write(scans, [user |-> self, bin |-> selectedBin]);
      end with;
  UserAwaitScanResponse:
      read(permissions[self], perm);
      assert perm.user = self;
      assert perm.bin = selectedBin;
      if perm.granted then
  UserOpenDoor:
        doorUser[selectedBin] := self;
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand[selectedBin].command = "finished";
  UserDepositTrash:
        assert trashInTop[selectedBin] = 0;
        trashInTop[selectedBin] := userTrash[self];
        userTrash[self] := 0;
  UserCloseDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand[selectedBin].command = "finished";
      end if;
    end while;
end process;


\*****************************
\* Process for a server
\*****************************
fair process serverProcess = Server
variables
  req = [user |-> 0]
begin
  ServerNextIteration:
    while TRUE do
  ServerAwaitRequest:
      read(serverRequests, req);
      with valid \in ValidCard(req.user) do
        write(serverResponses, [user |-> req.user, permission |-> valid]);
      end with;
    end while;
end process;


\*****************************
\* Process for a truck
\*****************************
\* Each truck owns its command slot until completion. The controller keeps
\* its assigned bin unavailable for deposits throughout that interval.
fair process truckProcess \in Trucks
begin
  TruckWaitForRequest:
    while TRUE do
      await truckCommand[self].command = "request";
  TruckDriveToBin:
      truckCommand[self].command := "arrived";
  TruckStartEmptying:
      with b = truckCommand[self].bin do
        await binCommand[b].command = "finished";
        await outerDoorLocked[b] /\ ~outerDoorOpen[b];
        await ~trapDoorOpen[b] /\ ~ramExtended[b];
        await trashInTop[b] = 0 /\ trashUncompressed[b] = 0;
        truckCommand[self].command := "start_emptying";
        binCommand[b] := [command |-> "empty", open |-> FALSE];
      end with;
  TruckAwaitEmptied:
      await binCommand[truckCommand[self].bin].command = "finished";
      truckCommand[self].command := "emptied";
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
\* Deposits are serialized; trucks and card scanning proceed concurrently.
\* Pending collections get priority when a truck is available. Otherwise
\* the next scan is handled, including a negative response for a full bin.
fair process controlProcess = Control
variables
  currentScan = [user |-> 0, bin |-> 0],
  serverResponse = [user |-> 0, permission |-> FALSE]
begin
  ControlNext:
    while TRUE do
      await scans /= << >> \/ (pendingBins /= << >> /\ AvailableTrucks /= {});
      if pendingBins /= << >> /\ AvailableTrucks /= {} then
        with t = FirstAvailableTruck do
          truckCommand[t] := [command |-> "request", bin |-> Head(pendingBins)];
          pendingBins := Tail(pendingBins);
        end with;
      else
        read(scans, currentScan);
        write(serverRequests, [user |-> currentScan.user]);
  ControlValidation:
        read(serverResponses, serverResponse);
        assert serverResponse.user = currentScan.user;
        if serverResponse.permission
           /\ TrashFitsCapacity(currentScan.bin, MaxUserTrash)
           /\ ~Collecting(currentScan.bin) /\ ~Queued(currentScan.bin) then
          await binCommand[currentScan.bin].command = "finished";
          binCommand[currentScan.bin] := [command |-> "change_outer_lock", open |-> TRUE];
  ControlGrant:
          await binCommand[currentScan.bin].command = "finished";
          grantedUser[currentScan.bin] := currentScan.user;
          write(permissions[currentScan.user],
                [user |-> currentScan.user, bin |-> currentScan.bin, granted |-> TRUE]);
  ControlAwaitDoor:
          await binCommand[currentScan.bin].command = "finished";
          binCommand[currentScan.bin] := [command |-> "change_outer_lock", open |-> FALSE];
  ControlAwaitLock:
          await binCommand[currentScan.bin].command = "finished";
          grantedUser[currentScan.bin] := 0;
          binCommand[currentScan.bin] := [command |-> "change_trap_door", open |-> TRUE];
  ControlAwaitTrapOpen:
          await binCommand[currentScan.bin].command = "finished";
          binCommand[currentScan.bin] := [command |-> "change_ram", open |-> TRUE];
  ControlAwaitRamExtend:
          await binCommand[currentScan.bin].command = "finished";
          binCommand[currentScan.bin] := [command |-> "change_ram", open |-> FALSE];
  ControlAwaitRamRetract:
          await binCommand[currentScan.bin].command = "finished";
          binCommand[currentScan.bin] := [command |-> "change_trap_door", open |-> FALSE];
  ControlAwaitTrapClose:
          await binCommand[currentScan.bin].command = "finished";
          binSensor[currentScan.bin] := [sensor |-> "idle"];
          if ~TrashFitsCapacity(currentScan.bin, MaxUserTrash) then
            assert ~Queued(currentScan.bin) /\ ~Collecting(currentScan.bin);
            write(pendingBins, currentScan.bin);
          end if;
        else
          write(permissions[currentScan.user],
                [user |-> currentScan.user, bin |-> currentScan.bin, granted |-> FALSE]);
        end if;
      end if;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "795ffe4" /\ chksum(tla) = "d15f5c02")
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, grantedUser, doorUser, pendingBins, 
          binCommand, binSensor, scans, permissions, serverRequests, 
          serverResponses, truckCommand, pc

(* define statement *)
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]

AvailableTrucks == {t \in Trucks : truckCommand[t].command = "emptied"}
Collecting(bin) == \E t \in Trucks:
                    /\ truckCommand[t].bin = bin
                    /\ truckCommand[t].command /= "emptied"
Queued(bin) == \E i \in 1..Len(pendingBins): pendingBins[i] = bin

FirstAvailableTruck == CHOOSE t \in AvailableTrucks:
                        \A other \in AvailableTrucks: t <= other






TypeOK == /\ \A b \in Bins: /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A b \in Bins: /\ grantedUser[b] \in Users \cup {0}
                            /\ doorUser[b] \in Users \cup {0}
          /\ pendingBins \in Seq(Bins)
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins


MessagesOK == /\ Len(scans) <= NumUsers
              /\ Len(pendingBins) <= NumBins
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)









OuterDoorLocked == \A b \in Bins: outerDoorLocked[b] => ~outerDoorOpen[b]

RamOuterDoor == \A b \in Bins:
                  ramExtended[b] => (~outerDoorOpen[b] /\ outerDoorLocked[b])

TrashEmptied == \A b \in Bins:
                  ~TrashFitsCapacity(b, MaxUserTrash) ~> TrashFitsCapacity(b, MaxUserTrash)

AuthorizedOpenOnly == \A b \in Bins:
                        outerDoorOpen[b] =>
                          /\ doorUser[b] \in Users
                          /\ doorUser[b] = grantedUser[b]
                          /\ TRUE \in ValidCard(doorUser[b])

UserTrash == \A u \in Users:
               /\ []<>(userTrash[u] > 0)
               /\ []<>(userTrash[u] = 0)

UserTrashDeposited == \A u \in Users: userTrash[u] > 0 ~> userTrash[u] = 0

TruckEmpties == \A b \in Bins: \A t \in Trucks:
                 (truckCommand[t].bin = b /\ truckCommand[t].command = "request")
                 ~> (truckCommand[t].bin = b /\ truckCommand[t].command = "emptied")


CollectionExclusive ==
  /\ \A i, j \in 1..Len(pendingBins): pendingBins[i] = pendingBins[j] => i = j
  /\ \A b \in Bins: Queued(b) => ~Collecting(b)
  /\ \A t1, t2 \in Trucks:
       (truckCommand[t1].command /= "emptied" /\ truckCommand[t2].command /= "emptied"
        /\ truckCommand[t1].bin = truckCommand[t2].bin) => t1 = t2

VARIABLES perm, selectedBin, req, currentScan, serverResponse

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, grantedUser, doorUser, pendingBins, 
           binCommand, binSensor, scans, permissions, serverRequests, 
           serverResponses, truckCommand, pc, perm, selectedBin, req, 
           currentScan, serverResponse >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = [b \in Bins |-> FALSE]
        /\ outerDoorLocked = [b \in Bins |-> TRUE]
        /\ trapDoorOpen = [b \in Bins |-> FALSE]
        /\ ramExtended = [b \in Bins |-> FALSE]
        /\ trashInTop = [b \in Bins |-> 0]
        /\ trashCompressed = [b \in Bins |-> 0]
        /\ trashUncompressed = [b \in Bins |-> 0]
        /\ trashCapacity = [b \in Bins |-> MaxCapacity]
        /\ trapDestroyed = [b \in Bins |-> FALSE]
        /\ userTrash = [u \in Users |-> 0]
        /\ grantedUser = [b \in Bins |-> 0]
        /\ doorUser = [b \in Bins |-> 0]
        /\ pendingBins = << >>
        /\ binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]]
        /\ binSensor = [b \in Bins |-> [sensor |-> "idle"]]
        /\ scans = << >>
        /\ permissions = [u \in Users |-> << >>]
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        /\ selectedBin = [self \in Users |-> 0]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process controlProcess *)
        /\ currentScan = [user |-> 0, bin |-> 0]
        /\ serverResponse = [user |-> 0, permission |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckWaitForRequest"
                                        [] self = Control -> "ControlNext"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand[self].command /= "finished"
                           /\ IF binCommand[self].command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked[self], 
                                                "Failure of assertion at line 205, column 9.")
                                      /\ outerDoorOpen' = [outerDoorOpen EXCEPT ![self] = binCommand[self].open]
                                      /\ IF ~outerDoorOpen'[self]
                                            THEN /\ binSensor' = [binSensor EXCEPT ![self] = [sensor |-> "outer_door_closed"]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand[self].command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen[self], 
                                                           "Failure of assertion at line 212, column 9.")
                                                 /\ outerDoorLocked' = [outerDoorLocked EXCEPT ![self] = ~(binCommand[self].open)]
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand[self].command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked[self], 
                                                                      "Failure of assertion at line 215, column 9.")
                                                            /\ IF ramExtended[self] \/ CapacityExceeded(self)
                                                                  THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = [trapDoorOpen EXCEPT ![self] = binCommand[self].open]
                                                            /\ IF trapDoorOpen'[self]
                                                                  THEN /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = trashUncompressed[self] + trashInTop[self]]
                                                                       /\ trashInTop' = [trashInTop EXCEPT ![self] = 0]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand[self].command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked[self], 
                                                                                 "Failure of assertion at line 227, column 9.")
                                                                       /\ ramExtended' = [ramExtended EXCEPT ![self] = binCommand[self].open]
                                                                       /\ IF ramExtended'[self]
                                                                             THEN /\ IF ~trapDoorOpen[self]
                                                                                        THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = (trashCompressed[self]) + IF ((trashUncompressed[self]) > 1) THEN (trashUncompressed[self]) \div 2 ELSE (trashUncompressed[self])]
                                                                                  /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand[self].command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked[self], 
                                                                                            "Failure of assertion at line 239, column 9.")
                                                                                  /\ Assert(~trapDoorOpen[self], 
                                                                                            "Failure of assertion at line 240, column 9.")
                                                                                  /\ Assert(~ramExtended[self], 
                                                                                            "Failure of assertion at line 241, column 9.")
                                                                                  /\ Assert(trashInTop[self] = 0, 
                                                                                            "Failure of assertion at line 242, column 9.")
                                                                                  /\ Assert(trashUncompressed[self] = 0, 
                                                                                            "Failure of assertion at line 243, column 9.")
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 247, column 9.")
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, userTrash, 
                                           grantedUser, doorUser, pendingBins, 
                                           binCommand, scans, permissions, 
                                           serverRequests, serverResponses, 
                                           truckCommand, perm, selectedBin, 
                                           req, currentScan, serverResponse >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT ![self].command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            grantedUser, doorUser, pendingBins, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, perm, selectedBin, 
                                            req, currentScan, serverResponse >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash[self] = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           grantedUser, doorUser, pendingBins, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, currentScan, 
                                           serverResponse >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ \E sBin \in Bins:
                           /\ selectedBin' = [selectedBin EXCEPT ![self] = sBin]
                           /\ scans' = Append(scans, ([user |-> self, bin |-> selectedBin'[self]]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      grantedUser, doorUser, pendingBins, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, currentScan, 
                                      serverResponse >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 279, column 7.")
                               /\ Assert(perm'[self].bin = selectedBin[self], 
                                         "Failure of assertion at line 280, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               userTrash, grantedUser, 
                                               doorUser, pendingBins, 
                                               binCommand, binSensor, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, selectedBin, req, 
                                               currentScan, serverResponse >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ doorUser' = [doorUser EXCEPT ![selectedBin[self]] = self]
                      /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> TRUE]]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      grantedUser, pendingBins, binSensor, 
                                      scans, permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, 
                                      selectedBin, req, currentScan, 
                                      serverResponse >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand[selectedBin[self]].command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           grantedUser, doorUser, pendingBins, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           selectedBin, req, currentScan, 
                                           serverResponse >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop[selectedBin[self]] = 0, 
                                    "Failure of assertion at line 288, column 9.")
                          /\ trashInTop' = [trashInTop EXCEPT ![selectedBin[self]] = userTrash[self]]
                          /\ userTrash' = [userTrash EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          grantedUser, doorUser, pendingBins, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, perm, 
                                          selectedBin, req, currentScan, 
                                          serverResponse >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> FALSE]]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       grantedUser, doorUser, pendingBins, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, selectedBin, req, 
                                       currentScan, serverResponse >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand[selectedBin[self]].command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             grantedUser, doorUser, 
                                             pendingBins, binCommand, 
                                             binSensor, scans, permissions, 
                                             serverRequests, serverResponses, 
                                             truckCommand, perm, selectedBin, 
                                             req, currentScan, serverResponse >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = [userTrash EXCEPT ![self] = amt]
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, 
                                      grantedUser, doorUser, pendingBins, 
                                      binCommand, binSensor, scans, 
                                      permissions, serverRequests, 
                                      serverResponses, truckCommand, perm, 
                                      selectedBin, req, currentScan, 
                                      serverResponse >>

userProcess(self) == UserNextIteration(self) \/ UserScanCard(self)
                        \/ UserAwaitScanResponse(self)
                        \/ UserOpenDoor(self) \/ UserAwaitOpenDoor(self)
                        \/ UserDepositTrash(self) \/ UserCloseDoor(self)
                        \/ UserAwaitClosedDoor(self) \/ UserNewTrash(self)

ServerNextIteration == /\ pc[Server] = "ServerNextIteration"
                       /\ pc' = [pc EXCEPT ![Server] = "ServerAwaitRequest"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       grantedUser, doorUser, pendingBins, 
                                       binCommand, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       selectedBin, req, currentScan, 
                                       serverResponse >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req'.user):
                           serverResponses' = Append(serverResponses, ([user |-> req'.user, permission |-> valid]))
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      grantedUser, doorUser, pendingBins, 
                                      binCommand, binSensor, scans, 
                                      permissions, truckCommand, perm, 
                                      selectedBin, currentScan, serverResponse >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckWaitForRequest(self) == /\ pc[self] = "TruckWaitForRequest"
                             /\ truckCommand[self].command = "request"
                             /\ pc' = [pc EXCEPT ![self] = "TruckDriveToBin"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             grantedUser, doorUser, 
                                             pendingBins, binCommand, 
                                             binSensor, scans, permissions, 
                                             serverRequests, serverResponses, 
                                             truckCommand, perm, selectedBin, 
                                             req, currentScan, serverResponse >>

TruckDriveToBin(self) == /\ pc[self] = "TruckDriveToBin"
                         /\ truckCommand' = [truckCommand EXCEPT ![self].command = "arrived"]
                         /\ pc' = [pc EXCEPT ![self] = "TruckStartEmptying"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userTrash, grantedUser, doorUser, 
                                         pendingBins, binCommand, binSensor, 
                                         scans, permissions, serverRequests, 
                                         serverResponses, perm, selectedBin, 
                                         req, currentScan, serverResponse >>

TruckStartEmptying(self) == /\ pc[self] = "TruckStartEmptying"
                            /\ LET b == truckCommand[self].bin IN
                                 /\ binCommand[b].command = "finished"
                                 /\ outerDoorLocked[b] /\ ~outerDoorOpen[b]
                                 /\ ~trapDoorOpen[b] /\ ~ramExtended[b]
                                 /\ trashInTop[b] = 0 /\ trashUncompressed[b] = 0
                                 /\ truckCommand' = [truckCommand EXCEPT ![self].command = "start_emptying"]
                                 /\ binCommand' = [binCommand EXCEPT ![b] = [command |-> "empty", open |-> FALSE]]
                            /\ pc' = [pc EXCEPT ![self] = "TruckAwaitEmptied"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            grantedUser, doorUser, pendingBins, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            perm, selectedBin, req, 
                                            currentScan, serverResponse >>

TruckAwaitEmptied(self) == /\ pc[self] = "TruckAwaitEmptied"
                           /\ binCommand[truckCommand[self].bin].command = "finished"
                           /\ truckCommand' = [truckCommand EXCEPT ![self].command = "emptied"]
                           /\ pc' = [pc EXCEPT ![self] = "TruckWaitForRequest"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           grantedUser, doorUser, pendingBins, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, perm, selectedBin, 
                                           req, currentScan, serverResponse >>

truckProcess(self) == TruckWaitForRequest(self) \/ TruckDriveToBin(self)
                         \/ TruckStartEmptying(self)
                         \/ TruckAwaitEmptied(self)

ControlNext == /\ pc[Control] = "ControlNext"
               /\ scans /= << >> \/ (pendingBins /= << >> /\ AvailableTrucks /= {})
               /\ IF pendingBins /= << >> /\ AvailableTrucks /= {}
                     THEN /\ LET t == FirstAvailableTruck IN
                               /\ truckCommand' = [truckCommand EXCEPT ![t] = [command |-> "request", bin |-> Head(pendingBins)]]
                               /\ pendingBins' = Tail(pendingBins)
                          /\ pc' = [pc EXCEPT ![Control] = "ControlNext"]
                          /\ UNCHANGED << scans, serverRequests, currentScan >>
                     ELSE /\ scans /= <<>>
                          /\ currentScan' = Head(scans)
                          /\ scans' = Tail(scans)
                          /\ serverRequests' = Append(serverRequests, ([user |-> currentScan'.user]))
                          /\ pc' = [pc EXCEPT ![Control] = "ControlValidation"]
                          /\ UNCHANGED << pendingBins, truckCommand >>
               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                               ramExtended, trashInTop, trashCompressed, 
                               trashUncompressed, trashCapacity, trapDestroyed, 
                               userTrash, grantedUser, doorUser, binCommand, 
                               binSensor, permissions, serverResponses, perm, 
                               selectedBin, req, serverResponse >>

ControlValidation == /\ pc[Control] = "ControlValidation"
                     /\ serverResponses /= <<>>
                     /\ serverResponse' = Head(serverResponses)
                     /\ serverResponses' = Tail(serverResponses)
                     /\ Assert(serverResponse'.user = currentScan.user, 
                               "Failure of assertion at line 370, column 9.")
                     /\ IF serverResponse'.permission
                           /\ TrashFitsCapacity(currentScan.bin, MaxUserTrash)
                           /\ ~Collecting(currentScan.bin) /\ ~Queued(currentScan.bin)
                           THEN /\ binCommand[currentScan.bin].command = "finished"
                                /\ binCommand' = [binCommand EXCEPT ![currentScan.bin] = [command |-> "change_outer_lock", open |-> TRUE]]
                                /\ pc' = [pc EXCEPT ![Control] = "ControlGrant"]
                                /\ UNCHANGED permissions
                           ELSE /\ permissions' = [permissions EXCEPT ![currentScan.user] = Append((permissions[currentScan.user]), ([user |-> currentScan.user, bin |-> currentScan.bin, granted |-> FALSE]))]
                                /\ pc' = [pc EXCEPT ![Control] = "ControlNext"]
                                /\ UNCHANGED binCommand
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     grantedUser, doorUser, pendingBins, 
                                     binSensor, scans, serverRequests, 
                                     truckCommand, perm, selectedBin, req, 
                                     currentScan >>

ControlGrant == /\ pc[Control] = "ControlGrant"
                /\ binCommand[currentScan.bin].command = "finished"
                /\ grantedUser' = [grantedUser EXCEPT ![currentScan.bin] = currentScan.user]
                /\ permissions' = [permissions EXCEPT ![currentScan.user] = Append((permissions[currentScan.user]), ([user |-> currentScan.user, bin |-> currentScan.bin, granted |-> TRUE]))]
                /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitDoor"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, doorUser, 
                                pendingBins, binCommand, binSensor, scans, 
                                serverRequests, serverResponses, truckCommand, 
                                perm, selectedBin, req, currentScan, 
                                serverResponse >>

ControlAwaitDoor == /\ pc[Control] = "ControlAwaitDoor"
                    /\ binCommand[currentScan.bin].command = "finished"
                    /\ binCommand' = [binCommand EXCEPT ![currentScan.bin] = [command |-> "change_outer_lock", open |-> FALSE]]
                    /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitLock"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    grantedUser, doorUser, pendingBins, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, selectedBin, req, 
                                    currentScan, serverResponse >>

ControlAwaitLock == /\ pc[Control] = "ControlAwaitLock"
                    /\ binCommand[currentScan.bin].command = "finished"
                    /\ grantedUser' = [grantedUser EXCEPT ![currentScan.bin] = 0]
                    /\ binCommand' = [binCommand EXCEPT ![currentScan.bin] = [command |-> "change_trap_door", open |-> TRUE]]
                    /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitTrapOpen"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    doorUser, pendingBins, binSensor, scans, 
                                    permissions, serverRequests, 
                                    serverResponses, truckCommand, perm, 
                                    selectedBin, req, currentScan, 
                                    serverResponse >>

ControlAwaitTrapOpen == /\ pc[Control] = "ControlAwaitTrapOpen"
                        /\ binCommand[currentScan.bin].command = "finished"
                        /\ binCommand' = [binCommand EXCEPT ![currentScan.bin] = [command |-> "change_ram", open |-> TRUE]]
                        /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitRamExtend"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, grantedUser, doorUser, 
                                        pendingBins, binSensor, scans, 
                                        permissions, serverRequests, 
                                        serverResponses, truckCommand, perm, 
                                        selectedBin, req, currentScan, 
                                        serverResponse >>

ControlAwaitRamExtend == /\ pc[Control] = "ControlAwaitRamExtend"
                         /\ binCommand[currentScan.bin].command = "finished"
                         /\ binCommand' = [binCommand EXCEPT ![currentScan.bin] = [command |-> "change_ram", open |-> FALSE]]
                         /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitRamRetract"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userTrash, grantedUser, doorUser, 
                                         pendingBins, binSensor, scans, 
                                         permissions, serverRequests, 
                                         serverResponses, truckCommand, perm, 
                                         selectedBin, req, currentScan, 
                                         serverResponse >>

ControlAwaitRamRetract == /\ pc[Control] = "ControlAwaitRamRetract"
                          /\ binCommand[currentScan.bin].command = "finished"
                          /\ binCommand' = [binCommand EXCEPT ![currentScan.bin] = [command |-> "change_trap_door", open |-> FALSE]]
                          /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitTrapClose"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashInTop, trashCompressed, 
                                          trashUncompressed, trashCapacity, 
                                          trapDestroyed, userTrash, 
                                          grantedUser, doorUser, pendingBins, 
                                          binSensor, scans, permissions, 
                                          serverRequests, serverResponses, 
                                          truckCommand, perm, selectedBin, req, 
                                          currentScan, serverResponse >>

ControlAwaitTrapClose == /\ pc[Control] = "ControlAwaitTrapClose"
                         /\ binCommand[currentScan.bin].command = "finished"
                         /\ binSensor' = [binSensor EXCEPT ![currentScan.bin] = [sensor |-> "idle"]]
                         /\ IF ~TrashFitsCapacity(currentScan.bin, MaxUserTrash)
                               THEN /\ Assert(~Queued(currentScan.bin) /\ ~Collecting(currentScan.bin), 
                                              "Failure of assertion at line 401, column 13.")
                                    /\ pendingBins' = Append(pendingBins, (currentScan.bin))
                               ELSE /\ TRUE
                                    /\ UNCHANGED pendingBins
                         /\ pc' = [pc EXCEPT ![Control] = "ControlNext"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userTrash, grantedUser, doorUser, 
                                         binCommand, scans, permissions, 
                                         serverRequests, serverResponses, 
                                         truckCommand, perm, selectedBin, req, 
                                         currentScan, serverResponse >>

controlProcess == ControlNext \/ ControlValidation \/ ControlGrant
                     \/ ControlAwaitDoor \/ ControlAwaitLock
                     \/ ControlAwaitTrapOpen \/ ControlAwaitRamExtend
                     \/ ControlAwaitRamRetract \/ ControlAwaitTrapClose

Next == serverProcess \/ controlProcess
           \/ (\E self \in Bins: binProcess(self))
           \/ (\E self \in Users: userProcess(self))
           \/ (\E self \in Trucks: truckProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Bins : WF_vars(binProcess(self))
        /\ \A self \in Users : WF_vars(userProcess(self))
        /\ WF_vars(serverProcess)
        /\ \A self \in Trucks : WF_vars(truckProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION 

=============================================================================
