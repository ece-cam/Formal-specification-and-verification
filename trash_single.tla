---------------------------- MODULE trash_single ----------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bin
  outerDoorOpen = FALSE,
  outerDoorLocked = TRUE,
  trapDoorOpen = FALSE,
  ramExtended = FALSE,
  trashInTop = 0,
  trashCompressed = 0,
  trashUncompressed = 0,
  trashCapacity = MaxCapacity,
  trapDestroyed = FALSE,

  \* Variable for user
  userTrash = 0,

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [command |-> "finished", open |-> FALSE],
  \* Sensor from bin
  binSensor = [sensor |-> "idle"],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = << >>,
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Command for the truck
  truckCommand = [command |-> "emptied", bin |-> 1];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.

\* The outer door can only be locked if it is closed.
OuterDoorLocked == outerDoorLocked => ~outerDoorOpen
\* The vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == ramExtended => (~outerDoorOpen /\ outerDoorLocked)
\* Every time the trash bin is full, eventually it is not full anymore.
TrashEmptied == ~TrashFitsCapacity(MaxUserTrash) ~> TrashFitsCapacity(MaxUserTrash)
\* An unauthorized user cannot open the outer door.
AuthorizedOpenOnly == outerDoorOpen => (\E u \in Users: TRUE \in ValidCard(u))
\* The user infinitely often has trash and infinitely often has no trash.
UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)
\* Every time the user has trash, they can deposit their trash.
UserTrashDeposited == userTrash > 0 ~> userTrash = 0
\* Every time the truck is requested for the trash bin, the truck has eventually emptied the bin.
TruckEmpties == truckCommand.command = "request" ~> truckCommand.command = "emptied"

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

\* Custom macro that operate on hardware
macro issue_bin_command(cmd, op) begin
  binCommand := [command |-> cmd, open |-> op];
end macro


\*****************************
\* Process for a bin
\*****************************
fair process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand.command /= "finished";
      if binCommand.command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked;
        outerDoorOpen := binCommand.open;
        if ~outerDoorOpen then
          binSensor := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand.command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen;
        outerDoorLocked := ~(binCommand.open);
      elsif binCommand.command = "change_trap_door" then
        assert outerDoorLocked;
        \* Open/Close trap door
        if ramExtended \/ CapacityExceeded then
            trapDestroyed := TRUE;
        end if;
        trapDoorOpen := binCommand.open;
        if trapDoorOpen then
          \* Trash falls through
          trashUncompressed := trashUncompressed + trashInTop;
          trashInTop := 0;
        end if
      elsif binCommand.command = "change_ram" then
        assert outerDoorLocked;
        \* Extend/Retract ram
        ramExtended := binCommand.open;
        if ramExtended then
          if ~trapDoorOpen then
            trapDestroyed := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed, trashUncompressed);
        end if;
      elsif binCommand.command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked;
        assert ~trapDoorOpen;
        assert ~ramExtended;
        assert trashInTop = 0;
        assert trashUncompressed = 0;
        trashCompressed := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand.command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE]
begin
  UserNextIteration:
    while TRUE do
      if userTrash = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash := amt;
        end with;
      end if;
  UserScanCard:
      write(scans, [user |-> self, bin |-> 1]);
  UserAwaitScanResponse:
      read(permissions, perm);
      assert perm.user = self;
      assert perm.bin = 1;
      if perm.granted then
  UserOpenDoor:
        binCommand := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand.command = "finished";
  UserDepositTrash:
        assert trashInTop = 0;
        trashInTop := userTrash;
        userTrash := 0;
  UserCloseDoor:
        binCommand := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand.command = "finished";
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
\* Section 4.2: receive a request, travel, empty the bin, and acknowledge.
\* The intermediate commands describe the truck's progress. The supplied
\* controller only sends "request" and observes the final "emptied" status.
fair process truckProcess \in Trucks
begin
  TruckWaitForRequest:
    while TRUE do
      await truckCommand.command = "request";
      assert truckCommand.bin = 1;
  TruckDriveToBin:
      \* Travel takes a separate step, during which scans can be handled.
      truckCommand.command := "arrived";
  TruckStartEmptying:
      \* Wait for a safe, idle bin; only binProcess changes the hardware.
      await binCommand.command = "finished";
      await outerDoorLocked /\ ~outerDoorOpen;
      await ~trapDoorOpen /\ ~ramExtended;
      await trashInTop = 0 /\ trashUncompressed = 0;
      truckCommand.command := "start_emptying";
      binCommand := [command |-> "empty", open |-> FALSE];
  TruckAwaitEmptied:
      \* Acknowledge completion only after the bin has executed the command.
      await binCommand.command = "finished";
      truckCommand.command := "emptied";
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
\* DUMMY main control process type.
\* Remodel it to control the trash bin system and handle requests by users!
fair process controlProcess = Control
variables
    currentScan = [user |-> 0, bin |-> 0];
    serverResponse = [user |-> 0, permission |-> FALSE];
    requestGranted = FALSE;
begin
  ControlStart:
    \* Implement behaviour
    while TRUE do
        ProcessUserScans:
            \* Waits and reads the user's scan, then sends validation request
            read(scans, currentScan);
            write(serverRequests, [user |-> currentScan.user]);
        
        ServerValidation:
            \* Waits and reads the response
            read(serverResponses, serverResponse);
        
        DecisionAndPermission:
            requestGranted := serverResponse.permission /\ TrashFitsCapacity(MaxUserTrash);
            if ~requestGranted then
            write(permissions, [user |-> currentScan.user, bin |-> 1, granted |-> FALSE]);
            end if;
        if requestGranted then
            IssueUnlock:
            \* Waits bin to finish previous commands before unlocking
            await binCommand.command = "finished";
            issue_bin_command("change_outer_lock", TRUE);

            AwaitUnlockAndGrant:
            await binCommand.command = "finished";
            write(permissions, [user |-> currentScan.user, bin |-> 1, granted |-> TRUE]);

            HardwareUsage:
                await binSensor.sensor = "outer_door_closed" /\ binCommand.command = "finished";
                issue_bin_command("change_outer_lock", FALSE);

            AwaitLock:
                await binCommand.command = "finished";
                issue_bin_command("change_trap_door", TRUE);

            AwaitTrapOpen:
                await binCommand.command = "finished";
                issue_bin_command("change_ram", TRUE);

            AwaitRamExtend:
                await binCommand.command = "finished";
                issue_bin_command("change_ram", FALSE);

            AwaitRamRetract:
                await binCommand.command = "finished";
                issue_bin_command("change_trap_door", FALSE);

            AwaitTrapClose:
                await binCommand.command = "finished";
                \* Reset sensor so the next loop starts clean
                binSensor := [sensor |-> "idle"];
        end if;

        TruckManagement:
            \* Call the truck if capacity is exceeded and it hasn't been called yet
            if ~TrashFitsCapacity(MaxUserTrash) /\ truckCommand.command = "emptied" then
                truckCommand := [command |-> "request", bin |-> 1];
            end if;  
    end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "df389a4e" /\ chksum(tla) = "8743d45b")
VARIABLES pc, outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, scans, permissions, 
          serverRequests, serverResponses, truckCommand

(* define statement *)
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity






TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins


MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded








OuterDoorLocked == outerDoorLocked => ~outerDoorOpen

RamOuterDoor == ramExtended => (~outerDoorOpen /\ outerDoorLocked)

TrashEmptied == ~TrashFitsCapacity(MaxUserTrash) ~> TrashFitsCapacity(MaxUserTrash)

AuthorizedOpenOnly == outerDoorOpen => (\E u \in Users: TRUE \in ValidCard(u))

UserTrash == []<>(userTrash > 0) /\ []<>(userTrash = 0)

UserTrashDeposited == userTrash > 0 ~> userTrash = 0

TruckEmpties == truckCommand.command = "request" ~> truckCommand.command = "emptied"

VARIABLES perm, req, currentScan, serverResponse, requestGranted

vars == << pc, outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, perm, 
           req, currentScan, serverResponse, requestGranted >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = FALSE
        /\ outerDoorLocked = TRUE
        /\ trapDoorOpen = FALSE
        /\ ramExtended = FALSE
        /\ trashInTop = 0
        /\ trashCompressed = 0
        /\ trashUncompressed = 0
        /\ trashCapacity = MaxCapacity
        /\ trapDestroyed = FALSE
        /\ userTrash = 0
        /\ binCommand = [command |-> "finished", open |-> FALSE]
        /\ binSensor = [sensor |-> "idle"]
        /\ scans = << >>
        /\ permissions = << >>
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [command |-> "emptied", bin |-> 1]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process controlProcess *)
        /\ currentScan = [user |-> 0, bin |-> 0]
        /\ serverResponse = [user |-> 0, permission |-> FALSE]
        /\ requestGranted = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckWaitForRequest"
                                        [] self = Control -> "ControlStart"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand.command /= "finished"
                           /\ IF binCommand.command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked, 
                                                "Failure of assertion at line 167, column 9.")
                                      /\ outerDoorOpen' = binCommand.open
                                      /\ IF ~outerDoorOpen'
                                            THEN /\ binSensor' = [sensor |-> "outer_door_closed"]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand.command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen, 
                                                           "Failure of assertion at line 174, column 9.")
                                                 /\ outerDoorLocked' = ~(binCommand.open)
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand.command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked, 
                                                                      "Failure of assertion at line 177, column 9.")
                                                            /\ IF ramExtended \/ CapacityExceeded
                                                                  THEN /\ trapDestroyed' = TRUE
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = binCommand.open
                                                            /\ IF trapDoorOpen'
                                                                  THEN /\ trashUncompressed' = trashUncompressed + trashInTop
                                                                       /\ trashInTop' = 0
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand.command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked, 
                                                                                 "Failure of assertion at line 189, column 9.")
                                                                       /\ ramExtended' = binCommand.open
                                                                       /\ IF ramExtended'
                                                                             THEN /\ IF ~trapDoorOpen
                                                                                        THEN /\ trapDestroyed' = TRUE
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = (trashCompressed + IF (trashUncompressed > 1) THEN trashUncompressed \div 2 ELSE trashUncompressed)
                                                                                  /\ trashUncompressed' = 0
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand.command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked, 
                                                                                            "Failure of assertion at line 201, column 9.")
                                                                                  /\ Assert(~trapDoorOpen, 
                                                                                            "Failure of assertion at line 202, column 9.")
                                                                                  /\ Assert(~ramExtended, 
                                                                                            "Failure of assertion at line 203, column 9.")
                                                                                  /\ Assert(trashInTop = 0, 
                                                                                            "Failure of assertion at line 204, column 9.")
                                                                                  /\ Assert(trashUncompressed = 0, 
                                                                                            "Failure of assertion at line 205, column 9.")
                                                                                  /\ trashCompressed' = 0
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 209, column 9.")
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
                                           binCommand, scans, permissions, 
                                           serverRequests, serverResponses, 
                                           truckCommand, perm, req, 
                                           currentScan, serverResponse, 
                                           requestGranted >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT !.command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, perm, req, 
                                            currentScan, serverResponse, 
                                            requestGranted >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, currentScan, serverResponse, 
                                           requestGranted >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ scans' = Append(scans, ([user |-> self, bin |-> 1]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, currentScan, 
                                      serverResponse, requestGranted >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 236, column 7.")
                               /\ Assert(perm'[self].bin = 1, 
                                         "Failure of assertion at line 237, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               userTrash, binCommand, 
                                               binSensor, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, req, currentScan, 
                                               serverResponse, requestGranted >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [command |-> "change_outer_door", open |-> TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, currentScan, 
                                      serverResponse, requestGranted >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand.command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, currentScan, serverResponse, 
                                           requestGranted >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop = 0, 
                                    "Failure of assertion at line 244, column 9.")
                          /\ trashInTop' = userTrash
                          /\ userTrash' = 0
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, perm, 
                                          req, currentScan, serverResponse, 
                                          requestGranted >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [command |-> "change_outer_door", open |-> FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, req, currentScan, 
                                       serverResponse, requestGranted >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand.command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             perm, req, currentScan, 
                                             serverResponse, requestGranted >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = amt
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, currentScan, 
                                      serverResponse, requestGranted >>

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
                                       binCommand, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       req, currentScan, serverResponse, 
                                       requestGranted >>

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
                                      binCommand, binSensor, scans, 
                                      permissions, truckCommand, perm, 
                                      currentScan, serverResponse, 
                                      requestGranted >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckWaitForRequest(self) == /\ pc[self] = "TruckWaitForRequest"
                             /\ truckCommand.command = "request"
                             /\ Assert(truckCommand.bin = 1, 
                                       "Failure of assertion at line 285, column 7.")
                             /\ pc' = [pc EXCEPT ![self] = "TruckDriveToBin"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             perm, req, currentScan, 
                                             serverResponse, requestGranted >>

TruckDriveToBin(self) == /\ pc[self] = "TruckDriveToBin"
                         /\ truckCommand' = [truckCommand EXCEPT !.command = "arrived"]
                         /\ pc' = [pc EXCEPT ![self] = "TruckStartEmptying"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userTrash, binCommand, binSensor, 
                                         scans, permissions, serverRequests, 
                                         serverResponses, perm, req, 
                                         currentScan, serverResponse, 
                                         requestGranted >>

TruckStartEmptying(self) == /\ pc[self] = "TruckStartEmptying"
                            /\ binCommand.command = "finished"
                            /\ outerDoorLocked /\ ~outerDoorOpen
                            /\ ~trapDoorOpen /\ ~ramExtended
                            /\ trashInTop = 0 /\ trashUncompressed = 0
                            /\ truckCommand' = [truckCommand EXCEPT !.command = "start_emptying"]
                            /\ binCommand' = [command |-> "empty", open |-> FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "TruckAwaitEmptied"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            perm, req, currentScan, 
                                            serverResponse, requestGranted >>

TruckAwaitEmptied(self) == /\ pc[self] = "TruckAwaitEmptied"
                           /\ binCommand.command = "finished"
                           /\ truckCommand' = [truckCommand EXCEPT !.command = "emptied"]
                           /\ pc' = [pc EXCEPT ![self] = "TruckWaitForRequest"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, perm, req, 
                                           currentScan, serverResponse, 
                                           requestGranted >>

truckProcess(self) == TruckWaitForRequest(self) \/ TruckDriveToBin(self)
                         \/ TruckStartEmptying(self)
                         \/ TruckAwaitEmptied(self)

ControlStart == /\ pc[Control] = "ControlStart"
                /\ pc' = [pc EXCEPT ![Control] = "ProcessUserScans"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, permissions, serverRequests, 
                                serverResponses, truckCommand, perm, req, 
                                currentScan, serverResponse, requestGranted >>

ProcessUserScans == /\ pc[Control] = "ProcessUserScans"
                    /\ scans /= <<>>
                    /\ currentScan' = Head(scans)
                    /\ scans' = Tail(scans)
                    /\ serverRequests' = Append(serverRequests, ([user |-> currentScan'.user]))
                    /\ pc' = [pc EXCEPT ![Control] = "ServerValidation"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, permissions, 
                                    serverResponses, truckCommand, perm, req, 
                                    serverResponse, requestGranted >>

ServerValidation == /\ pc[Control] = "ServerValidation"
                    /\ serverResponses /= <<>>
                    /\ serverResponse' = Head(serverResponses)
                    /\ serverResponses' = Tail(serverResponses)
                    /\ pc' = [pc EXCEPT ![Control] = "DecisionAndPermission"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binCommand, binSensor, scans, permissions, 
                                    serverRequests, truckCommand, perm, req, 
                                    currentScan, requestGranted >>

DecisionAndPermission == /\ pc[Control] = "DecisionAndPermission"
                         /\ requestGranted' = (serverResponse.permission /\ TrashFitsCapacity(MaxUserTrash))
                         /\ IF ~requestGranted'
                               THEN /\ permissions' = Append(permissions, ([user |-> currentScan.user, bin |-> 1, granted |-> FALSE]))
                               ELSE /\ TRUE
                                    /\ UNCHANGED permissions
                         /\ IF requestGranted'
                               THEN /\ pc' = [pc EXCEPT ![Control] = "IssueUnlock"]
                               ELSE /\ pc' = [pc EXCEPT ![Control] = "TruckManagement"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userTrash, binCommand, binSensor, 
                                         scans, serverRequests, 
                                         serverResponses, truckCommand, perm, 
                                         req, currentScan, serverResponse >>

IssueUnlock == /\ pc[Control] = "IssueUnlock"
               /\ binCommand.command = "finished"
               /\ binCommand' = [command |-> "change_outer_lock", open |-> TRUE]
               /\ pc' = [pc EXCEPT ![Control] = "AwaitUnlockAndGrant"]
               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                               ramExtended, trashInTop, trashCompressed, 
                               trashUncompressed, trashCapacity, trapDestroyed, 
                               userTrash, binSensor, scans, permissions, 
                               serverRequests, serverResponses, truckCommand, 
                               perm, req, currentScan, serverResponse, 
                               requestGranted >>

AwaitUnlockAndGrant == /\ pc[Control] = "AwaitUnlockAndGrant"
                       /\ binCommand.command = "finished"
                       /\ permissions' = Append(permissions, ([user |-> currentScan.user, bin |-> 1, granted |-> TRUE]))
                       /\ pc' = [pc EXCEPT ![Control] = "HardwareUsage"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, scans, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, req, currentScan, 
                                       serverResponse, requestGranted >>

HardwareUsage == /\ pc[Control] = "HardwareUsage"
                 /\ binSensor.sensor = "outer_door_closed" /\ binCommand.command = "finished"
                 /\ binCommand' = [command |-> "change_outer_lock", open |-> FALSE]
                 /\ pc' = [pc EXCEPT ![Control] = "AwaitLock"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, perm, req, currentScan, 
                                 serverResponse, requestGranted >>

AwaitLock == /\ pc[Control] = "AwaitLock"
             /\ binCommand.command = "finished"
             /\ binCommand' = [command |-> "change_trap_door", open |-> TRUE]
             /\ pc' = [pc EXCEPT ![Control] = "AwaitTrapOpen"]
             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                             ramExtended, trashInTop, trashCompressed, 
                             trashUncompressed, trashCapacity, trapDestroyed, 
                             userTrash, binSensor, scans, permissions, 
                             serverRequests, serverResponses, truckCommand, 
                             perm, req, currentScan, serverResponse, 
                             requestGranted >>

AwaitTrapOpen == /\ pc[Control] = "AwaitTrapOpen"
                 /\ binCommand.command = "finished"
                 /\ binCommand' = [command |-> "change_ram", open |-> TRUE]
                 /\ pc' = [pc EXCEPT ![Control] = "AwaitRamExtend"]
                 /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                 ramExtended, trashInTop, trashCompressed, 
                                 trashUncompressed, trashCapacity, 
                                 trapDestroyed, userTrash, binSensor, scans, 
                                 permissions, serverRequests, serverResponses, 
                                 truckCommand, perm, req, currentScan, 
                                 serverResponse, requestGranted >>

AwaitRamExtend == /\ pc[Control] = "AwaitRamExtend"
                  /\ binCommand.command = "finished"
                  /\ binCommand' = [command |-> "change_ram", open |-> FALSE]
                  /\ pc' = [pc EXCEPT ![Control] = "AwaitRamRetract"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userTrash, binSensor, scans, 
                                  permissions, serverRequests, serverResponses, 
                                  truckCommand, perm, req, currentScan, 
                                  serverResponse, requestGranted >>

AwaitRamRetract == /\ pc[Control] = "AwaitRamRetract"
                   /\ binCommand.command = "finished"
                   /\ binCommand' = [command |-> "change_trap_door", open |-> FALSE]
                   /\ pc' = [pc EXCEPT ![Control] = "AwaitTrapClose"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binSensor, scans, permissions, 
                                   serverRequests, serverResponses, 
                                   truckCommand, perm, req, currentScan, 
                                   serverResponse, requestGranted >>

AwaitTrapClose == /\ pc[Control] = "AwaitTrapClose"
                  /\ binCommand.command = "finished"
                  /\ binSensor' = [sensor |-> "idle"]
                  /\ pc' = [pc EXCEPT ![Control] = "TruckManagement"]
                  /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                  ramExtended, trashInTop, trashCompressed, 
                                  trashUncompressed, trashCapacity, 
                                  trapDestroyed, userTrash, binCommand, scans, 
                                  permissions, serverRequests, serverResponses, 
                                  truckCommand, perm, req, currentScan, 
                                  serverResponse, requestGranted >>

TruckManagement == /\ pc[Control] = "TruckManagement"
                   /\ IF ~TrashFitsCapacity(MaxUserTrash) /\ truckCommand.command = "emptied"
                         THEN /\ truckCommand' = [command |-> "request", bin |-> 1]
                         ELSE /\ TRUE
                              /\ UNCHANGED truckCommand
                   /\ pc' = [pc EXCEPT ![Control] = "ControlStart"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binCommand, binSensor, scans, permissions, 
                                   serverRequests, serverResponses, perm, req, 
                                   currentScan, serverResponse, requestGranted >>

controlProcess == ControlStart \/ ProcessUserScans \/ ServerValidation
                     \/ DecisionAndPermission \/ IssueUnlock
                     \/ AwaitUnlockAndGrant \/ HardwareUsage \/ AwaitLock
                     \/ AwaitTrapOpen \/ AwaitRamExtend \/ AwaitRamRetract
                     \/ AwaitTrapClose \/ TruckManagement

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
\* Modification History
