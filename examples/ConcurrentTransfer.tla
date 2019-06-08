------------------------- MODULE ConcurrentTransfer -------------------------

EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10,
          account_total = alice_account + bob_account;

\** the process keyword indicates that this unit of work can happen concurrently in multiple processes 
process Transfer \in 1..2
  variable money \in 1..20;
begin
Transfer:
  if alice_account >= money then

    \* note that since both statements of the transfer use a single label, they are treated atomically
    \* this would need to be implemented correctly, e.g., using database transactions
    \* however, since the money check above happens outside of that atomic unit, there is still a race condition here, 
    \* causing Alice's account total to go negative. TLC will nicely catch and report that when running this model.  
    A: alice_account := alice_account - money;
       bob_account := bob_account + money;
  
  end if;
  
C: assert alice_account >= 0;
end process

end algorithm *)


\* BEGIN TRANSLATION
\* Label Transfer of process Transfer at line 14 col 3 changed to Transfer_
VARIABLES alice_account, bob_account, account_total, pc, money

vars == << alice_account, bob_account, account_total, pc, money >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ account_total = alice_account + bob_account
        (* Process Transfer *)
        /\ money \in [1..2 -> 1..20]
        /\ pc = [self \in ProcSet |-> "Transfer_"]

Transfer_(self) == /\ pc[self] = "Transfer_"
                   /\ IF alice_account >= money[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "A"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "C"]
                   /\ UNCHANGED << alice_account, bob_account, account_total, 
                                   money >>

A(self) == /\ pc[self] = "A"
           /\ alice_account' = alice_account - money[self]
           /\ bob_account' = bob_account + money[self]
           /\ pc' = [pc EXCEPT ![self] = "C"]
           /\ UNCHANGED << account_total, money >>

C(self) == /\ pc[self] = "C"
           /\ Assert(alice_account >= 0, 
                     "Failure of assertion at line 25, column 4.")
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << alice_account, bob_account, account_total, money >>

Transfer(self) == Transfer_(self) \/ A(self) \/ C(self)

Next == (\E self \in 1..2: Transfer(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


\* MoneyNotNegative == money >= 0   \** note that this doesn't make sense now that money is local variable also, so there are two values for money
MoneyInvariant == alice_account + bob_account = account_total



=============================================================================
\* Modification History
\* Last modified Sat Jun 08 10:39:16 PDT 2019 by pallav.kothari
\* Created Sat Jun 08 10:20:31 PDT 2019 by pallav.kothari
