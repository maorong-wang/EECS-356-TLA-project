----------------------------- MODULE semaphore -----------------------------
EXTENDS Integers
CONSTANTS N
VARIABLES state, step, occupation
TypeInvariant == /\ \A p \in 0..N-1 : occupation[p] \in {TRUE, FALSE}
                 /\ \A p \in 0..N-1 : state[p] \in {"idle", "sentRequest", "waiting", "critical"}
----------------------------------------------------------------------------
Init == /\ state = [i \in 0..N-1 |-> "idle"]  
        /\ occupation = [i \in 0..N-1 |-> FALSE] 
        /\ step = 0 
Request(p) == /\ state[p] = "idle"
              /\ state' = [state EXCEPT ![p] = "sentRequest"]
              /\ UNCHANGED <<occupation>>
BeginWaiting(p) == /\ state[p] = "sentRequest"
                   /\ state' = [state EXCEPT ![p] = "waiting"]
                   /\ UNCHANGED <<occupation>>
EnterCritical(p) == /\ state[p] = "waiting"
                    /\ \A pi \in 0..N-1 : occupation[pi] = FALSE
                    /\ state' = [state EXCEPT ![p] = "critical"]
                    /\ occupation' = [occupation EXCEPT ![p] = TRUE]
ExitCritical(p) == /\ state[p] = "critical"
                   /\ state' = [state EXCEPT ![p] = "idle"]
                   /\ occupation' = [occupation EXCEPT ![p] = FALSE]
Next == /\ \E p \in 0..N-1 :
            \/ Request(p)
            \/ BeginWaiting(p)
            \/ EnterCritical(p)
            \/ ExitCritical(p)
        /\ step' = step + 1
Spec == Init /\ [][Next]_<<state, occupation, step>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Fri Dec 04 17:41:16 CST 2020 by 26632
\* Created Sat Nov 07 11:17:25 CST 2020 by 26632
