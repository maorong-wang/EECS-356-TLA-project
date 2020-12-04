----------------------------- MODULE semaphore -----------------------------
EXTENDS Integers
CONSTANTS N
VARIABLES state, step, occupation, prev_occup, flag
TypeInvariant == /\ \A p \in 0..N-1 : occupation[p] \in {TRUE, FALSE}
                 /\ \A p \in 0..N-1 : prev_occup[p] \in {TRUE, FALSE}
                 /\ \A p \in 0..N-1 : flag[p] \in {TRUE, FALSE}
                 /\ \A p \in 0..N-1 : state[p] \in {"idle", "sentRequest", "waiting", "critical"}
----------------------------------------------------------------------------
Init == /\ state = [i \in 0..N-1 |-> "idle"]  
        /\ occupation = [i \in 0..N-1 |-> FALSE] 
        /\ prev_occup = [i \in 0..N-1 |-> FALSE] 
        /\ flag = [i \in 0..N-1 |-> FALSE] 
        /\ step = 0 
Request(p) == /\ state[p] = "idle"
              /\ state' = [state EXCEPT ![p] = "sentRequest"]
              /\ flag' = [flag EXCEPT ![p] = TRUE]
              /\ UNCHANGED <<occupation, prev_occup>>
BeginWaiting(p) == /\ state[p] = "sentRequest"
                   /\ state' = [state EXCEPT ![p] = "waiting"]
                   /\ UNCHANGED <<occupation,flag,prev_occup>>
EnterCritical(p) == /\ state[p] = "waiting"
                    /\ \A pi \in 0..N-1 : occupation[pi] = FALSE
                    /\ prev_occup[p] = FALSE \/ \A pii \in 0..N-1 : flag[pii] = FALSE \/ pii = p
                    /\ state' = [state EXCEPT ![p] = "critical"]
                    /\ occupation' = [occupation EXCEPT ![p] = TRUE]
                    /\ UNCHANGED <<prev_occup,flag>>
ExitCritical(p) == /\ state[p] = "critical"
                   /\ state' = [state EXCEPT ![p] = "idle"]
                   /\ IF \A pii \in 0..N-1 : prev_occup[pii]=TRUE \/ flag[pii] = FALSE \/ pii=p
                        THEN prev_occup' = [i \in 0..N-1 |-> FALSE] 
                        ELSE prev_occup' = [prev_occup EXCEPT ![p] = TRUE]
                   /\ occupation' = [occupation EXCEPT ![p] = FALSE]
                   /\ flag' = [flag EXCEPT ![p] = FALSE]
Next == /\ \E p \in 0..N-1 :
            \/ Request(p)
            \/ BeginWaiting(p)
            \/ EnterCritical(p)
            \/ ExitCritical(p)
        /\ step' = step + 1
Spec == Init /\ [][Next]_<<state, occupation, step, flag, prev_occup>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Fri Dec 04 13:44:14 CST 2020 by 26632
\* Created Sat Nov 07 11:17:25 CST 2020 by 26632
