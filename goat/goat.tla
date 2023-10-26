-------------------------------- MODULE goat --------------------------------
\* Modification History
\* Last modified Wed Oct 25 09:42:34 PDT 2023 by ethanxh
\* Created Tue Oct 24 09:42:59 PDT 2023 by ethanxh
CONSTANTS ITEMS
VARIABLES left, right, boat

W == "WOLF"
G == "GOAT"
C == "CABBAGE"

ASSUME ITEMS = {W, G, C}

vars == <<left, right, boat>>

INIT == 
    /\ left = ITEMS
    /\ right = {}
    /\ boat = 0 (* 0 for left bank, 1 for right bank *)

NotSafe(side) == 
    \/ (W \in side /\ G \in side)
    \/ (G \in side /\ C \in side)

Safe(side) == ~NotSafe(side)

IsSafe == 
\*  If boat on the left side we want to make sure the right side is safe
    /\ (boat = 0 => Safe(right))
\*  Similarily, the left side should be safe if boat is on the right
    /\ (boat = 1 => Safe(left))

MOVE(item) == 
    IF boat = 0 THEN
        /\ item \in left
        /\ Safe(left \ {item})
        /\ right' = right \union {item}
        /\ left' = left \ {item}
        /\ boat' = 1
    ELSE
        /\ item \in right
        /\ Safe(right \ {item})
        /\ left' = left \union {item}
        /\ right' = right \ {item}
        /\ boat' = 0


MoveBoat(b) ==
    IF boat = 1 THEN
        /\ Safe(right)
        /\ boat' = 0
        /\ UNCHANGED <<left, right>>
    ELSE
        /\ Safe(left)
        /\ boat' = 1
        /\ UNCHANGED <<left, right>>

Next == 
    \/ \E item \in ITEMS: MOVE(item)
    \/ MoveBoat(boat)

Termination == right = ITEMS

Spec == 
    INIT /\ [][Next]_vars /\ WF_vars(Next) /\ <>[]Termination

=============================================================================