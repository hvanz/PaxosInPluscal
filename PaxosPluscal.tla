--------------------------- MODULE PaxosPluscal -----------------------------
(***************************************************************************)
(* This module contains a version of the Paxos algorithm written in        *)
(* PlusCal, with a proof of the consistency property.  In this             *)
(* specification, the two participants, acceptor and proposer/learner, are *)
(* modeled as disjoint processes, each with their own invariant            *)
(* properties.                                                             *)
(*                                                                         *)
(* The goal of this spec and proof is to obtain a low-level model of the   *)
(* algorithm, closer to an implementation in an imperative language, with  *)
(* disjoint invariants for the proposer and the acceptor, i.e., formulas   *)
(* that do not share variables (except one variable representing network   *)
(* communication).  Consequently, ballots are modeled as tuples of ballot  *)
(* number and proposer id, the main processes are enclosed in an infinite  *)
(* loop, and proposers have a local variable that keep track of the        *)
(* acceptors that replied to it, which is used to compute quorums.         *)
(*                                                                         *)
(* Additionally, this specification includes an optimization that allows a *)
(* proposer to preempt and restart its execution when it receives a        *)
(* message from an acceptor with a higher ballot than its own.             *)
(*                                                                         *)
(* This spec was built starting from the simpler TLA+ spec of Paxos by     *)
(* Leslie Lamport where only acceptors were modeled.                       *)
(*                                                                         *)
(* Proved with TLAPS v1.4.3, CVC4 v1.4, and Z3 v4.3.2.                     *)
(*                                                                         *)
(* Author: `^Hern\'an Vanzetto, 2018^'.                                    *)
(***************************************************************************)
EXTENDS Integers, TLAPS, TLC, Sequences, SequenceTheorems

CONSTANTS 
  Acceptors, \* Set of acceptor ids. 
  Proposers, \* Set of proposer ids.
  Values,    \* Set of values that proposers are allowed to vote for.
  Quorums    \* Set of possible quorums of acceptor ids.

ASSUME QuorumAssumption1 == Quorums \subseteq SUBSET Acceptors
ASSUME QuorumAssumption2 == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
BY QuorumAssumption2

ASSUME ProposersNat == \A p \in Proposers: p \in Nat

(* A ballot is a tuple composed of a ballot number and a proposer id. *)
ValidBallots == Nat \X Proposers
NoBallot == << -1, -1 >>
Ballots == ValidBallots \cup {NoBallot}
USE DEF Ballots 

NoValue == CHOOSE v : v \notin Values

LEMMA NoValueNotAValue == NoValue \notin Values
BY NoSetContainsEverything DEF NoValue
 
Messages ==
       [type : {"1a"}, from : Proposers, bal : ValidBallots]
  \cup [type : {"1b"}, from : Acceptors, bal : ValidBallots, 
        to: Proposers, vbal : Ballots, vval : Values \cup {NoValue}]
  \cup [type : {"2a"}, from : Proposers, bal : ValidBallots, val : Values]
  \cup [type : {"2b"}, from : Acceptors, bal : ValidBallots,
        to: Proposers, val : Values \cup {NoValue}]

(***    this is a comment containing the PlusCal code *
--algorithm Paxos

variables 
    msgs = {} \* The set of messages that have been sent by proposers and acceptors, 
              \* representing the history of network communication.

define 
    \* The next ballot of b increases the ballot number by one:
    nextBallot(b,p) == IF b = NoBallot THEN << 0, p >> ELSE << b[1] + 1, p >>
    \* Lexicographic order of ballots:
    a \prec b == 
        \/ a[1] < b[1] 
        \/ a[1] = b[1] /\ a[2] < b[2] 
    a \preceq b == a \prec b \/ a = b 
end define;

macro Send(m) begin msgs := msgs \cup {m}; end macro;

process prop \in Proposers
    variables 
        pBal = NoBallot,  \* For each proposer, its ballot number.
        pVBal = NoBallot, \* For each proposer, ballot of the highest registered vote.
        pVVal = NoValue,  \* For each proposer, value of the highest registered vote.
        pQ1 = {},         \* Sets of acceptor ids for keeping record of "1b" and "2b"
        pQ2 = {},         \*   messages, repectively, received by each proposer.
        pWr = FALSE,      \* pWr[p] = Is proposer p's voted value pVVal written?
        pLBal = NoBallot; \* Ballot of the last "2a" message sent by proposer.

begin
P1: while TRUE do
        \********************************************************************
        \* Proposer step 1 [Set and send ballot].  Set the ballot number to  
        \* the current number plus one, store that number in pBal, and send a  
        \* "1a" message to all acceptors.
        \*                                                                         
        \* A proposer p can be preempted.  Some acceptor may preempt the  
        \* execution of p by replying to p with a ballot number higher than       
        \* p's ballot.  In this case, p is enabled to execute action P1 again  
        \* and allowed to set a new ballot number.  
        \* Resetting the variables pVBal, pVVal, pQ1 and pQ2 is required in
        \* case process prop was preempted.                                                                
        \********************************************************************
        when pWr = FALSE;
        pBal := nextBallot(pBal,self);
        Send([type |-> "1a", from |-> self, bal |-> pBal]);
        pVBal := NoBallot; 
        pVVal := NoValue;
        pQ1 := {};
        pQ2 := {}; 
P2:
        \********************************************************************
        \* Proposer step 2a [Wait]. Receive and process one "1b" message at a 
        \* time, until a quorum of acceptors have replied. The messages must 
        \* satisfy the following conditions: p is the message's target, the 
        \* message has the same ballot as the proposer's. The sender ids (the 
        \* acceptors ids) are recorded in pQ1, until there is a majority of 
        \* acceptors in pQ1. If the message's ballot is higher than the 
        \* current ballot, the execution is aborted and restarted from P1.
        \* The variables pVBal and pVVal store the ballot and vote of the 
        \* highest-seen ballot, discarding the votes that come with the lower 
        \* ballots.
        \********************************************************************
        while pQ1 \notin Quorums do
            with m \in { x \in msgs : /\ x.type = "1b" 
                                      /\ x.to = self 
                                      /\ x.from \notin pQ1} do
                if m.bal = pBal then
                    pQ1 := pQ1 \cup {m.from};
                    if pVBal \prec m.vbal then
                        pVBal := m.vbal;
                        pVVal := m.vval; 
                    end if;
                elsif pBal \prec m.bal then
                    goto P1;
                end if
            end with
        end while;
        \********************************************************************
        \* Proposer step 2b [Select and send value].  Now there is a set of       
        \* "1a" messages from a quorum of acceptors, whose ids are stored in        
        \* pQ1 (so pQ1 \in Quorums). This step selects a value to propose in            
        \* the following way.  If pVBal = NoBallot, some value is selected      
        \* non-deterministically, representing a value passed as an argument      
        \* to the proposer. Otherwise, if there is a valid ballot in pVBal,  
        \* the value to be sent is in pVVal.
        \* The conditions pQ1 \in Quorums /\ pQ2 = {} /\ pLBal \prec pBal  
        \* are redundant; they just help simplify the invariants by not  
        \* relying on the variable pc, specifically the condition pc[p] = "P2".
        \********************************************************************
        when pQ1 \in Quorums /\ pQ2 = {} /\ pLBal \prec pBal; 
        with v \in Values do
           when pVBal = NoBallot \/ (pVBal \in ValidBallots /\ v = pVVal);
           Send([type |-> "2a", from |-> self, bal |-> pBal, val |-> v]);
           pLBal := pBal;
        end with;
P3:    
        \********************************************************************
        \* Proposer step 3 [Wait and Learn].  Collect "2b" messages while    
        \* recording the senders in pQ2, until there is a majority of                                                                  
        \* acceptors in pQ2.  If there is a majority of "2b" messages, the    
        \* proposer learns that the selected value has been voted.  The    
        \* proposer takes the vote from the last "2b" message, stores the                                                                    
        \* voted ballot and value, and set it to "written". If the message's   
        \* ballot is higher than the proposer's ballot, abort the execution 
        \* and restart from P1.
        \********************************************************************
        while pQ2 \notin Quorums do
            with m \in {x \in msgs : /\ x.type = "2b" 
                                     /\ x.to = self  
                                     /\ x.from \notin pQ2 
                                     /\ x.val \in Values } do 
                if m.bal = pBal then
                    pQ2 := pQ2 \cup {m.from};
                    pVBal := m.bal;
                    pVVal := m.val;
                elsif pBal \prec m.bal then
                    goto P1;
                end if
            end with
        end while;
        pWr := TRUE;
    end while
end process;

process acc \in Acceptors
    variables 
      aBal = NoBallot,  \* The highest-numbered ballot acceptor acc has participated in. 
      aVBal = NoBallot, \* The highest ballot in which the acceptor has voted, and
      aVVal = NoValue;  \*   the value it voted for in that ballot.
      
begin
A1: while TRUE do
        with m \in msgs do
        either
            \****************************************************************
            \* Acceptor phase 1 [Promise].  Acceptor acc process a "1a"        
            \* message only if the message's ballot is strictly higher than      
            \* the acceptor's current ballot.  It updates the highest seen  
            \* ballot number.  In this version of Paxos with preemption, the          
            \* acceptor always responds with the highest ballot it has seen.   
            \* If this number is higher than the recipient's ballot, it will      
            \* cause its preemption.  If acceptor and proposer are        
            \* participating in the same ballot b, the "1b" response is a 
            \* promise from the acceptor of not accepting any proposals for 
            \* ballots less than b.            
            \****************************************************************
            when m.type = "1a";
            if aBal \prec m.bal then aBal := m.bal; end if;
            Send([type |-> "1b", from |-> self, to |-> m.from,
                  bal |-> aBal, vbal |-> aVBal, vval |-> aVVal]);
        or
            \****************************************************************
            \* Acceptor phase 2 [Vote]: If an acceptor receives a "2a"      
            \* message for a ballot numbered b, it votes for the message's 
            \* value in ballot b unless it has already responded to a "1a" 
            \* request for a ballot number greater than or equal to b.     
            \* In the latter case, the acceptor responds with a NoValue value  
            \* to tell the proposer to not use that ballot number.                                                 
            \****************************************************************
            when m.type = "2a";
            if aBal \preceq m.bal then 
                aBal := m.bal;
                aVBal := m.bal;
                aVVal := m.val; 
                Send([type |-> "2b", from |-> self, to |-> m.from, 
                      bal |-> m.bal, val |-> m.val]);
            else
                Send([type |-> "2b", from |-> self, to |-> m.from, 
                      bal |-> aBal, val |-> NoValue]);
            end if
        end either
        end with
    end while  
end process 

end algorithm
***        this ends the comment containg the pluscal code        **********)

(***************************************************************************)
(* The following TLA+ spec definitions were automatically translated from  *)
(* the PlusCal program above.  Do not modify them manually.                *)
(***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES msgs, pc

(* define statement *)
nextBallot(b,p) == IF b = NoBallot THEN << 0, p >> ELSE << b[1] + 1, p >>

a \prec b ==
    \/ a[1] < b[1]
    \/ a[1] = b[1] /\ a[2] < b[2]
a \preceq b == a \prec b \/ a = b

VARIABLES pBal, pVBal, pVVal, pQ1, pQ2, pWr, pLBal, aBal, aVBal, aVVal

vars == << msgs, pc, pBal, pVBal, pVVal, pQ1, pQ2, pWr, pLBal, aBal, aVBal, 
           aVVal >>

ProcSet == (Proposers) \cup (Acceptors)

Init == (* Global variables *)
        /\ msgs = {}
        (* Process prop *)
        /\ pBal = [self \in Proposers |-> NoBallot]
        /\ pVBal = [self \in Proposers |-> NoBallot]
        /\ pVVal = [self \in Proposers |-> NoValue]
        /\ pQ1 = [self \in Proposers |-> {}]
        /\ pQ2 = [self \in Proposers |-> {}]
        /\ pWr = [self \in Proposers |-> FALSE]
        /\ pLBal = [self \in Proposers |-> NoBallot]
        (* Process acc *)
        /\ aBal = [self \in Acceptors |-> NoBallot]
        /\ aVBal = [self \in Acceptors |-> NoBallot]
        /\ aVVal = [self \in Acceptors |-> NoValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Proposers -> "P1"
                                        [] self \in Acceptors -> "A1"]

P1(self) == /\ pc[self] = "P1"
            /\ pWr[self] = FALSE
            /\ pBal' = [pBal EXCEPT ![self] = nextBallot(pBal[self],self)]
            /\ msgs' = (msgs \cup {([type |-> "1a", from |-> self, bal |-> pBal'[self]])})
            /\ pVBal' = [pVBal EXCEPT ![self] = NoBallot]
            /\ pVVal' = [pVVal EXCEPT ![self] = NoValue]
            /\ pQ1' = [pQ1 EXCEPT ![self] = {}]
            /\ pQ2' = [pQ2 EXCEPT ![self] = {}]
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << pWr, pLBal, aBal, aVBal, aVVal >>

P2(self) == /\ pc[self] = "P2"
            /\ IF pQ1[self] \notin Quorums
                  THEN /\ \E m \in { x \in msgs : /\ x.type = "1b"
                                                  /\ x.to = self
                                                  /\ x.from \notin pQ1[self]}:
                            IF m.bal = pBal[self]
                               THEN /\ pQ1' = [pQ1 EXCEPT ![self] = pQ1[self] \cup {m.from}]
                                    /\ IF pVBal[self] \prec m.vbal
                                          THEN /\ pVBal' = [pVBal EXCEPT ![self] = m.vbal]
                                               /\ pVVal' = [pVVal EXCEPT ![self] = m.vval]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED << pVBal, pVVal >>
                                    /\ pc' = [pc EXCEPT ![self] = "P2"]
                               ELSE /\ IF pBal[self] \prec m.bal
                                          THEN /\ pc' = [pc EXCEPT ![self] = "P1"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "P2"]
                                    /\ UNCHANGED << pVBal, pVVal, pQ1 >>
                       /\ UNCHANGED << msgs, pLBal >>
                  ELSE /\ pQ1[self] \in Quorums /\ pQ2[self] = {} /\ pLBal[self] \prec pBal[self]
                       /\ \E v \in Values:
                            /\ pVBal[self] = NoBallot \/ (pVBal[self] \in ValidBallots /\ v = pVVal[self])
                            /\ msgs' = (msgs \cup {([type |-> "2a", from |-> self, bal |-> pBal[self], val |-> v])})
                            /\ pLBal' = [pLBal EXCEPT ![self] = pBal[self]]
                       /\ pc' = [pc EXCEPT ![self] = "P3"]
                       /\ UNCHANGED << pVBal, pVVal, pQ1 >>
            /\ UNCHANGED << pBal, pQ2, pWr, aBal, aVBal, aVVal >>

P3(self) == /\ pc[self] = "P3"
            /\ IF pQ2[self] \notin Quorums
                  THEN /\ \E m \in {x \in msgs : /\ x.type = "2b"
                                                 /\ x.to = self
                                                 /\ x.from \notin pQ2[self]
                                                 /\ x.val \in Values }:
                            IF m.bal = pBal[self]
                               THEN /\ pQ2' = [pQ2 EXCEPT ![self] = pQ2[self] \cup {m.from}]
                                    /\ pVBal' = [pVBal EXCEPT ![self] = m.bal]
                                    /\ pVVal' = [pVVal EXCEPT ![self] = m.val]
                                    /\ pc' = [pc EXCEPT ![self] = "P3"]
                               ELSE /\ IF pBal[self] \prec m.bal
                                          THEN /\ pc' = [pc EXCEPT ![self] = "P1"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "P3"]
                                    /\ UNCHANGED << pVBal, pVVal, pQ2 >>
                       /\ pWr' = pWr
                  ELSE /\ pWr' = [pWr EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "P1"]
                       /\ UNCHANGED << pVBal, pVVal, pQ2 >>
            /\ UNCHANGED << msgs, pBal, pQ1, pLBal, aBal, aVBal, aVVal >>

prop(self) == P1(self) \/ P2(self) \/ P3(self)

A1(self) == /\ pc[self] = "A1"
            /\ \E m \in msgs:
                 \/ /\ m.type = "1a"
                    /\ IF aBal[self] \prec m.bal
                          THEN /\ aBal' = [aBal EXCEPT ![self] = m.bal]
                          ELSE /\ TRUE
                               /\ aBal' = aBal
                    /\ msgs' = (msgs \cup {([type |-> "1b", from |-> self, to |-> m.from,
                                             bal |-> aBal'[self], vbal |-> aVBal[self], vval |-> aVVal[self]])})
                    /\ UNCHANGED <<aVBal, aVVal>>
                 \/ /\ m.type = "2a"
                    /\ IF aBal[self] \preceq m.bal
                          THEN /\ aBal' = [aBal EXCEPT ![self] = m.bal]
                               /\ aVBal' = [aVBal EXCEPT ![self] = m.bal]
                               /\ aVVal' = [aVVal EXCEPT ![self] = m.val]
                               /\ msgs' = (msgs \cup {([type |-> "2b", from |-> self, to |-> m.from,
                                                        bal |-> m.bal, val |-> m.val])})
                          ELSE /\ msgs' = (msgs \cup {([type |-> "2b", from |-> self, to |-> m.from,
                                                        bal |-> aBal[self], val |-> NoValue])})
                               /\ UNCHANGED << aBal, aVBal, aVVal >>
            /\ pc' = [pc EXCEPT ![self] = "A1"]
            /\ UNCHANGED << pBal, pVBal, pVVal, pQ1, pQ2, pWr, pLBal >>

acc(self) == A1(self)

Next == (\E self \in Proposers: prop(self))
           \/ (\E self \in Acceptors: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Extra spec definitions.  We split the specification variables into      *)
(* variables that are shared (messages and pc), and variables for          *)
(* proposers and for acceptors.                                            *)
(***************************************************************************)
\** shared variables
svars == <<msgs, pc>>
\** proposer variables
pvars == <<pBal, pVBal, pVVal, pWr, pQ1, pQ2, pLBal>>
\** acceptor variables
avars == <<aBal, aVBal, aVVal>>

\** shared variables initial state
SInit ==
  /\ msgs  = {}
  /\ pc = [self \in ProcSet |-> CASE self \in Proposers -> "P1"
                                  [] self \in Acceptors -> "A1"]

\** proposer initial state
PInit ==
  /\ pBal  = [p \in Proposers |-> NoBallot]
  /\ pVBal = [p \in Proposers |-> NoBallot]
  /\ pVVal = [p \in Proposers |-> NoValue]
  /\ pWr   = [p \in Proposers |-> FALSE]
  /\ pQ1   = [p \in Proposers |-> {}]
  /\ pQ2   = [p \in Proposers |-> {}]
  /\ pLBal = [p \in Proposers |-> NoBallot]

\** acceptor initial state
AInit == 
  /\ aBal  = [a \in Acceptors |-> NoBallot]
  /\ aVBal = [a \in Acceptors |-> NoBallot]
  /\ aVVal = [a \in Acceptors |-> NoValue]

\** proposer spec
PNext == \E p \in Proposers : P1(p) \/ P2(p) \/ P3(p)
PSpec == (SInit /\ PInit) /\ [][PNext]_(svars \o pvars)

\** acceptor spec
ANext == \E a \in Acceptors : A1(a)
ASpec == (SInit /\ AInit) /\ [][ANext]_(svars \o avars)

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness invariants.                                            *)
(***************************************************************************)
STypeOK == 
  /\ msgs  \in SUBSET Messages
  /\ pc    \in [Acceptors \cup Proposers -> {"A1","P1","P2","P3"}]

ATypeOK == 
  /\ aBal  \in [Acceptors -> Ballots]
  /\ aVBal \in [Acceptors -> Ballots]
  /\ aVVal \in [Acceptors -> Values \cup {NoValue}]

PTypeOK == 
  /\ pBal  \in [Proposers -> Ballots]
  /\ pVBal \in [Proposers -> Ballots]
  /\ pVVal \in [Proposers -> Values \cup {NoValue}]
  /\ pWr   \in [Proposers -> BOOLEAN]
  /\ pQ1   \in [Proposers -> SUBSET Acceptors]
  /\ pQ2   \in [Proposers -> SUBSET Acceptors]
  /\ pLBal \in [Proposers -> Ballots]
  
-----------------------------------------------------------------------------
(***************************************************************************)
(* Chosen(v) means that v has been chosen by a majority of acceptors.      *)
(***************************************************************************)
VotedForIn(a, v, b) == 
  \E m \in msgs : /\ m.type = "2b"
                  /\ m.from = a
                  /\ m.val  = v
                  /\ m.bal  = b
                  /\ m.val \in Values \* For preemption, the acceptor sends a "2b" with a NoValue.

ChosenIn(v, b) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in ValidBallots : ChosenIn(v, b)

(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
AConsistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)

-----------------------------------------------------------------------------
(***************************************************************************)
(* DidntVoteIn(a, b) = "acceptor a has not voted in ballot b".             *)
(***************************************************************************)
DidntVoteIn(a, b) == \A v \in Values : ~ VotedForIn(a, v, b)

(***************************************************************************)
(* An acceptor a took part in a voting process with ballot d if it         *)
(* responded to that ballot, in either of both phases.                     *)
(***************************************************************************)
ParticipatedIn(a, d) ==
  \E m \in msgs: /\ \/ m.type = "1b"
                    \/ m.type = "2b" /\ m.val \in Values  
                 /\ m.from = a 
                 /\ m.bal = d 

(***************************************************************************)
(* An acceptor a won't vote in ballot c if it participates in a ballot d   *)
(* greater than c.  We will prove later that this is equivalent to the     *)
(* formula c < aBal[a].                                                    *)
(***************************************************************************)
WontVoteIn(a, c) == \E d \in ValidBallots: c \prec d /\ ParticipatedIn(a, d)

(***************************************************************************)
(* The predicate SafeAt is a key invariant for the proof.  It means that   *)
(* it is "safe" for any proposer to vote for value v in ballot b.          *)
(*                                                                         *)
(* Formally, safe means that at each ballot number c that is lower than b, *)
(* we can take a majority of acceptors Q with the following disjunctive    *)
(* property.  The first possibility is that the acceptor in Q voted in     *)
(* that ballot c, in which case it must have voted for value v.  Note that *)
(* not necessarilly a majority of acceptors voted in that ballot.  The     *)
(* second possibility is that the acceptor in Q did not vote in ballot c   *)
(* and will not able to vote in c.                                         *)
(*                                                                         *)
(* The formula SafeAt is a property about sets of acceptor ids and         *)
(* messages sent by acceptors.  This formula is equivalent to Lamport's,   *)
(* but it does not mention acceptor or proposer variables.                 *)
(***************************************************************************)
SafeAt(v, b) ==
  \A c \in ValidBallots: c \prec b =>
     \E Q \in Quorums :
        \A a \in Q : \/ VotedForIn(a, v, c) 
                     \/ /\ DidntVoteIn(a, c)
                        /\ WontVoteIn(a, c)  \* This last condition is not required 
                                             \* for the consistency proofs, but for   
                                             \* making the SafeAt predicate inductive.
  
-----------------------------------------------------------------------------
(***************************************************************************)
(*  `^\textbf{Acceptor properties and invariants}^'                        *)
(***************************************************************************)

(***************************************************************************)
(* AMsgInv: Acceptor's message invariant.  How messages "1b" and "2b" sent *)
(* by an acceptor with id m.from are related to other messages.            *)
(***************************************************************************)
AMsgInv ==
  \A m \in msgs :
     /\ (m.type = "1b") =>
          /\ AM2(m):: m.vbal \preceq m.bal
          /\ AM3(m):: \/ /\ m.vval \in Values
                         /\ m.vbal \in ValidBallots
                         /\ VotedForIn(m.from, m.vval, m.vbal)
                      \/ /\ m.vval = NoValue
                         /\ m.vbal = NoBallot
          /\ AM4(m):: \A c \in ValidBallots: 
                        m.vbal \prec c /\ c \prec m.bal => DidntVoteIn(m.from, c)
     /\ (m.type = "2b") /\ (m.val \in Values) =>
          /\ AM5(m):: \E mp \in msgs : /\ mp.type = "2a"
                                       /\ mp.from = m.to
                                       /\ mp.bal  = m.bal
                                       /\ mp.val  = m.val

(***************************************************************************)
(* AStateInv: Inductive invariant about the acceptor variables.  Note that *)
(* proposer variables do not appear in this formula.                       *)
(***************************************************************************)
AStateInv ==
  \A a \in Acceptors:
     /\ AS1(a):: aVBal[a] = NoBallot <=> aVVal[a] = NoValue
     /\ AS2(a):: aVBal[a] \preceq aBal[a]
     /\ AS3(a):: aVBal[a] \in ValidBallots => VotedForIn(a, aVVal[a], aVBal[a])
     /\ AS4(a):: \A b \in Ballots : aVBal[a] \prec b => DidntVoteIn(a, b)
     /\ AS5(a):: \A b \in Ballots : WontVoteIn(a, b) <=> b \prec aBal[a]
     /\ AS6(a):: \A m \in msgs: m.from = a /\ (m.type = "1b") => m.bal \preceq aBal[a] 
     /\ AS7(a):: \A m \in msgs: m.from = a /\ (m.type = "2b") /\ (m.val \in Values) 
                   => m.bal \preceq aVBal[a]

-----------------------------------------------------------------------------
(***************************************************************************)
(*  `^\textbf{Proposer properties and invariants}^'                        *)
(***************************************************************************)

(***************************************************************************)
(* PKnowsIn(p,v,b): "proposer p knows that value v was chosen at ballot b" *)
(***************************************************************************)
PKnowsIn(p,v,b) == pWr[p] /\ pVBal[p] = b /\ pVVal[p] = v

PKnows(p,v) == \E b \in ValidBallots : PKnowsIn(p, v, b)

PConsistency ==
  \A p1, p2 \in Proposers: \A v1, v2 \in Values :
     PKnows(p1, v1) /\ PKnows(p1, v2) => (v1 = v2)

(***************************************************************************)
(* PMsgInv: Proposer's message invariant.                                  *)
(***************************************************************************)
PMsgInv ==
  \A m \in msgs :
    LET p == m.from IN
    /\ m.type = "2a" =>
       /\ PM1(m):: \A ma \in msgs : 
            (ma.type = "2a") /\ (ma.bal = m.bal) => (ma.val = m.val)
          \* A proposer that attempts to write a value v, it can only write 
          \* the same value that was attempted before for the same ballot.
          \* Required to prove VotedOnce and KnowsSameValue.
       /\ PM2(m):: SafeAt(m.val, m.bal)
    /\ m.type = "2a" /\ p = pBal[p][2] =>
       /\ PM3(m):: m.bal = pBal[p] => pQ1[p] \in Quorums 
          \* Required in proofs of step P2b.
       /\ PM4(m):: m.bal = pBal[p] /\ pVBal[p] \in ValidBallots /\ pQ2[p] \notin Quorums 
                   => m.val = pVVal[p]      
          \* Required to prove PS7, step P2b.
    /\ PM5(m):: m.type \in {"1a","2a"} => p = m.bal[2]

(***************************************************************************)
(* Msg1bOK(p,S) expresses the relation between proposer p's state          *)
(* variables and the messages it received for the first phase.             *)
(*                                                                         *)
(* For proposer p, the "1b" messages received by p satisfy the following   *)
(* properties.  (1) There is a bijection between the set of "1b" messages  *)
(* and the set pQ1[p] of acceptor ids that sent those messages.  (2) There *)
(* are two disjoint cases for the messages in S: (2a) If p's current voted *)
(* ballot pVBal[p] contains the initial value, it is because all acceptors *)
(* that replied didn't cast any vote yet.  (2b) If p has recorded a valid  *)
(* vote <<pVBal[p], pVVal[p]>>, then that vote has the highest ballot      *)
(* number of all "1b" replies; moreover, that vote was sent by at least    *)
(* one acceptor in a "1b" message --if the proposer didn't learn a value   *)
(* yet (~ pWr[p]), because the proposed value in "2a" could come from a    *)
(* not yet processed "1b" message.                                         *)
(***************************************************************************)
Msg1bOK(p,S) ==
  /\ \A m \in S : m.type = "1b" /\ m.to = p /\ m.bal = pBal[p] /\ m.from \in pQ1[p]
  /\ \A a \in pQ1[p] : \E m \in S : m.from = a 
  /\ IF pVBal[p] = NoBallot 
     THEN \A m \in S : m.vbal = NoBallot
     ELSE /\ \A m \in S : m.vbal \preceq pVBal[p]
          /\ ~ pWr[p] => \E m \in S : m.vbal = pVBal[p] /\ m.vval = pVVal[p]

(***************************************************************************)
(* Msg2bOK(p,S) expresses the relation between proposer p's state          *)
(* variables and the messages it received for the second phase.            *)
(***************************************************************************)
Msg2bOK(p,S) ==
  /\ \A m \in S : /\ m.type = "2b" /\ m.to = p /\ m.bal = pBal[p] 
                  /\ m.from \in pQ2[p] /\ m.val \in Values
  /\ \A a \in pQ2[p] : \E m \in S : m.from = a

(***************************************************************************)
(* PStateInv: Inductive invariant about the proposer variables.  Note that *)
(* acceptor variables do not appear in the formula.                        *)
(***************************************************************************)
PStateInv ==
  \A p \in Proposers:
    /\ PS1(p):: pVBal[p] = NoBallot <=> pVVal[p] = NoValue
    /\ PS2(p):: pVBal[p] \preceq pBal[p] 
    /\ PS3(p):: pVBal[p] \in ValidBallots => pBal[p] \in ValidBallots
    /\ PS4(p):: pQ1[p] = {} => pVBal[p] = NoBallot /\ pVVal[p] = NoValue
    /\ PS5(p):: pQ1[p] # {} /\ pQ2[p] = {} => 
                pBal[p] \in ValidBallots /\ \E S \in SUBSET msgs: Msg1bOK(p,S)
    /\ PS6(p):: pQ2[p] # {} => 
                pVBal[p] = pBal[p] /\ \E S \in SUBSET msgs: Msg2bOK(p,S)
    /\ PS7(p):: pVBal[p] \in ValidBallots => 
                \A a \in pQ2[p] : VotedForIn(a, pVVal[p], pBal[p]) \* Used in PConsistent. 
    /\ PS8(p):: pWr[p] => pQ1[p] \in Quorums /\ pQ2[p] \in Quorums /\ pVBal[p] = pBal[p]
    /\ PS9(p):: \A a \in pQ1[p], c \in ValidBallots: 
                  pVBal[p] \prec c /\ c \prec pBal[p] =>
                  DidntVoteIn(a, c) /\ WontVoteIn(a, c) \* For proving SafeAt
    /\ PS10(p):: pQ1[p] \notin Quorums => pQ2[p] = {} \* Required for step <4>2 of PS6.
    /\ PS11(p):: pLBal[p] \preceq pBal[p]
    /\ PS12(p):: \A m \in msgs: m.type = "1a" /\ m.from = p => m.bal \preceq pBal[p] 
    /\ PS13(p):: \A m \in msgs: m.type = "2a" /\ m.from = p => m.bal \preceq pLBal[p]
    /\ PS14(p):: pBal[p] \in ValidBallots => pBal[p][2] = p

-----------------------------------------------------------------------------
(***************************************************************************)
(* Inv is the inductive invariant of the whole system.                     *)
(***************************************************************************)
\** proposer invariant
PInv == STypeOK /\ PTypeOK /\ PMsgInv /\ PStateInv
\** acceptor invariant
AInv == STypeOK /\ ATypeOK /\ AMsgInv /\ AStateInv 
\** whole system's invariant
Inv == PInv /\ AInv 

-----------------------------------------------------------------------------
(***************************************************************************)
(* VotedOnce: When two values are voted in the same ballot, then those     *)
(* values must be equal, regardless of which acceptor voted.               *)
(***************************************************************************)
LEMMA VotedOnce ==
  ASSUME AMsgInv, PMsgInv
  PROVE  \A a1, a2 \in Acceptors, b \in ValidBallots, v1, v2 \in Values :
           VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
BY Z3 DEF PMsgInv, AMsgInv, VotedForIn
    \* From VotedForIn(a1, v1, b), there exists a "2a" message for ballot b,
    \* by AM5.  Equally for VotedForIn(a2, v2, b), there exists another "2a"
    \* message for b.  Then v1 = v2, by PM1.

(***************************************************************************)
(* KnowsSameValue: If two proposers learn some values in the same ballot,  *)
(* then those values must be the same.                                     *)
(***************************************************************************)
LEMMA KnowsSameValue ==
  ASSUME AMsgInv, PMsgInv, PStateInv
  PROVE  \A p1, p2 \in Proposers, b \in ValidBallots, v1, v2 \in Values :
           PKnowsIn(p1, v1, b) /\ PKnowsIn(p2, v2, b) => (v1 = v2)
<1> SUFFICES ASSUME NEW p1 \in Proposers, NEW p2 \in Proposers, 
                    NEW b \in ValidBallots, 
                    NEW v1 \in Values, NEW v2 \in Values,
                    PKnowsIn(p1, v1, b), PKnowsIn(p2, v2, b)
             PROVE  v1 = v2
  OBVIOUS
<1>1. pQ2[p1] \in Quorums /\ \A a \in pQ2[p1]: VotedForIn(a,v1,b)
  BY Z3 DEF PKnowsIn, PStateInv
<1>2. pQ2[p2] \in Quorums /\ \A a \in pQ2[p2]: VotedForIn(a,v2,b)
  BY Z3 DEF PKnowsIn, PStateInv
<1> QED
  BY <1>1, <1>2, QuorumAssumption2, Z3 DEF PKnowsIn, PMsgInv, AMsgInv, VotedForIn

(***************************************************************************)
(* VotedInv: If an acceptor voted for a value, it was because that value   *)
(* was safe (at the same ballot as the vote).                              *)
(***************************************************************************)
LEMMA VotedInv ==
  ASSUME AMsgInv, PMsgInv
  PROVE  \A a \in Acceptors, v \in Values, b \in ValidBallots :
           VotedForIn(a, v, b) => SafeAt(v, b) 
BY DEF AMsgInv, PMsgInv, VotedForIn, SafeAt

(***************************************************************************)
(* Corollary of PStateInv!PS6 and AMsgInv!AM5.                             *)
(***************************************************************************)
COROLLARY ExistsQuorum1 ==
  ASSUME STypeOK, PStateInv, AMsgInv, PMsgInv
  PROVE  \A p \in Proposers: pQ2[p] # {} => pQ1[p] \in Quorums
<1> TAKE p \in Proposers
<1> HAVE pQ2[p] # {}
<1> PICK a \in pQ2[p] : TRUE
  OBVIOUS
<1> PICK m2b \in msgs : /\ m2b.type = "2b" 
                        /\ m2b.from = a
                        /\ m2b.to = p 
                        /\ m2b.bal = pBal[p]
                        /\ m2b.val \in Values
  BY DEF STypeOK, Messages, PStateInv, Msg2bOK
<1> PICK m2a \in msgs : /\ m2a.type = "2a"
                        /\ m2a.from = m2b.to
                        /\ m2a.bal  = m2b.bal
                        /\ m2a.val  = m2b.val
  BY DEF STypeOK, Messages, AMsgInv
<1> QED
  BY DEF PMsgInv

-----------------------------------------------------------------------------
(***************************************************************************)
(* `^\textbf{Properties about Ballots, ballot order \prec and NoBallot.}^' *)
(***************************************************************************)

LEMMA SpecialPairEqualIffCase1 ==
  ASSUME NEW A, NEW B, NEW x, NEW y,
         NEW a \in A \X B \cup {<<x,y>>}, 
         NEW b \in A \X B \cup {<<x,y>>}
  PROVE  a[1] = b[1] /\ a[2] = b[2] => (a = b)
OBVIOUS (*{by (isabelle "(auto simp: fcnEqualIff prod_def)")}*)

THEOREM BallotEq == 
  \A a, b \in Ballots: a = b <=> a[1] = b[1] /\ a[2] = b[2] 
BY ProposersNat, SpecialPairEqualIffCase1, Zenon DEFS ValidBallots, NoBallot
  
LEMMA BallotLeRefl == \A b \in Ballots: b \preceq b
BY DEFS ValidBallots, \preceq
LEMMA BallotLtIsLe == \A a, b \in Ballots: a \prec b => a \preceq b
BY DEF \preceq, \prec 
LEMMA NoBallotLowest == \A b \in ValidBallots: NoBallot \prec b
BY DEF \prec, NoBallot, ValidBallots 
LEMMA NoBallotNotHighest == \A b \in Ballots: ~ (b \prec NoBallot)
BY DEF \prec, NoBallot, ValidBallots 

LEMMA BallotTransLtLt == \A x,y,z \in Ballots: x \prec y /\ y \prec z => x \prec z
BY ProposersNat, SMT DEF \prec, NoBallot, ValidBallots
LEMMA BallotTransLeLe == \A x,y,z \in Ballots: x \preceq y /\ y \preceq z => x \preceq z
BY ProposersNat, SMT DEF \preceq, \prec, NoBallot, ValidBallots
LEMMA BallotTransLeLt == \A x,y,z \in Ballots: x \preceq y /\ y \prec z => x \prec z
BY ProposersNat, SMT DEF \prec, \preceq, NoBallot, ValidBallots
LEMMA BallotTransLtLe == \A x,y,z \in Ballots: x \prec y /\ y \preceq z => x \prec z
BY ProposersNat, SMT DEF \prec, \preceq, NoBallot, ValidBallots

LEMMA BallotLtNe == \A x,y \in Ballots: x \prec y => x # y
BY ProposersNat, SMT DEF \prec, NoBallot, ValidBallots
LEMMA BallotLeDef == \A a,b \in Ballots: a \preceq b <=> a \prec b \/ a = b 
BY ProposersNat DEF \preceq, \prec, ValidBallots

LEMMA BallotLtTrichotomy == \A a,b \in Ballots: a \prec b \/ a = b \/ b \prec a
BY BallotEq, ProposersNat, Z3 DEF \prec, ValidBallots, NoBallot
LEMMA BallotLtNeg ==  \A a,b \in Ballots: ~ (a \prec b) => a = b \/ b \prec a
BY BallotEq, ProposersNat, Z3 DEF \prec, ValidBallots, NoBallot
LEMMA BallotLtLtDisjoint == \A x,y \in Ballots : x \prec y /\ y \prec x => FALSE
BY ProposersNat, Z3 DEF \prec, ValidBallots, NoBallot
LEMMA BallotLeLtDisjoint == \A x,y \in Ballots : x \prec y /\ y \preceq x => FALSE
BY BallotLtLtDisjoint, BallotLtNe, BallotLeDef

LEMMA NoBallotNotInValidBallots == NoBallot \notin ValidBallots
BY DEFS NoBallot, ValidBallots
LEMMA BallotLeNegNoBallot == \A x,y \in Ballots: ~ (x \preceq y) => x # NoBallot
BY BallotLtTrichotomy, NoBallotNotHighest, BallotLeDef, Z3 DEF ValidBallots
LEMMA BallotLtNoBallot == \A x, y \in Ballots: x \prec y => y # NoBallot
BY DEFS \prec, NoBallot, ValidBallots 

THEOREM BallotLtProps ==
  /\ BallotLeRefl
  /\ BallotLtIsLe
  /\ NoBallotLowest
  /\ NoBallotNotHighest
  /\ BallotTransLtLt /\ BallotTransLtLe /\ BallotTransLeLt /\ BallotTransLeLe
  /\ BallotLtNe
  /\ BallotLeDef
  /\ BallotLtTrichotomy
  /\ BallotLtNeg /\ BallotLtLtDisjoint /\ BallotLeLtDisjoint /\ BallotLeLtDisjoint
  /\ BallotLeNegNoBallot /\ BallotLtNoBallot
BY BallotLeRefl, BallotLtIsLe, NoBallotLowest, NoBallotNotHighest,
  BallotTransLtLt, BallotTransLtLe, BallotTransLeLt, BallotTransLeLe, 
  BallotLtNe, BallotLeDef, BallotLtTrichotomy,
  BallotLtNeg, BallotLtLtDisjoint, BallotLeLtDisjoint, BallotLeLtDisjoint,
  BallotLeNegNoBallot, BallotLtNoBallot
USE DEF BallotLtProps

LEMMA NextBallotGtAll == \A b \in Ballots, p \in Proposers: b \prec nextBallot(b,p)
BY NoBallotNotInValidBallots DEF nextBallot, \prec, ValidBallots, NoBallot
LEMMA NextBallotInValidBallots == \A b \in Ballots, p \in Proposers: nextBallot(b,p) \in ValidBallots
BY DEF nextBallot, ValidBallots
LEMMA NextBallotProj1 == \A b \in ValidBallots, p \in Proposers: nextBallot(b,p)[1] = b[1] + 1 
BY NoBallotNotInValidBallots DEF nextBallot, ValidBallots
LEMMA NextBallotProj2 == \A b \in Ballots, p \in Proposers: nextBallot(b,p)[2] = p
BY DEF nextBallot, ValidBallots

THEOREM NextBallotProps ==
  /\ NextBallotGtAll
  /\ NextBallotInValidBallots
  /\ NextBallotProj1
  /\ NextBallotProj2
BY NextBallotGtAll, NextBallotInValidBallots, NextBallotProj1, NextBallotProj2
USE DEF NextBallotProps

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorems PSafeAtStable and ASafeAtStable show that (the invariant       *)
(* implies that) the predicate SafeAt(v, b) is stable, meaning that once   *)
(* it becomes true, it remains true throughout the rest of the execution.  *)
(***************************************************************************)

LEMMA PSafeAtStable == 
  ASSUME PNext 
  PROVE  \A v \in Values, b \in ValidBallots: SafeAt(v, b) => SafeAt(v, b)'
BY SMTT(10) DEF PNext, P1, P2, P3,
    Send, ValidBallots, SafeAt, DidntVoteIn, VotedForIn, 
    WontVoteIn, ParticipatedIn

LEMMA ASafeAtStable == 
  ASSUME AInv, ANext, ATypeOK'
  PROVE  \A v \in Values, b \in ValidBallots: SafeAt(v, b) => SafeAt(v, b)'
<1> USE DEF Send, AInv, ValidBallots
<1> SUFFICES ASSUME NEW v \in Values, NEW b \in ValidBallots,
                    SafeAt(v, b)
             PROVE  SafeAt(v, b)'
  BY Isa
<1>1. SUFFICES ASSUME NEW a \in Acceptors, A1(a) PROVE SafeAt(v, b)'
  BY DEF ANext
<1>2. PICK m \in msgs: A1(a)!2!(m)
  BY <1>1 DEF A1
<1>a. CASE A1(a)!2!(m)!1
  <2> SUFFICES ASSUME m.type = "1a",
                      IF aBal[a] \prec m.bal
                        THEN aBal' = [aBal EXCEPT ![a] = m.bal]
                        ELSE aBal' = aBal,
                      Send([type |-> "1b", from |-> a, to |-> m.from, bal |-> (aBal')[a], 
                            vbal |-> aVBal[a], vval |-> aVVal[a]]),
                      UNCHANGED <<aVBal, aVVal>> 
               PROVE  SafeAt(v, b)'
    BY <1>a DEF A1
  <2> \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
    BY NoValueNotAValue DEF A1, VotedForIn, WontVoteIn, ParticipatedIn
  <2> QED
    BY Z3 DEF A1, WontVoteIn, ParticipatedIn, SafeAt, DidntVoteIn
<1>b. CASE A1(a)!2!(m)!2
  <2>0. SUFFICES ASSUME m.type = "2a",
                        IF aBal[a] \preceq m.bal
                          THEN /\ aBal' = [aBal EXCEPT ![a] = m.bal]
                               /\ aVBal' = [aVBal EXCEPT ![a] = m.bal]
                               /\ aVVal' = [aVVal EXCEPT ![a] = m.val]
                               /\ Send([type |-> "2b", from |-> a, to |-> m.from, 
                                        bal |-> m.bal, val |-> m.val])
                          ELSE /\ Send([type |-> "2b", from |-> a, to |-> m.from, 
                                        bal |-> aBal[a], val |-> NoValue])
                               /\ UNCHANGED <<aBal, aVBal, aVVal>>,
                        NEW c \in ValidBallots, c \prec b
                 PROVE  SafeAt(v, b)!(c)'
    BY <1>b DEF A1, SafeAt
  <2>1. PICK Q \in Quorums : SafeAt(v, b)!(c)!2!(Q)
    BY <2>0, Zenon DEF SafeAt
  <2> SUFFICES ASSUME NEW a_1 \in Q 
               PROVE  \/ VotedForIn(a_1, v, c)' 
                      \/ DidntVoteIn(a_1, c)' /\ WontVoteIn(a_1, c)'
    BY <2>1 DEF SafeAt
  <2>a. CASE aBal[a] \preceq m.bal
    <3> /\ aBal' = [aBal EXCEPT ![a] = m.bal]
        /\ aVBal' = [aVBal EXCEPT ![a] = m.bal]
        /\ aVVal' = [aVVal EXCEPT ![a] = m.val]
        /\ Send([type |-> "2b", from |-> a, to |-> m.from, bal |-> m.bal, val |-> m.val])
        /\ c \prec b
      BY <2>0, <2>a
    <3>a. CASE VotedForIn(a_1, v, c) 
      BY <2>a, <3>a, NoValueNotAValue DEFS VotedForIn
    <3>b. CASE DidntVoteIn(a_1, c) /\ WontVoteIn(a_1, c)
      <4> WontVoteIn(a, m.bal) => m.bal \prec aBal[a]
        BY DEF ATypeOK, Messages, AStateInv
      <4> QED
        BY <2>a, <3>b, BallotLeLtDisjoint
        DEFS ATypeOK, DidntVoteIn, VotedForIn, WontVoteIn, ParticipatedIn
    <3> QED
      BY <3>a, <3>b, <2>1
  <2>b. CASE ~ (aBal[a] \preceq m.bal)
    <3>1. /\ Send([type |-> "2b", from |-> a, to |-> m.from,
                   bal |-> aBal[a], val |-> NoValue])
          /\ UNCHANGED <<aBal, aVBal, aVVal>>
      BY <2>0, <2>b  
    <3> /\ \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
        /\ \A aa, cc: WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
      BY <3>1, NoValueNotAValue DEF VotedForIn, WontVoteIn, ParticipatedIn
    <3> QED
      BY <2>b, NoValueNotAValue, <2>1, Z3 
      DEFS DidntVoteIn
  <2> QED
    BY <2>a, <2>b, Zenon
<1> QED
  BY <1>2, <1>a, <1>b DEF ANext
  
THEOREM SafeAtStable == 
  ASSUME Inv /\ Next /\ ATypeOK'
  PROVE  \A v \in Values, b \in ValidBallots: SafeAt(v, b) => SafeAt(v, b)'
BY PSafeAtStable, ASafeAtStable DEF Inv, Next, PNext, ANext, prop, acc

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorem: the predicate PInv is an inductive invariant in the proposer,  *)
(* assuming that the received messages satisfy AMsgInv.                    *)
(***************************************************************************)
THEOREM PInvariant == ASSUME AMsgInv PROVE PSpec => []PInv
<1> USE DEFS PInv, Send, ProcSet
<1>1. SInit /\ PInit => PInv
  <2> HAVE SInit /\ PInit
  <2> USE DEFS PInit, SInit
  <2>1. STypeOK
    BY DEF STypeOK, Messages 
  <2>2. PTypeOK
    BY DEF PTypeOK 
  <2>3. PMsgInv
    BY DEF PMsgInv
  <2>4. PStateInv
    BY QuorumNonEmpty, BallotLtProps, SMT DEF PStateInv
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF PInv
<1>2. PInv /\ [PNext]_(svars \o pvars) => PInv'
  <2> SUFFICES ASSUME PInv, PNext PROVE PInv'
    <3> CASE UNCHANGED (svars \o pvars)
      <4> /\ \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
          /\ \A aa, cc: WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
        BY DEF svars, pvars, VotedForIn, WontVoteIn, ParticipatedIn
      <4> USE DEFS svars, pvars, Messages, SafeAt, DidntVoteIn
      <4> QED
        BY Z3 DEFS STypeOK, PTypeOK, PMsgInv, PStateInv, Msg1bOK, Msg2bOK
    <3> QED
      OBVIOUS
  <2>1. STypeOK' /\ PTypeOK'
    <3> USE DEF STypeOK, PTypeOK, Messages
    <3>1. CASE \E p \in Proposers: P1(p)
      BY <3>1, NextBallotProps, SMT DEF P1, PTypeOK
    <3>2. CASE \E p \in Proposers: P2(p) /\ pQ1[p] \notin Quorums
      BY <3>2, Z3 DEFS P2
    <3>3. CASE \E p \in Proposers: P2(p) /\ pQ1[p] \in Quorums
      <4> SUFFICES ASSUME NEW p \in Proposers,
                          pc[p] = "P2",
                          pQ1[p] \in Quorums,
                          pQ2[p] = {}, 
                          pLBal[p] \prec pBal[p],
                          NEW v \in Values,
                          Send([type |-> "2a", from |-> p, bal |-> pBal[p], val |-> v]),
                          \/ pVBal[p] = NoBallot
                          \/ pVBal[p] \in ValidBallots /\ v = pVVal[p],
                          pLBal' = [pLBal EXCEPT ![p] = pBal[p]],
                          UNCHANGED <<pBal, pVBal, pVVal, pQ1, pQ2, pWr>>, 
                          pc' = [pc EXCEPT ![p] = "P3"]
                   PROVE  STypeOK' /\ PTypeOK'
        BY <3>3 DEF P2
      <4>a. CASE pVBal[p] = NoBallot
        BY <4>a, QuorumNonEmpty, SMT DEF PStateInv, Msg1bOK \* using pQ2[p] = {}
      <4>b. CASE pVBal[p] \in ValidBallots /\ v = pVVal[p]
        BY <4>b, Z3 DEFS PStateInv, PTypeOK
      <4> QED
        BY <4>a, <4>b
    <3>4. ASSUME NEW p \in Proposers, P3(p) PROVE <2>1
      <4> SUFFICES ASSUME P3(p)!2!2 PROVE <2>1
        BY <3>4 DEFS P3
      <4> PICK m \in msgs : P3(p)!2!2!1!(m)
        BY <3>4 DEFS P3
      <4> QED
        BY <3>4 DEFS P3
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4 DEF PNext
  <2>2. PMsgInv'
    <3> SUFFICES ASSUME NEW m \in msgs' PROVE PMsgInv!(m)!1'
      BY DEF PMsgInv
    <3>1. m.type \in {"1a","2a"} => m.from = m.bal[2]
      <4> HAVE m.type \in {"1a","2a"}
      <4>1. CASE \E p \in Proposers: P1(p)
        BY <4>1, BallotLtProps, NextBallotProps, Z3 
        DEF P1, PMsgInv, STypeOK, PTypeOK, Messages
      <4>2. CASE \E p \in Proposers: P2(p) /\ pQ1[p] \notin Quorums
        BY <4>2 DEF P2, PMsgInv, VotedForIn
      <4>3. CASE \E p \in Proposers: P2(p) /\ pQ1[p] \in Quorums
        <5>0. SUFFICES 
                ASSUME NEW p \in Proposers,
                       pQ1[p] \in Quorums, 
                       pQ2[p] = {},
                       NEW v \in Values,
                       pVBal[p] = NoBallot \/ (pVBal[p] \in ValidBallots /\ v = pVVal[p]),
                       Send([type |-> "2a", from |-> p, bal |-> pBal[p], val |-> v]),
                       UNCHANGED << pBal, pVBal, pVVal, pQ1, pQ2, pWr >>
                PROVE  <3>1!2
          BY <4>3, SMT DEF P2
        <5> DEFINE M == [type |-> "2a", from |-> p, bal |-> pBal[p], val |-> v]
        <5>a. CASE m \in msgs
          BY <5>a, SMT DEFS STypeOK, PTypeOK, Messages, PMsgInv
        <5>b. CASE m = M
          <6> SUFFICES m.from = pBal[p][2]
            BY <5>b, BallotLtProps, NextBallotProps, Z3 
            DEFS STypeOK, PTypeOK, Messages, PMsgInv
          <6> pBal[p] \in ValidBallots 
            BY <5>0, QuorumNonEmpty 
            DEFS STypeOK, PTypeOK, Messages, PStateInv \* using pQ2[p] = {}
          <6> QED
            BY <5>b DEFS STypeOK, PTypeOK, Messages, PStateInv
        <5> QED
          BY <5>0, <5>a, <5>b
      <4>4. CASE \E p \in Proposers: P3(p)
        BY <4>4 DEF P3, PMsgInv, VotedForIn
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3>a. m.type = "2a" => \A ma \in msgs' : ma.type = "2a" /\ ma.bal = m.bal => ma.val = m.val
      <4> HAVE m.type = "2a"
      <4> TAKE ma \in msgs'
      <4> HAVE ma.type = "2a" /\ ma.bal = m.bal 
      <4>1. CASE \E p \in Proposers: P1(p)
        <5> SUFFICES ASSUME NEW p \in Proposers, P1(p) PROVE ma.val = m.val
          BY <4>1, NextBallotProps, SMT DEF P1, PMsgInv, VotedForIn
        <5>a. pBal[p] \in ValidBallots => pBal[m.from][2]' = pBal[m.from][2]
          BY NextBallotProps, Z3 DEF P1, STypeOK, PTypeOK, Messages, PMsgInv, PStateInv
        <5>b. CASE pBal[p] = NoBallot
          BY <5>b, NextBallotProps, BallotLtProps, Z3 
          DEF P1, STypeOK, PTypeOK, Messages, PMsgInv, PStateInv \* by PS13
        <5> QED
          BY <5>a, <5>b DEF P1, PMsgInv, STypeOK, PTypeOK, Messages
      <4>2. CASE \E p \in Proposers: P2(p) /\ pQ1[p] \notin Quorums
        BY <4>2 DEF P2, PMsgInv, VotedForIn
      <4>3. CASE \E p \in Proposers: P2(p) /\ pQ1[p] \in Quorums
        <5>0. SUFFICES 
                ASSUME NEW p \in Proposers, 
                       pQ1[p] \in Quorums,
                       pLBal[p] \prec pBal[p],
                       NEW v \in Values,
                       pVBal[p] = NoBallot \/ (pVBal[p] \in ValidBallots /\ v = pVVal[p]),
                       Send([type |-> "2a", from |-> p, bal |-> pBal[p], val |-> v]),
                       pLBal' = [pLBal EXCEPT ![p] = pBal[p]],
                       UNCHANGED << pBal, pVBal, pVVal, pQ1, pQ2, pWr >>
                PROVE  ma.val = m.val 
          BY <4>3, SMT DEF P2
        <5> DEFINE M == [type |-> "2a", from |-> p, bal |-> pBal[p], val |-> v]
        <5>a. CASE m \in msgs /\ ma \in msgs
          <6> pBal[m.from][2]' = pBal[m.from][2]
            BY <5>0, Z3 DEFS STypeOK, PTypeOK, Messages, PMsgInv
          <6> QED
            BY <5>a, SMT DEFS STypeOK, PTypeOK, Messages, PMsgInv
        <5>b. CASE m = ma /\ ma = M
          BY <5>b, SMT DEFS STypeOK, PTypeOK, Messages, PMsgInv
        <5> ~ \E mm \in msgs : mm.type = "2a" /\ mm.from = p /\ mm.bal = pBal[p]
          <6> \A mm \in msgs : mm.type = "2a" /\ mm.from = p => mm.bal \preceq pLBal[p] 
            BY <5>0 DEF PStateInv \** by PS13
          <6> QED
            BY <5>0, BallotLtProps, Z3 DEFS STypeOK, PTypeOK, Messages, PStateInv \** by PStateInv!PS13(p)
        <5>c. CASE m \in msgs /\ ma = M
          <6> m.from = m.bal[2]
            BY <5>c DEFS PMsgInv
          <6> SUFFICES m.from = p
            BY <5>0, <5>c
          <6> QED
            BY <5>0, <5>c DEFS STypeOK, PTypeOK, Messages, PStateInv
        <5>d. CASE ma \in msgs /\ m = M
          <6> SUFFICES ma.from = p
            BY <5>0, <5>d
          <6> ma.from = ma.bal[2]
            BY <5>d DEFS PMsgInv
          <6> QED
            BY <5>0, <5>d DEFS STypeOK, PTypeOK, Messages, PStateInv
        <5> QED
          BY <5>0, <5>a, <5>b, <5>c, <5>d
      <4>4. CASE \E p \in Proposers: P3(p)
        BY <4>4 DEF P3, PMsgInv, VotedForIn
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3>b. m.type = "2a" => SafeAt(m.val, m.bal)'
      <4> HAVE m.type = "2a"
      <4>1. CASE \E p \in Proposers: P1(p)
        BY <4>1, <2>1, BallotLtProps, PSafeAtStable, Z3 
        DEFS P1, STypeOK, PTypeOK, Messages, PMsgInv, PStateInv
      <4>2. CASE \E p \in Proposers: P2(p) /\ pQ1[p] \notin Quorums
        BY <4>2, <2>1, PSafeAtStable DEF P2, STypeOK, Messages, PMsgInv
      <4>3. ASSUME NEW p \in Proposers, P2(p), pQ1[p] \in Quorums PROVE <3>b
        <5> /\ pQ1[p] \in Quorums
            /\ UNCHANGED <<pBal, pVBal, pVVal, pWr, pQ1, pQ2>>
            /\ pQ2[p] = {}   \* PStateInv!PS10(p)
          BY <4>3 DEF P2
        <5>1. PICK v \in Values :
                 /\ \/ pVBal[p] = NoBallot
                    \/ pVBal[p] \in ValidBallots /\ v = pVVal[p]
                 /\ Send([type |-> "2a", from |-> p, bal |-> pBal[p], val |-> v])
          BY <4>3 DEF P2, VotedForIn
        <5> SUFFICES SafeAt(m.val, m.bal)
          BY <5>1, <2>1, PSafeAtStable DEF STypeOK, PTypeOK, Messages, PMsgInv
        <5>s. PICK S \in SUBSET msgs : Msg1bOK(p, S)
          BY QuorumNonEmpty DEF PStateInv        
        <5>a. CASE m = [type |-> "2a", from |-> p, bal |-> pBal[p], val |-> v]
          <6> USE <5>a
          <6> SUFFICES ASSUME NEW c \in ValidBallots, c \prec pBal[p]
                       PROVE  \E Q \in Quorums :
                                \A a \in Q : \/ VotedForIn(a, v, c)
                                             \/ DidntVoteIn(a,c) /\ WontVoteIn(a, c)
            BY DEF SafeAt
          <6>a. CASE pVBal[p] = NoBallot
            <7> WITNESS pQ1[p] \in Quorums
            <7> TAKE a \in pQ1[p] 
            <7>m. PICK m1b \in S : m1b.from = a
              BY <5>s DEF Msg1bOK
            <7> USE <6>a
            <7>1. \A mm \in S : mm.vbal = NoBallot
              BY <7>m, <5>s DEF Msg1bOK
            <7>2. DidntVoteIn(a,c) /\ WontVoteIn(a, c)
              BY BallotLtProps DEF PStateInv, DidntVoteIn
            <7> QED
              BY <7>2
          <6>b. CASE pVBal[p] \in ValidBallots /\ v = pVVal[p]
            <7>0. pWr[p] = FALSE
              BY QuorumNonEmpty, <4>3 DEFS P2, PStateInv \* using pQ2[p] = {}
            <7>m. PICK m1bmax \in msgs :
                    /\ m1bmax.type = "1b"
                    /\ m1bmax.from \in pQ1[p]
                    /\ m1bmax.to = p
                    /\ m1bmax.bal = pBal[p]
                    /\ m1bmax.vbal = pVBal[p]
                    /\ m1bmax.vval = pVVal[p]
              BY <5>s, <6>b, <7>0, QuorumNonEmpty, BallotLtProps, SMT DEF Msg1bOK, PStateInv
            <7>1. VotedForIn(m1bmax.from, v, pVBal[p])
              BY <5>s, <6>b, <7>m, BallotLtProps DEF AMsgInv, Msg1bOK
            <7> HIDE DEF VotedForIn, PMsgInv
            <7>2. pVBal[p] \in ValidBallots 
              BY <5>1, <6>b, QuorumNonEmpty DEF PStateInv
            <7> pQ1[p] \in SUBSET Acceptors
              BY QuorumAssumption1 
            <7>a. CASE c \prec pVBal[p]
              (*************************************************************)
              (* Value v is safe at these ballots, by induction of SafeAt. *)
              (*************************************************************)
              <8>x. \A a_1 \in Acceptors :
                      VotedForIn(a_1, v, pVBal[p]) => SafeAt(v, pVBal[p])
                BY <6>b, VotedInv DEF STypeOK, PTypeOK, Messages
              <8> SafeAt(v, pVBal[p])
                BY <6>b, <7>m, <7>1, <8>x
              <8> QED
                BY <7>a, <6>b, BallotLtProps DEF SafeAt, DidntVoteIn
            <7>b. CASE c = pVBal[p]
              (*************************************************************)
              (* Acceptor m1bmax.from voted for v in ballot c.  For those  *)
              (* acceptors in pQ1[p] that voted in c, they must have voted *)
              (* for the same value v, by VotedOnce.  Those that did not   *)
              (* vote, it is because they are participating in a ballot    *)
              (* greater than c.  The acceptors in pQ1[p] form a majority, *)
              (* so it is safe to select v as the value for the second     *)
              (* phase.                                                    *)
              (*************************************************************)
              <8>1. VotedForIn(m1bmax.from, v, c)
                BY <7>1, <7>b
              <8>2. \A q \in pQ1[p], w \in Values : VotedForIn(q, w, c) => w = v
                BY <8>1, VotedOnce, <7>m 
              <8> m1bmax.from \in Acceptors
                BY <7>m, QuorumAssumption1
              <8> WITNESS pQ1[p] \in Quorums
              <8> TAKE a \in pQ1[p] 
              <8>3. /\ pBal[p] \in ValidBallots 
                    /\ \E SS \in SUBSET msgs: Msg1bOK(p,SS)
                <9> pBal[p] # NoBallot 
                  BY BallotLtProps DEF PStateInv, STypeOK, Messages
                <9> QED
                  BY PStateInv!PS5(p) DEF PStateInv \* using pQ2[p] = {}
              <8> QED
                BY <7>b, <8>1, <8>2, <8>3, BallotLtProps, Z3 
                DEFS Msg1bOK, DidntVoteIn, WontVoteIn, ParticipatedIn
            <7>c. CASE pVBal[p] \prec c /\ c \prec pBal[p]
              BY <5>1, <7>c DEF PStateInv 
            <7> QED
              BY <7>a, <7>b, <7>c, BallotLtProps DEF PTypeOK
          <6> QED
            BY <6>a, <6>b, <5>1
        <5>b. CASE m \in msgs
          BY <5>b, Z3 DEF PMsgInv, SafeAt
        <5> QED
          BY <5>a, <5>b, <5>1
      <4>4. ASSUME NEW p \in Proposers, P3(p) PROVE <3>b
        BY <4>4, <2>1, PSafeAtStable DEF P3, STypeOK, PTypeOK, Messages, PMsgInv
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext   
    <3> SUFFICES ASSUME m.type = "2a", m.from = pBal[m.from][2]' PROVE PMsgInv!(m)!1!2'
      BY <3>1, <3>a, <3>b DEF PMsgInv
    <3>c. m.bal = pBal[m.from]' => pQ1[m.from]' \in Quorums
      <4> HAVE m.bal = pBal[m.from]'
      <4>1. ASSUME NEW p \in Proposers, P1(p) PROVE <3>c!2
        <5>a. CASE p = m.from
          <6> ~ \E mm \in msgs: mm.type \in {"1a","2a"} /\ mm.from = p /\ nextBallot(pBal[p], p) \preceq mm.bal
            BY BallotLtProps, NextBallotProps, Z3 
            DEFS PTypeOK, STypeOK, Messages, PStateInv
          <6>a. CASE pBal[p] = NoBallot \* p was not preempted
            <7> USE <5>a, <6>a
            <7> SUFFICES ASSUME m \in msgs, m.bal = nextBallot(pBal[p],p) PROVE FALSE
              BY <4>1, QuorumNonEmpty, SMT DEFS P1, STypeOK, PTypeOK, Messages
            <7> QED
              BY <4>1, BallotLtProps, NextBallotProps, Z3 
              DEFS P1, STypeOK, Messages, PTypeOK, PStateInv
          <6>b. CASE pBal[p] # NoBallot \* p was preempted
            <7> USE <5>a, <6>b
            <7> SUFFICES ASSUME m \in msgs, m.bal = nextBallot(pBal[p],p) PROVE FALSE
              BY <4>1 DEFS P1, STypeOK, PTypeOK, Messages
            <7> QED
              BY <4>1, BallotLtProps, NextBallotProps, Z3 
              DEFS P1, STypeOK, Messages, PTypeOK, PStateInv
          <6> QED
            BY <6>a, <6>b
        <5>b. CASE p # m.from
          BY <4>1, <5>b DEFS P1, STypeOK, PTypeOK, Messages, PMsgInv
        <5> QED
          BY <5>a, <5>b
      <4>2. CASE \E p \in Proposers: P2(p) /\ pQ1[p] \notin Quorums
        BY <4>2 DEFS P2, STypeOK, PTypeOK, Messages, PMsgInv
      <4>3. CASE \E p \in Proposers: P2(p) /\ pQ1[p] \in Quorums
        BY <4>3 DEFS P2, STypeOK, PTypeOK, Messages, PMsgInv, PStateInv
      <4>4. CASE \E p \in Proposers: P3(p)
        <5> SUFFICES ASSUME NEW p \in Proposers,
                            pQ2[p] \notin Quorums,
                            NEW m_1 \in msgs, P3(p)!2!2!1!(m_1),
                            UNCHANGED <<msgs, pBal, pQ1>>
                     PROVE  <3>c!2
          BY <4>4 DEF P3, PMsgInv
        <5>a. CASE p = m.from
          BY <5>a, QuorumNonEmpty
          DEFS P3, STypeOK, PTypeOK, Messages, PStateInv, PMsgInv
        <5>b. CASE p # m.from
          BY <5>b DEFS P3, STypeOK, PTypeOK, Messages, PMsgInv
        <5> QED
          BY <5>a, <5>b
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext  
    <3>d. m.bal = pBal[m.from]' /\ pVBal[m.from]' \in ValidBallots /\ pQ2[m.from]' \notin Quorums 
          => m.val = pVVal[m.from]'
      <4> HAVE /\ m.bal = pBal[m.from]' /\ pVBal[m.from]' \in ValidBallots 
               /\ pQ2[m.from]' \notin Quorums 
      <4>1. ASSUME NEW p \in Proposers, P1(p) PROVE m.val = pVVal[m.from]'
        BY <4>1, BallotLtProps DEF P1, PMsgInv, STypeOK, PTypeOK, Messages, PStateInv
      <4>2. ASSUME NEW p \in Proposers, P2(p), pQ1[p] \notin Quorums PROVE m.val = pVVal[m.from]'
        <5> SUFFICES ASSUME pQ1[p] \notin Quorums,
                            NEW m_1 \in msgs, P2(p)!2!2!1!(m_1),
                            UNCHANGED <<msgs, pBal, pWr, pQ2>>
                     PROVE m.val = pVVal[m.from]'
          BY <4>2 DEFS P2, PMsgInv
        <5>a. CASE pVBal[p] \prec m_1.vbal
          <6>a. CASE p = m.from
            <7> SUFFICES ASSUME m.bal = pBal[p],
                                pQ1[p] \cup {m_1.from} \in Quorums,
                                pQ2[p] \notin Quorums,
                                m_1.vbal \in ValidBallots
                         PROVE m.val = m_1.vval
              BY <5>a, <6>a, SMT DEFS STypeOK, PTypeOK, Messages, PMsgInv
            <7> QED
              BY <5>a, <6>a, QuorumNonEmpty, Z3
              DEFS STypeOK, PTypeOK, Messages, PMsgInv, PStateInv
          <6>b. CASE p # m.from
            BY <5>a, <6>b, SMT DEFS STypeOK, PTypeOK, Messages, PMsgInv
          <6> QED
            BY <6>a, <6>b
        <5>b. CASE ~ (pVBal[p] \prec m_1.vbal)
          BY <5>b, SMT DEFS STypeOK, PTypeOK, Messages, PMsgInv
        <5> QED
          BY <5>a, <5>b
      <4>3. ASSUME NEW p \in Proposers, P2(p), pQ1[p] \in Quorums PROVE m.val = pVVal[m.from]'
        BY <4>3, BallotLtProps DEF P2, PMsgInv
      <4>4. ASSUME NEW p \in Proposers, P3(p) PROVE m.val = pVVal[m.from]'
        <5> SUFFICES ASSUME pQ2[p] \notin Quorums,
                            NEW m_1 \in msgs, 
                            m_1.type = "2b",
                            m_1.to = p,
                            m_1.from \notin pQ2[p],
                            m_1.val \in Values,
                            \*P3(p)!2!2!1!(m_1),
                            pQ2' = [pQ2 EXCEPT ![p] = pQ2[p] \cup {m_1.from}],
                            pVBal' = [pVBal EXCEPT ![p] = m_1.bal],
                            pVVal' = [pVVal EXCEPT ![p] = m_1.val],
                            UNCHANGED <<msgs, pBal, pQ1>>,
                            m_1.bal = pBal[p]
                     PROVE  m.val = pVVal[m.from]'
          BY <4>4, SMT DEF P3, PMsgInv, STypeOK, PTypeOK, Messages
        <5> QED
          BY SMT DEF PMsgInv, STypeOK, PTypeOK, Messages, AMsgInv
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3> QED
      BY <3>c, <3>d
  <2>3. PStateInv'
    <3> SUFFICES ASSUME NEW p \in Proposers PROVE PStateInv!(p)'
      BY DEF PStateInv
    <3> USE DEF PStateInv
    <3>1. pVBal[p]' = NoBallot <=> pVVal[p]' = NoValue
      <4>1. ASSUME NEW p_1 \in Proposers, P1(p_1) PROVE <3>1
        BY <4>1, NoValueNotAValue DEF P1, AMsgInv, STypeOK, PTypeOK, Messages
      <4>2. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \notin Quorums PROVE <3>1
        BY <4>2, NoValueNotAValue, NoBallotNotInValidBallots
        DEFS P2, AMsgInv, STypeOK, PTypeOK, Messages
      <4>3. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \in Quorums PROVE <3>1
        BY <4>3 DEF P2
      <4>4. ASSUME NEW p_1 \in Proposers, P3(p_1) PROVE <3>1
        BY <4>4, NoValueNotAValue, BallotLtProps 
        DEFS P3, AMsgInv, STypeOK, PTypeOK, Messages
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3>2. pVBal[p]' \preceq pBal[p]'
      <4>1. ASSUME NEW p_1 \in Proposers, P1(p_1) PROVE <3>2
        BY <4>1, BallotLtProps, NextBallotProps, Z3
        DEFS P1, AMsgInv, STypeOK, PTypeOK, Messages
      <4>2. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \notin Quorums PROVE <3>2
        BY <4>2, NoValueNotAValue DEF P2, AMsgInv, STypeOK, PTypeOK, Messages
      <4>3. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \in Quorums PROVE <3>2
        BY <4>3 DEF P2
      <4>4. ASSUME NEW p_1 \in Proposers, P3(p_1) PROVE <3>2
        BY <4>4, NoValueNotAValue, BallotLtProps 
        DEFS P3, AMsgInv, STypeOK, PTypeOK, Messages
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3>3. pVBal[p]' \in ValidBallots => pBal[p]' \in ValidBallots
      <4>1. ASSUME NEW p_1 \in Proposers, P1(p_1) PROVE <3>3
        BY <4>1, NoValueNotAValue, BallotLtProps 
        DEFS P1, AMsgInv, STypeOK, PTypeOK, Messages
      <4>2. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \notin Quorums PROVE <3>3
        BY <4>2, NoValueNotAValue DEF P2, AMsgInv, STypeOK, PTypeOK, Messages
      <4>3. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \in Quorums PROVE <3>3
        BY <4>3 DEF P2
      <4>4. ASSUME NEW p_1 \in Proposers, P3(p_1) PROVE <3>3
        BY <4>4, NoValueNotAValue, BallotLtProps 
        DEFS P3, AMsgInv, STypeOK, PTypeOK, Messages
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3>4. pQ1[p]' = {} => pVBal[p]' = NoBallot /\ pVVal[p]' = NoValue
      (*********************************************************************)
      (* pQ1[p] = {} only at init.                                         *)
      (*********************************************************************)
      <4>1. ASSUME NEW p_1 \in Proposers, P1(p_1) PROVE <3>4
        <5>a. CASE p = p_1
          BY <5>a, <4>1, QuorumNonEmpty, SMT 
          DEFS P1, STypeOK, PTypeOK, Messages, PStateInv
        <5>b. CASE p # p_1
          BY <5>b, <4>1 DEF P1, STypeOK, PTypeOK, Messages
        <5> QED
          BY <5>a, <5>b
      <4>2. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \notin Quorums PROVE <3>4
        BY <4>2, NoValueNotAValue, Z3 DEF P2, STypeOK, PTypeOK, Messages
      <4>3. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \in Quorums PROVE <3>4
        BY <4>3 DEF P2
      <4>4. ASSUME NEW p_1 \in Proposers, P3(p_1) PROVE <3>4
        <5> SUFFICES ASSUME pQ2[p_1] \notin Quorums,
                            NEW m \in msgs, 
                            m.type = "2b", m.to = p_1, 
                            m.from \notin pQ2[p_1], m.val \in Values, 
                            P3(p_1)!2!2!1!(m),
                            UNCHANGED <<msgs, pBal, pQ1>>
                     PROVE  <3>4
          BY <4>4, Zenon DEF P3
        <5> HAVE pQ1[p]' = {}
        <5>a. CASE pQ2[p_1] \cup {m.from} \in Quorums
          <6> SUFFICES ASSUME pQ1[p] = {} PROVE <3>4
            BY <5>a, SMT DEFS STypeOK, PTypeOK, Messages
          <6> PICK m2a \in msgs :
                   /\ m2a.type = "2a"
                   /\ m2a.from = m.to
                   /\ m2a.bal = m.bal
                   /\ m2a.val = m.val
            BY SMT DEFS STypeOK, PTypeOK, Messages, AMsgInv
          <6>a. CASE p = p_1
            BY <5>a, <6>a, QuorumNonEmpty, SMT DEFS STypeOK, PTypeOK, Messages, PMsgInv
          <6>b. CASE p # p_1
            <7> m2a.bal = pBal[p_1] => pQ1[p_1] \in Quorums \* by PM3 
              BY SMT DEFS STypeOK, PTypeOK, Messages, PMsgInv
            <7> QED
              BY <5>a, <6>b, QuorumNonEmpty, SMT DEFS STypeOK, PTypeOK, Messages
          <6> QED
            BY <6>a, <6>b
        <5> QED
          BY <5>a, QuorumNonEmpty, SMT DEFS STypeOK, PTypeOK, Messages, PMsgInv, AMsgInv
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext                           
    <3>5. pQ1[p]' # {} /\ pQ2[p]' = {} => pBal[p]' \in ValidBallots /\ \E S \in SUBSET msgs': Msg1bOK(p,S)'
      <4> HAVE pQ1[p]' # {} /\ pQ2[p]' = {}
      <4> USE DEF Send, ValidBallots, Msg1bOK
      <4>1. ASSUME NEW p_1 \in Proposers, P1(p_1) PROVE <3>5!2
        BY <4>1, Z3 DEF P1, STypeOK, PTypeOK, Messages
      <4>2. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \notin Quorums PROVE <3>5!2
        <5> HIDE DEF Msg1bOK
        <5> SUFFICES ASSUME pQ1[p_1] \notin Quorums,
                            NEW m \in msgs, 
                            m.type = "1b", m.to = p_1, m.from \notin pQ1[p_1],
                            P2(p_1)!2!2!1!(m),
                            UNCHANGED <<msgs, pBal, pWr, pQ2>>
                     PROVE  <3>5!2
          BY <4>2 DEF P2, Msg1bOK
        <5>a. CASE m.bal = pBal[p_1] /\ pVBal[p_1] \prec m.vbal
          <6>1. /\ pVBal' = [pVBal EXCEPT ![p_1] = m.vbal]
                /\ pVVal' = [pVVal EXCEPT ![p_1] = m.vval]
            BY <5>a
          <6> USE <5>a, <6>1
          <6>x. m.vbal # NoBallot
            BY BallotLtNoBallot DEF Msg1bOK, PTypeOK, STypeOK, Messages
          <6>a. CASE p = p_1
            <7> USE <6>a
            <7> SUFFICES \E S \in SUBSET msgs: Msg1bOK(p,S)'
              BY QuorumNonEmpty DEF PTypeOK, STypeOK, Messages
            <7>a. CASE pQ1[p] = {}
              <8> ~ \E mm \in msgs: mm.type = "1b" /\ mm.from \in pQ1[p] /\ 
                                    mm.to = p /\ mm.bal = pBal[p]
                BY <7>a DEF PStateInv
              <8> PICK SS \in SUBSET msgs : SS = {m}
                BY Isa
              <8> Msg1bOK(p,SS)'
                BY <6>x, BallotLeDef DEF Msg1bOK, PTypeOK, STypeOK, Messages
              <8> QED
                OBVIOUS
            <7>b. CASE pQ1[p] # {}
              <8> PICK S \in SUBSET msgs: Msg1bOK(p,S)
                BY <7>b
              <8> PICK SS \in SUBSET msgs : SS = S \cup {m}
                BY Isa
              <8> Msg1bOK(p,SS)'
                BY BallotLtProps, Z3 DEF Msg1bOK, PTypeOK, STypeOK, Messages
              <8> QED
                OBVIOUS
            <7> QED
              BY <7>a, <7>b
          <6>b. CASE p # p_1
            BY <6>b, Z3 DEF Msg1bOK, PTypeOK, STypeOK, Messages
          <6> QED
            BY <6>a, <6>b        
        <5>b. CASE m.bal = pBal[p_1] /\ ~ (pVBal[p_1] \prec m.vbal)
          <6>1. UNCHANGED <<pVBal, pVVal>>
            BY <5>b, <4>2 DEF P2
          <6> USE <6>1
          <6>a. CASE p = p_1
            <7> USE <6>a
            <7> SUFFICES \E S \in SUBSET msgs: Msg1bOK(p,S)'
              BY QuorumNonEmpty DEF PTypeOK, STypeOK, Messages
            <7>a. CASE pQ1[p] = {}
              <8> ~ \E mm \in msgs: mm.type = "1b" /\ mm.from \in pQ1[p] /\ 
                                    mm.to = p /\ mm.bal = pBal[p]
                BY <7>a DEF PStateInv
              <8> PICK SS \in SUBSET msgs : SS = {m}
                BY Isa
              <8> Msg1bOK(p,SS)'
                BY BallotLtProps, SMT DEF Msg1bOK, PTypeOK, STypeOK, Messages
              <8> QED
                BY SMT
            <7>b. CASE pQ1[p] # {}
              <8> PICK S \in SUBSET msgs: Msg1bOK(p,S)
                BY <7>b
              <8> PICK SS \in SUBSET msgs : SS = S \cup {m}
                BY Isa
              <8> Msg1bOK(p,SS)'
                BY <5>b, BallotLtProps, SMT DEF Msg1bOK, PTypeOK, STypeOK, Messages                
              <8> QED
                BY SMT
            <7> QED
              BY <7>a, <7>b
          <6>b. CASE p # p_1
            <7>a. CASE pQ1[p] = {}
              <8> pBal[p] \in ValidBallots
                BY <6>b, <7>a, QuorumNonEmpty DEFS PTypeOK, STypeOK, Messages
              <8> QED
                BY <6>b, <7>a, SMTT(10) DEFS PTypeOK, STypeOK, Messages, Msg1bOK
            <7>b. CASE pQ1[p] # {}
              <8> pBal[p] \in ValidBallots
                BY <6>b, <7>b, QuorumNonEmpty DEFS PTypeOK, STypeOK, Messages
              <8> QED
                BY <6>b, <7>b, Z3T(10) DEFS PTypeOK, STypeOK, Messages, Msg1bOK
            <7> QED
              BY <7>a, <7>b
          <6> QED
            BY <6>a, <6>b
        <5>c. CASE m.bal # pBal[p_1]
          BY <5>c, BallotLtProps, Z3 DEF Msg1bOK, PTypeOK, STypeOK, Messages
        <5> QED
          BY <5>a, <5>b, <5>c DEF PTypeOK, STypeOK, Messages
      <4>3. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \in Quorums PROVE <3>5!2
        BY <4>3 DEF P2
      <4>4. ASSUME NEW p_1 \in Proposers, P3(p_1), pQ2[p_1] \notin Quorums PROVE <3>5!2
        <5> SUFFICES ASSUME pQ2[p_1] \notin Quorums,
                            NEW m \in msgs, 
                            m.type = "2b", m.to = p_1, 
                            m.from \notin pQ2[p_1], m.val \in Values, 
                            P3(p_1)!2!2!1!(m),
                            UNCHANGED <<msgs, pBal, pQ1>>
                     PROVE  <3>5!2
          BY <4>4, SMT DEF P3, Msg1bOK
        <5> QED
          BY NoValueNotAValue, BallotLtProps, QuorumNonEmpty, Z3 
          DEFS AMsgInv, PTypeOK, STypeOK, Messages
      <4>5. ASSUME NEW p_1 \in Proposers, P3(p_1), pQ2[p_1] \in Quorums PROVE <3>5!2
        BY <4>5, QuorumNonEmpty, Z3 
        DEFS P3, Msg1bOK, AMsgInv, PTypeOK, STypeOK, Messages
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF PNext
    <3>6. pQ2[p]' # {} => pVBal[p]' = pBal[p]' /\ \E S \in SUBSET msgs': Msg2bOK(p,S)'
      <4> HAVE pQ2[p]' # {}
      <4> USE DEF Send, ValidBallots, Msg2bOK
      <4>1. ASSUME NEW p_1 \in Proposers, P1(p_1) PROVE <3>6!2
        BY <4>1, SMT DEF P1, PTypeOK, STypeOK, Messages, VotedForIn
      <4>2. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \notin Quorums PROVE <3>6!2
        <5> \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
          BY <4>2 DEF P2, VotedForIn
        <5> QED
          BY <4>2, QuorumNonEmpty, SMT DEF P2, PTypeOK, STypeOK, Messages
      <4>3. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \in Quorums PROVE <3>6!2
        <5> \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
          BY <4>3 DEF P2, VotedForIn
        <5> QED
          BY <4>3 DEF P2
      <4>4. ASSUME NEW p_1 \in Proposers, P3(p_1) PROVE <3>6!2
        <5> SUFFICES ASSUME pQ2[p_1] \notin Quorums,
                            NEW m \in msgs, m.type = "2b", m.to = p_1, 
                            m.from \notin pQ2[p_1], m.val \in Values, 
                            P3(p_1)!2!2!1!(m),
                            UNCHANGED <<msgs, pBal, pQ1>>
                     PROVE  <3>6!2
          BY <4>4, SMT DEF P3, PMsgInv
        <5> \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
          BY SMT DEF VotedForIn        
        <5>a. CASE p = p_1
          <6> USE <5>a
          <6> PICK S \in SUBSET msgs: Msg2bOK(p,S)
            BY SMT
          <6>a. CASE m.bal = pBal[p_1]
            <7> PICK SS \in SUBSET msgs : SS = S \cup {m}
              BY Isa
            <7> Msg2bOK(p,SS)'
              BY <6>a, SMT DEF PTypeOK, STypeOK, Messages 
            <7> QED
              BY SMT
          <6>b. CASE m.bal # pBal[p_1]
            BY <6>b, SMT DEF PTypeOK, STypeOK, Messages
          <6> QED
            BY <6>a, <6>b
        <5>b. CASE p # p_1
          BY <5>b DEF Msg1bOK, PTypeOK, STypeOK, Messages
        <5> QED
          BY <5>a, <5>b
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext 
    <3>7. pVBal[p]' \in ValidBallots => \A a \in pQ2[p]' : VotedForIn(a, pVVal[p], pBal[p])'
      <4> HAVE pVBal[p]' \in ValidBallots
      <4> TAKE aa \in pQ2[p]'
      <4>1. ASSUME NEW p_1 \in Proposers, P1(p_1) PROVE VotedForIn(aa, pVVal[p], pBal[p])'
        BY <4>1 DEF P1, VotedForIn, PTypeOK, STypeOK
      <4>2. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \notin Quorums PROVE VotedForIn(aa, pVVal[p], pBal[p])'
        <5>1. \A a, vv, cc: VotedForIn(a, vv, cc)' <=> VotedForIn(a, vv, cc)
          BY <4>2 DEF P2, VotedForIn
        <5> SUFFICES ASSUME pQ1[p_1] \notin Quorums,
                            NEW m \in msgs, P2(p_1)!2!2!1!(m),
                            UNCHANGED <<msgs, pBal, pWr, pQ2>>
                     PROVE  VotedForIn(aa, pVVal[p]', pBal[p]')
          BY <4>2, <5>1 DEF P2
        <5>a. CASE p # p_1
          BY <5>a, NoValueNotAValue DEF AMsgInv, PTypeOK, STypeOK, Messages
        <5>b. CASE p = p_1
          <6> pQ1[p] \in Quorums
            BY <5>b, ExistsQuorum1
          <6> QED \* by contradiction with pQ1[p_1] \notin Quorums
            BY <5>b, Zenon
        <5> QED
          BY <5>a, <5>b
      <4>3. ASSUME NEW p_1 \in Proposers, P2(p_1), pQ1[p_1] \in Quorums PROVE VotedForIn(aa, pVVal[p], pBal[p])'
        BY <4>3 DEF P2, VotedForIn
      <4>4. ASSUME NEW p_1 \in Proposers, P3(p_1) PROVE VotedForIn(aa, pVVal[p], pBal[p])'
        <5>1. \A a, vv, cc: VotedForIn(a, vv, cc)' <=> VotedForIn(a, vv, cc)
          BY <4>4 DEF P3, VotedForIn
        <5> SUFFICES ASSUME pQ2[p_1] \notin Quorums,
                            NEW m \in msgs, 
                            m.type = "2b", m.to = p_1, 
                            m.from \notin pQ2[p_1], m.val \in Values,
                            pQ2' = [pQ2 EXCEPT ![p_1] = pQ2[p_1] \cup {m.from}],
                            pVBal' = [pVBal EXCEPT ![p_1] = m.bal],
                            pVVal' = [pVVal EXCEPT ![p_1] = m.val],
                            UNCHANGED <<msgs, pBal, pQ1>>,
                            m.bal = pBal[p_1],
                            p = p_1
                     PROVE  VotedForIn(aa, pVVal[p]', pBal[p]')
          BY <4>4, <5>1, SMT DEF P3, PTypeOK, STypeOK, Messages
        <5>a. CASE (pQ2')[p_1] \in Quorums
          <6> SUFFICES ASSUME m.bal \in ValidBallots,
                              aa \in pQ2[p] \cup {m.from}
                       PROVE  VotedForIn(aa, m.val, pBal[p])
              BY <5>a, SMT DEF PTypeOK, STypeOK, Messages
          <6>a. CASE pQ2[p] # {}
            <8>2. PICK S \in SUBSET msgs : Msg2bOK(p, S)
              BY <6>a, Zenon
            <8>3. PICK M \in msgs : /\ M.type = "2b" /\ M.from = aa /\ M.to = p 
                                    /\ M.bal = pBal[p] /\ M.val \in Values
              BY <8>2 DEF Msg2bOK
            <8> PICK m2a \in msgs: /\ m2a.type = "2a"
                                   /\ m2a.from = p
                                   /\ m2a.bal  = M.bal
                                   /\ m2a.val  = M.val
              BY <8>3 DEF AMsgInv
            <8>4. VotedForIn(m.from, m.val, pBal[p])
              BY <5>a DEF VotedForIn
            <8>5. VotedForIn(aa, m2a.val, pBal[p])
              BY <8>3, Z3 DEF VotedForIn
            <8> QED
              BY <8>4, <8>5, VotedOnce, Z3 DEF PTypeOK, STypeOK, Messages
          <6>b. CASE pQ2[p] = {}
            BY <6>b, QuorumNonEmpty, SMT 
            DEFS Msg2bOK, AMsgInv, VotedForIn, PTypeOK, STypeOK, Messages
          <6> QED
            BY <6>a, <6>b
        <5>b. CASE ~ ((pQ2')[p_1] \in Quorums)
          <6> SUFFICES ASSUME pBal[p] \in ValidBallots,
                              aa \in pQ2[p] \cup {m.from}
                       PROVE  VotedForIn(aa, m.val, pBal[p])
            BY <5>b, SMT DEF PTypeOK, STypeOK, Messages
          <6>a. CASE pQ2[p] # {}
            <8>2. PICK S \in SUBSET msgs : Msg2bOK(p, S)
              BY <6>a, Zenon
            <8>3. PICK M \in msgs : /\ M.type = "2b" /\ M.from = aa /\ M.to = p 
                                    /\ M.bal = pBal[p] /\ M.val \in Values
              BY <8>2 DEF Msg2bOK
            <8> PICK m2a \in msgs: /\ m2a.type = "2a"
                                   /\ m2a.from = p
                                   /\ m2a.bal  = pBal[p]
                                   /\ m2a.val  = M.val
              BY <8>3 DEF AMsgInv
            <8>4. VotedForIn(m.from, m.val, pBal[p])
              BY <5>b DEF VotedForIn
            <8>5. VotedForIn(aa, m2a.val, pBal[p])
              BY <8>3, Z3 DEF VotedForIn
            <8>6. m.val = m2a.val
              BY <8>4, <8>5, VotedOnce, Z3 DEF PTypeOK, STypeOK, Messages
            <8>7. pQ1[p] \in Quorums
              BY <6>a, ExistsQuorum1 DEF PStateInv
            <8>8. pVBal[p] \in ValidBallots
              BY <6>a DEF PMsgInv, PTypeOK, STypeOK, Messages
            <8> pQ2[p_1] \notin Quorums => m2a.val = pVVal[p]
              BY <5>a, <8>7, <8>8 DEF PMsgInv \* by PM4
            <8> QED
              BY <8>4, <8>5, <8>6, SMT DEF PTypeOK, STypeOK, Messages
          <6>b. CASE pQ2[p] = {}
            <8> PICK m2a \in msgs: /\ m2a.type = "2a"
                                   /\ m2a.from = m.to
                                     /\ m2a.bal  = pBal[p]
                                   /\ m2a.val  = m.val
              BY <6>b, SMT DEFS AMsgInv 
            <8> m2a.bal = pBal[p] /\ pWr[p] = FALSE /\ pVBal[p] \in ValidBallots 
                  => m2a.val = pVVal[p]
              BY DEF PMsgInv \* by PM4
            <8> QED
              BY <6>b, QuorumNonEmpty, SMT 
              DEFS Msg2bOK, AMsgInv, VotedForIn, PTypeOK, STypeOK, Messages
          <6> QED
            BY <6>a, <6>b
        <5> QED
          BY <5>a, <5>b
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3>8. pWr[p]' => pQ1[p]' \in Quorums /\ pQ2[p]' \in Quorums /\ pVBal[p]' = pBal[p]'
      <4> HAVE pWr[p]'  
      <4> USE DEF Send, ValidBallots
      <4>1. CASE \E p_1 \in Proposers: P1(p_1)
        <5> SUFFICES ASSUME NEW p_1 \in Proposers,
                            pWr[p_1] = FALSE,
                            pVBal' = [pVBal EXCEPT ![p_1] = NoBallot],
                            pVVal' = [pVVal EXCEPT ![p_1] = NoValue],
                            pQ1' = [pQ1 EXCEPT ![p_1] = {}],
                            pQ2' = [pQ2 EXCEPT ![p_1] = {}],
                            pBal' = [pBal EXCEPT ![p_1] = nextBallot(pBal[p_1],p_1)],
                            Send([type |-> "1a", from |-> p_1, bal |-> pBal'[p_1]]),
                            UNCHANGED pWr
                     PROVE  <3>8!2
          BY <4>1, SMT DEF P1
        <5> pQ1[p] \in Quorums /\ pQ2[p] \in Quorums /\ pVBal[p] = pBal[p]
          BY DEFS PTypeOK, STypeOK, Messages
        <5>a. CASE p = p_1 \* By contradiction.
          BY <5>a, QuorumNonEmpty, SMT 
          DEFS VotedForIn, PTypeOK, STypeOK, Messages, AMsgInv
        <5>b. CASE p # p_1
          BY <5>b, SMT DEFS PTypeOK, STypeOK, Messages
        <5> QED
          BY QuorumNonEmpty, SMT 
          DEFS VotedForIn, PTypeOK, STypeOK, Messages, AMsgInv
      <4>2. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \notin Quorums
        BY <4>2 DEF P2, VotedForIn, PTypeOK, STypeOK, Messages, AMsgInv
      <4>3. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \in Quorums
        BY <4>3 DEF P2, VotedForIn
      <4>4. CASE \E p_1 \in Proposers: P3(p_1) /\ pQ2[p_1] \notin Quorums
        <5> SUFFICES ASSUME pQ2[p] \notin Quorums,
                            NEW m \in msgs, 
                            m.type = "2b", m.to = p, 
                            m.from \notin pQ2[p], m.val \in Values, 
                            P3(p)!2!2!1!(m),
                            UNCHANGED <<msgs, pBal, pQ1, pWr>>
                     PROVE  <3>8!2
          BY <4>4, SMT DEF P3, PTypeOK, STypeOK, Messages
        <5>1. PICK ma \in msgs: /\ ma.type = "2a"
                                /\ ma.from = m.to
                                /\ ma.bal = m.bal \* = pBal[p_1]
                                /\ ma.val = m.val
          BY DEF STypeOK, Messages, AMsgInv
        <5>2. ma.bal = pBal[p] => pQ1[p] \in Quorums  
          BY <5>1, QuorumNonEmpty, SMT 
          DEFS PTypeOK, STypeOK, Messages, PMsgInv \* by PMsgInv!(p)!2!3
        <5> QED
          BY <5>1, <5>2, SMT DEF PTypeOK, STypeOK, Messages
      <4>5. CASE \E p_1 \in Proposers: P3(p_1) /\ pQ2[p_1] \in Quorums
        <5> SUFFICES ASSUME NEW p_1 \in Proposers,
                            pQ2[p_1] \in Quorums,
                            pWr' = [pWr EXCEPT ![p_1] = TRUE],
                            UNCHANGED << msgs, pBal, pVBal, pVVal, pQ1, pQ2>>
                     PROVE  <3>8!2
          BY <4>5, SMT DEF P3
        <5>a. CASE p = p_1
          BY <5>a, QuorumNonEmpty, ExistsQuorum1, SMT DEF PTypeOK, STypeOK, Messages
        <5>b. CASE p # p_1
          BY <5>b, QuorumNonEmpty, SMT DEF PTypeOK, STypeOK, Messages
        <5> QED
          BY <5>a, <5>b
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF PNext
    <3>9. \A a \in pQ1[p]': 
          \A c \in ValidBallots: pVBal[p]' \prec c /\ c \prec pBal[p]' => 
            DidntVoteIn(a,c)' /\ WontVoteIn(a, c)'
      <4> TAKE a \in pQ1[p]'
      <4> TAKE c \in ValidBallots
      <4> HAVE pVBal[p]' \prec c /\ c \prec pBal[p]' 
      <4> USE DEF DidntVoteIn
      <4>1. CASE \E p_1 \in Proposers: P1(p_1) 
        <5> \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
          BY <4>1, SMT DEF P1, VotedForIn
        <5> \A aa, cc: WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
          BY <4>1, SMT DEF P1, WontVoteIn, ParticipatedIn
        <5> QED
          BY <4>1 DEF P1, PTypeOK, STypeOK, Messages
      <4>2. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \notin Quorums 
        <5>1. /\ \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
              /\ \A aa, cc: WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
          BY <4>2 DEF P2, VotedForIn, WontVoteIn, ParticipatedIn
        <5> SUFFICES ASSUME NEW p_1 \in Proposers,
                            pQ1[p_1] \notin Quorums,
                            NEW m \in msgs, 
                            m.type = "1b", 
                            m.to = p_1, 
                            m.from \notin pQ1[p_1],
                            P2(p_1)!2!2!1!(m),
                            UNCHANGED <<msgs, pBal, pWr, pQ2>>
                     PROVE  DidntVoteIn(a, c) /\ WontVoteIn(a, c)
          BY <4>2, <5>1 DEF P2
        <5> SUFFICES ASSUME p = p_1,
                            m.bal = pBal[p_1], 
                            pVBal[p]' \prec c /\ c \prec pBal[p], 
                            a \in pQ1[p] \cup {m.from}
                     PROVE  DidntVoteIn(a, c) /\ WontVoteIn(a, c)
          BY  DEF PTypeOK, STypeOK, Messages
        <5>2. pBal[p] # NoBallot
          BY NoBallotNotHighest
        <5>a. CASE m.bal = pBal[p_1] /\ pVBal[p_1] \prec m.vbal
          <7>a. CASE a = m.from
            <8>1. DidntVoteIn(a, c)
              BY <5>a, <7>a DEF PTypeOK, STypeOK, Messages, AMsgInv
            <8>2. WontVoteIn(a, c)
              BY <5>a, <7>a, <5>2 DEF PTypeOK, STypeOK, Msg1bOK, WontVoteIn, ParticipatedIn
            <8>3. QED
              BY <8>1, <8>2
          <7> pQ2[p_1] = {}
            BY <5>a DEF PStateInv 
          <7> QED
            BY <5>a, <7>a, NoValueNotAValue, BallotTransLtLt, Z3 
            DEF PTypeOK, STypeOK, Messages
        <5>b. CASE m.bal = pBal[p_1] /\ ~ (pVBal[p_1] \prec m.vbal)
          <6>a. CASE a = m.from
            <7>x. m.vbal \preceq pVBal[p_1]
              BY <5>b, <6>a, BallotLeDef, BallotLtNeg, Z3 DEFS PTypeOK, STypeOK, Messages
            <7>y. m.vbal \prec c
              BY <5>b, <6>a, <7>x, BallotTransLeLt, Z3 DEFS PTypeOK, STypeOK, Messages
            <7>1. DidntVoteIn(a, c)
              BY <5>b, <6>a, <7>y DEF PTypeOK, STypeOK, Messages, AMsgInv
            <7>2. WontVoteIn(a, c)
              BY <5>b, <6>a, <5>2 DEF PTypeOK, STypeOK, Msg1bOK, WontVoteIn, ParticipatedIn
            <7> QED
              BY <7>1, <7>2
          <6> QED
            BY <5>b, <6>a, NoValueNotAValue
        <5>c. CASE m.bal # pBal[p_1]
          BY <5>c, NoValueNotAValue DEF PTypeOK, STypeOK, Messages
        <5> QED
          BY <5>a, <5>b, <5>c, Zenon
      <4>3. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \in Quorums 
        <5> \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
          BY <4>3 DEF P2, VotedForIn
        <5> \A aa, cc: WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
          BY <4>3 DEF P2, WontVoteIn, ParticipatedIn
        <5> QED
          BY <4>3 DEF P2
      <4>4. CASE \E p_1 \in Proposers: P3(p_1) /\ pQ2[p_1] \notin Quorums
        <5>1. \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
          BY <4>4 DEF P3, VotedForIn
        <5>2. \A aa, cc: WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
          BY <4>4 DEF P3, WontVoteIn, ParticipatedIn
        <5> SUFFICES ASSUME NEW p_1 \in Proposers, 
                            pQ2[p_1] \notin Quorums,
                            NEW m \in msgs, 
                            m.type = "2b", m.to = p_1, 
                            m.from \notin pQ2[p_1], m.val \in Values, 
                            P3(p_1)!2!2!1!(m),
                            UNCHANGED <<msgs, pBal, pQ1>>,
                            m.bal = pBal[p_1]
                     PROVE  DidntVoteIn(a, c) /\ WontVoteIn(a, c)
          BY <4>4, <5>1, <5>2 DEF P3, PTypeOK, STypeOK, Messages
        <5> p = p_1 => pVBal[p] \prec c
          BY BallotTransLeLt, BallotLtIsLe, Z3 DEFS PTypeOK, STypeOK, Messages
        <5> QED
          BY DEFS PTypeOK, STypeOK, Messages
      <4>5. CASE \E p_1 \in Proposers: P3(p_1) /\ pQ2[p_1] \in Quorums
        <5> \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
          BY <4>5 DEF P3, VotedForIn
        <5> \A aa, cc: WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
          BY <4>5 DEF P3, WontVoteIn, ParticipatedIn
        <5> QED
          BY <4>5 DEF P3
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF PNext
    <3>10. pQ1[p]' \notin Quorums => pQ2[p]' = {}
      <4> HAVE pQ1[p]' \notin Quorums
      <4>1. CASE \E p_1 \in Proposers: P1(p_1)
        BY <4>1, QuorumNonEmpty, NextBallotProps, SMT DEF P1, STypeOK, PTypeOK, Messages
      <4>2. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \notin Quorums
        BY <4>2, QuorumNonEmpty, SMT DEF P2, STypeOK, PTypeOK, Messages
      <4>3. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \in Quorums
        BY <4>3, QuorumNonEmpty, SMT DEF P2, STypeOK, PTypeOK, Messages
      <4>4. CASE \E p_1 \in Proposers: P3(p_1)
        BY <4>4, QuorumNonEmpty, Z3 DEF P3, STypeOK, PTypeOK, Messages, PMsgInv, AMsgInv
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3>11. pLBal[p]' \preceq pBal[p]'
      <4>1. CASE \E p_1 \in Proposers: P1(p_1)
        BY <4>1, BallotLtProps, NextBallotProps, Z3 DEF P1, STypeOK, PTypeOK, Messages
      <4>2. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \notin Quorums
        BY <4>2, SMT DEF P2, STypeOK, PTypeOK, Messages
      <4>3. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \in Quorums
        BY <4>3, BallotLtProps, Z3 DEF P2, STypeOK, PTypeOK, Messages
      <4>4. CASE \E p_1 \in Proposers: P3(p_1)
        BY <4>4, SMT DEF P3, STypeOK, PTypeOK, Messages
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3>12. \A m \in msgs': m.type = "1a" /\ m.from = p => m.bal \preceq pBal[p]' 
      <4> USE DEF STypeOK, PTypeOK, Messages
      <4>1. CASE \E p_1 \in Proposers: P1(p_1)
        BY <4>1, NextBallotProps, BallotLtProps, Z3 DEFS P1, ValidBallots
      <4>2. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \notin Quorums
        BY <4>2, SMT DEF P2
      <4>3. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \in Quorums
        BY <4>3, BallotLtProps, Z3 DEFS P2, ValidBallots \* by PStateInv!PS13 only
      <4>4. CASE \E p_1 \in Proposers: P3(p_1)
        BY <4>4, SMT DEF P3
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3>13. \A m \in msgs' : m.type = "2a" /\ m.from = p => m.bal \preceq pLBal[p]'
      <4>1. CASE \E p_1 \in Proposers: P1(p_1)
        BY <4>1, NextBallotProps, SMT DEF P1, STypeOK, PTypeOK, Messages
      <4>2. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \notin Quorums
        BY <4>2, SMT DEF P2, STypeOK, PTypeOK, Messages
      <4>3. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \in Quorums
        BY <4>3, BallotLtProps, Z3 DEF P2, STypeOK, PTypeOK, Messages
      <4>4. CASE \E p_1 \in Proposers: P3(p_1)
        BY <4>4, SMT DEF P3, STypeOK, PTypeOK, Messages
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3>14. pBal[p]' \in ValidBallots => pBal[p][2]' = p
      <4> HAVE pBal[p]' \in ValidBallots
      <4>1. CASE \E p_1 \in Proposers: P1(p_1)
        BY <4>1, NextBallotProps, SMT DEF P1, STypeOK, PTypeOK, Messages
      <4>2. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \notin Quorums
        BY <4>2, SMT DEF P2, STypeOK, PTypeOK, Messages
      <4>3. CASE \E p_1 \in Proposers: P2(p_1) /\ pQ1[p_1] \in Quorums
        BY <4>3, SMT DEF P2, STypeOK, PTypeOK, Messages
      <4>4. CASE \E p_1 \in Proposers: P3(p_1)
        BY <4>4, SMT DEF P3, STypeOK, PTypeOK, Messages
      <4> QED
        BY <4>1, <4>2, <4>3, <4>4 DEF PNext
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF PInv
<1> QED
  BY <1>1, <1>2, PTL DEF PSpec

(***************************************************************************)
(* Theorem: the predicate AInv is an inductive invariant of the acceptor.  *)
(* Note that it is not required to assume PMsgInv and PStateInv; this      *)
(* means that the behavior of the acceptors is independent of the          *)
(* proposers.                                                              *)
(***************************************************************************)
THEOREM AInvariant == ASpec => []AInv
<1> USE DEFS AInv, ValidBallots, Send, ProcSet
<1>1. SInit /\ AInit => AInv
  BY BallotLeRefl, NoBallotNotInValidBallots, NoBallotNotHighest 
  DEFS AInit, SInit, ATypeOK, STypeOK, Messages, AMsgInv, AStateInv, 
    VotedForIn, SafeAt, DidntVoteIn, WontVoteIn, ParticipatedIn
<1>2. AInv /\ [ANext]_(svars \o avars) => AInv'
  <2> SUFFICES ASSUME AInv, ANext PROVE AInv'
    <3> CASE UNCHANGED (svars \o avars)
      <4> /\ \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
          /\ \A aa, cc: WontVoteIn(aa, cc)' <=> WontVoteIn(aa, cc)
        BY DEF svars, avars, VotedForIn, WontVoteIn, ParticipatedIn
      <4> QED
        BY DEF svars, avars, ATypeOK, STypeOK, Messages, 
               AMsgInv, AStateInv, SafeAt, DidntVoteIn, Msg1bOK, Msg2bOK
    <3> QED
      OBVIOUS
  <2>0. SUFFICES ASSUME NEW a \in Acceptors,  
                        NEW m \in msgs, A1(a)!2!(m),
                        pc[a] = "A1",
                        pc' = [pc EXCEPT ![a] = "A1"]  
                 PROVE  AInv'
    BY DEF A1, ANext
  <2>1. STypeOK' /\ ATypeOK'
    <3> USE DEF STypeOK, ATypeOK, Messages
    <3>a. CASE A1(a)!2!(m)!1
      BY <2>0, <3>a, BallotLeNegNoBallot, BallotLeDef, SMT DEF A1, STypeOK      
    <3>b. CASE A1(a)!2!(m)!2
      <4> SUFFICES ASSUME m.type = "2a",
                          IF aBal[a] \preceq m.bal
                             THEN /\ aBal' = [aBal EXCEPT ![a] = m.bal]
                                  /\ aVBal' = [aVBal EXCEPT ![a] = m.bal]
                                  /\ aVVal' = [aVVal EXCEPT ![a] = m.val]
                                  /\ Send([type |-> "2b", from |-> a, to |-> m.from,
                                           bal |-> m.bal, val |-> m.val])
                             ELSE /\ Send([type |-> "2b", from |-> a, to |-> m.from,
                                           bal |-> aBal[a], val |-> NoValue])
                                  /\ UNCHANGED << aBal, aVBal, aVVal >>
                   PROVE  STypeOK' /\ ATypeOK'
        BY <2>0, <3>b DEFS A1
      <4>a. CASE aBal[a] \preceq m.bal
        BY <2>0, <4>a, SMT
      <4>b. CASE ~ (aBal[a] \preceq m.bal)
        BY <2>0, BallotLeNegNoBallot, <4>b, SMT
      <4> QED
        BY<4>a, <4>b        
    <3> QED
      BY <2>0, <3>a, <3>b
  <2>2. AMsgInv'
    <3>a. CASE A1(a)!2!(m)!1
      <4> SUFFICES ASSUME m.type = "1a",
                          IF aBal[a] \prec m.bal
                             THEN aBal' = [aBal EXCEPT ![a] = m.bal]
                             ELSE aBal' = aBal,
                          msgs' = (msgs \cup {[type |-> "1b", from |-> a, to |-> m.from,
                                               bal |-> aBal'[a], vbal |-> aVBal[a], 
                                               vval |-> aVVal[a]]}),
                          NEW mm \in msgs'
                   PROVE  AMsgInv!(mm)'
        BY <2>0, <3>a, SMT DEFS A1, AMsgInv, VotedForIn, DidntVoteIn
      <4> DEFINE M == [type |-> "1b", from |-> a, to |-> m.from,
                       bal |-> aBal'[a], vbal |-> aVBal[a], vval |-> aVVal[a]]
      <4>a. ASSUME mm.type = "1b" PROVE AMsgInv!(mm)!1!2'
        <5>a. CASE mm \in msgs
          <6>1. AMsgInv!(mm)!1!2
            BY <4>a, <5>a, Zenon DEFS AMsgInv, VotedForIn, DidntVoteIn
          <6> QED
            BY <6>1 DEF VotedForIn, DidntVoteIn
        <5>b. CASE mm = M
          <6>2. mm.vbal \preceq mm.bal
            BY <5>b, BallotTransLeLt, BallotLtIsLe, Z3 
            DEF STypeOK, ATypeOK, Messages, AStateInv
          <6>3. \/ /\ mm.vval \in Values
                   /\ mm.vbal \in ValidBallots
                   /\ VotedForIn(mm.from, mm.vval, mm.vbal)'
                \/ /\ mm.vval = NoValue
                   /\ mm.vbal = NoBallot
              BY <5>b DEF STypeOK, ATypeOK, AStateInv, Messages, VotedForIn
          <6>4. ASSUME NEW c \in ValidBallots, mm.vbal \prec c /\ c \prec mm.bal 
                PROVE DidntVoteIn(mm.from, c)'
            <7> aVBal[a] \prec c
              BY <5>b, <6>3, <6>4 DEF STypeOK, ATypeOK, Messages
            <7> QED
              BY <4>a, <5>b, <6>3, Z3 DEF STypeOK, ATypeOK, AStateInv, DidntVoteIn, VotedForIn
          <6> QED
            BY <6>2, <6>3, <6>4
        <5> QED 
          BY <5>a, <5>b
      <4>b. AMsgInv!(mm)!2'
        BY <2>0 DEF AMsgInv, VotedForIn, DidntVoteIn
      <4> QED 
        BY <4>a, <4>b
    <3>b. CASE A1(a)!2!(m)!2
      <4>0. SUFFICES 
              ASSUME m.type = "2a",
                     IF aBal[a] \preceq m.bal
                       THEN /\ aBal' = [aBal EXCEPT ![a] = m.bal]
                            /\ aVBal' = [aVBal EXCEPT ![a] = m.bal]
                            /\ aVVal' = [aVVal EXCEPT ![a] = m.val]
                            /\ Send([type |-> "2b", from |-> a, to |-> m.from,
                                     bal |-> m.bal, val |-> m.val])
                       ELSE /\ Send([type |-> "2b", from |-> a, to |-> m.from,
                                     bal |-> aBal[a], val |-> NoValue])
                            /\ UNCHANGED << aBal, aVBal, aVVal >>,
                     NEW mm \in msgs'
              PROVE  AMsgInv!(mm)'
        BY <2>0, <3>b DEFS AMsgInv, A1
      <4> HIDE DEF AMsgInv, VotedForIn
      <4>a. CASE aBal[a] \preceq m.bal
        <5> DEFINE M == [type |-> "2b", from |-> a, to |-> m.from,
                         bal |-> m.bal, val |-> m.val]
        <5>0. /\ aBal' = [aBal EXCEPT ![a] = m.bal]
              /\ aVBal' = [aVBal EXCEPT ![a] = m.bal]
              /\ aVVal' = [aVVal EXCEPT ![a] = m.val]
              /\ msgs' = msgs \cup {M}
          BY <4>a, <4>0, SMT
        <5>a. AMsgInv!(mm)!1'
          <6> SUFFICES ASSUME mm.type = "1b" PROVE AMsgInv!(mm)!1!2'
            OBVIOUS
\*          <6>1. mm.bal \preceq aBal[mm.from]'
\*            <7>a. CASE mm = M
\*              BY <4>a, <5>0, <7>a, BallotLeRefl 
\*              DEFS STypeOK, ATypeOK, Messages, AMsgInv
\*            <7>b. CASE mm \in msgs /\ mm.from = a
\*              BY <4>a, <5>0, <7>b, BallotTransLeLe, Z3
\*              DEF STypeOK, ATypeOK, Messages, AMsgInv
\*            <7>c. CASE mm \in msgs /\ mm.from # a
\*              BY <4>a, <5>0, <7>c DEF STypeOK, ATypeOK, Messages, AMsgInv
\*            <7> QED
\*              BY <5>0, <7>a, <7>b, <7>c
          <6>2. mm.vbal \preceq mm.bal
            BY <4>a, <5>0 DEF AMsgInv
          <6>3. \/ /\ mm.vval \in Values
                   /\ mm.vbal \in ValidBallots
                   /\ VotedForIn(mm.from, mm.vval, mm.vbal)'
                \/ /\ mm.vval = NoValue
                   /\ mm.vbal = NoBallot
            <7> VotedForIn(mm.from, mm.vval, mm.vbal) => 
                VotedForIn(mm.from, mm.vval, mm.vbal)'
              BY <5>0 DEF VotedForIn
            <7> QED
              BY <5>0 DEF AMsgInv
          <6>4. ASSUME NEW c \in ValidBallots, mm.vbal \prec c /\ c \prec mm.bal
                PROVE  DidntVoteIn(mm.from, c)'
            <7> SUFFICES ASSUME NEW vv \in Values,
                                NEW m_1, m_1 \in msgs \/ m_1 = M
                         PROVE ~ /\ m_1.type = "2b"
                                 /\ m_1.val = vv
                                 /\ m_1.bal = c
                                 /\ m_1.from = mm.from
              BY <5>0 DEF VotedForIn, DidntVoteIn
            <7>1. DidntVoteIn(mm.from, c)
              BY <5>0, <6>4 DEF AMsgInv
            <7>a. CASE m_1 \in msgs
              BY <5>0, <7>1, <7>a, Zenon DEF VotedForIn, DidntVoteIn
            <7>b. CASE m_1 = M
              <8> mm.bal \preceq aBal[mm.from]
                BY <5>0 DEF STypeOK, ATypeOK, Messages, AStateInv \*AMsgInv
              <8> c \prec aBal[mm.from] 
                BY <5>0, <6>4, BallotTransLtLe, Z3 DEF STypeOK, ATypeOK, Messages
              <8> mm.from = a => c \prec m.bal 
                BY <5>0, <7>b, <4>a, BallotTransLtLe, Z3 DEF STypeOK, ATypeOK, Messages
              <8> QED
                BY <5>0, <7>b, <6>4, <4>a, BallotLtNe DEF STypeOK, ATypeOK, Messages
            <7> QED
              BY <7>a, <7>b
          <6> QED
            BY (*<6>1,*) <6>2, <6>3, <6>4
        <5>b. AMsgInv!(mm)!2'
          <6> SUFFICES ASSUME mm.type = "2b", mm.val \in Values
                       PROVE  AMsgInv!(mm)!2!2'
            OBVIOUS
          <6>1. \E ma \in msgs' : /\ ma.type = "2a"
                                  /\ ma.from = mm.to
                                  /\ ma.bal  = mm.bal
                                  /\ ma.val  = mm.val
            BY <4>0, <5>0 DEF AMsgInv
\*          <6>2. mm.bal \preceq aVBal[mm.from]'
\*            <7>a. CASE mm \in msgs
\*              <8> mm.bal \preceq aVBal[mm.from]
\*                BY <5>0, <7>a DEF AMsgInv
\*              <8> QED
\*                BY <5>0, <7>a, <4>a, BallotTransLeLe, Z3 
\*                DEF STypeOK, ATypeOK, Messages, AStateInv
\*            <7>b. CASE mm = M
\*              BY <5>0, <7>b, BallotLeRefl DEF STypeOK, ATypeOK, Messages
\*            <7> QED
\*              BY <5>0, <7>a, <7>b
          <6> QED
            BY <6>1 (*, <6>2*)
        <5> QED
          BY <5>a, <5>b, Zenon
      <4>b. CASE ~ (aBal[a] \preceq m.bal)
        (*******************************************************************)
        (* The proposer tries to write with a lower ballot than the        *)
        (* acceptor.  The acceptor just replies with its ballot and        *)
        (* NoValue.                                                        *)
        (*******************************************************************)
        <5> DEFINE M == [type |-> "2b", from |-> a, to |-> m.from,
                         bal |-> aBal[a], val |-> NoValue]
        <5>0. /\ msgs' = msgs \cup {M}
              /\ UNCHANGED <<aBal, aVBal, aVVal>>
          BY <4>b, <4>0, SMT DEF STypeOK, ATypeOK, Messages
        <5>a. AMsgInv!(mm)!1'
          <6> SUFFICES ASSUME mm.type = "1b" PROVE AMsgInv!(mm)!1!2'
            OBVIOUS
\*          <6>1. mm.bal \preceq aBal[mm.from]'
\*            BY <4>b, <5>0 DEF AMsgInv
          <6>2. mm.vbal \preceq mm.bal
            BY <4>b, <5>0 DEF AMsgInv
          <6>3. \/ /\ mm.vval \in Values
                   /\ mm.vbal \in ValidBallots
                   /\ VotedForIn(mm.from, mm.vval, mm.vbal)'
                \/ /\ mm.vval = NoValue
                   /\ mm.vbal = NoBallot
            <7> VotedForIn(mm.from, mm.vval, mm.vbal) => 
                VotedForIn(mm.from, mm.vval, mm.vbal)'
              BY <5>0 DEF VotedForIn
            <7> QED
              BY <5>0 DEF AMsgInv
          <6>4. ASSUME NEW c \in ValidBallots, mm.vbal \prec c /\ c \prec mm.bal
                PROVE  ~ \E v \in Values : VotedForIn(mm.from, v, c)'
              <7> SUFFICES ASSUME NEW vv \in Values,
                                NEW m_1, m_1 \in msgs \/ m_1 = M
                         PROVE ~ /\ m_1.type =   "2b"
                                 /\ m_1.val = vv
                                 /\ m_1.bal = c
                                 /\ m_1.from = mm.from
              BY <5>0 DEF VotedForIn
            <7>1. ~ \E v \in Values : VotedForIn(mm.from, v, c)
              BY <5>0, <6>4 DEF AMsgInv, DidntVoteIn
            <7>a. CASE m_1 \in msgs
              BY <5>0, <7>1, <7>a, Zenon DEF VotedForIn
            <7>b. CASE m_1 = M
              <8> mm.bal \preceq aBal[mm.from]
                BY <5>0 DEF STypeOK, ATypeOK, Messages, AStateInv \*AMsgInv
              <8> c \prec aBal[mm.from] 
                BY <5>0, <6>4, BallotTransLtLe, Z3 DEF STypeOK, ATypeOK, Messages
              <8> QED
                BY <5>0, <7>b, BallotLtNe DEF STypeOK, ATypeOK, Messages
            <7> QED
              BY <7>a, <7>b
          <6> QED
            BY (*<6>1,*) <6>2, <6>3, <6>4 DEF DidntVoteIn
        <5>b. AMsgInv!(mm)!2'
          <6> SUFFICES ASSUME mm.type = "2b", mm.val \in Values
                       PROVE AMsgInv!(mm)!2!2'
            OBVIOUS
          <6>a. CASE mm \in msgs
            <7>a. \E ma \in msgs' : /\ ma.type = "2a"
                                    /\ ma.from = mm.to
                                    /\ ma.bal  = mm.bal
                                    /\ ma.val  = mm.val
              BY <4>b, <5>0, <6>a DEF AMsgInv, VotedForIn
\*            <7>b. mm.bal \preceq aVBal[mm.from]'
\*              <8> mm.bal \preceq aVBal[mm.from]
\*                BY <5>0, <6>a DEF AMsgInv
\*              <8> QED
\*                BY <5>0, <6>a, <4>b
            <7> QED
              BY <7>a (*, <7>b*)
          <6>b. CASE mm = M
            BY <6>b, NoValueNotAValue
          <6> QED
            BY <5>0, <6>a, <6>b
        <5> QED
          BY <5>a, <5>b, Zenon
      <4> QED
        BY <4>a, <4>b, Zenon
    <3> QED
      BY <2>0, <3>a, <3>b DEF ANext
  <2>3. AStateInv'
    <3>a. CASE A1(a)!2!(m)!1
      <4> SUFFICES 
            ASSUME m.type = "1a",
                   IF aBal[a] \prec m.bal
                      THEN aBal' = [aBal EXCEPT ![a] = m.bal]
                      ELSE aBal' = aBal,
                   Send([type |-> "1b", from |-> a, to |-> m.from, bal |-> aBal'[a], 
                         vbal |-> aVBal[a], vval |-> aVVal[a]]),
                   UNCHANGED <<aVBal, aVVal>>,
                   NEW a_1 \in Acceptors
            PROVE  AStateInv!(a_1)'
        BY <2>0, <3>a, Z3 
        DEFS A1, AStateInv, VotedForIn, WontVoteIn, ParticipatedIn, DidntVoteIn
      <4> \A aa, vv, cc: VotedForIn(aa, vv, cc)' <=> VotedForIn(aa, vv, cc)
        BY DEF VotedForIn
      <4>a. CASE aBal[a] \prec m.bal
        <5> USE <4>a
        <5> aBal' = [aBal EXCEPT ![a] = m.bal]
          BY <4>a
        <5> QED    
          <6>1. (aVBal[a_1] = NoBallot <=> aVVal[a_1] = NoValue)'
            BY DEF AStateInv
          <6>2. (aVBal[a_1] \preceq aBal[a_1])'
            BY BallotTransLeLt, BallotLtIsLe, Z3 
            DEF AStateInv, STypeOK, ATypeOK, Messages  
          <6>3. (aVBal[a_1] \in ValidBallots => VotedForIn(a_1, aVVal[a_1], aVBal[a_1]))'
            BY DEF AStateInv
          <6>4. (\A c \in Ballots : aVBal[a_1] \prec c => DidntVoteIn(a_1, c))'
            BY DEF AStateInv, DidntVoteIn
          <6>5a. (\A b \in Ballots : WontVoteIn(a_1, b) => b \prec aBal[a_1])'
            <7> SUFFICES ASSUME NEW b \in Ballots,
                                WontVoteIn(a_1, b)'
                         PROVE  b \prec aBal[a_1]'
              OBVIOUS
            <7>a. CASE a = a_1
              <8> PICK d \in ValidBallots : b \prec d /\ ParticipatedIn(a, d)'
                BY <7>a, Z3 DEF AStateInv, WontVoteIn
              <8> PICK m_2 \in msgs' :
                    /\ \/ m_2.type = "1b"
                       \/ m_2.type = "2b" /\ m_2.val \in Values
                    /\ m_2.from = a
                    /\ m_2.bal = d
                BY <7>a, Zenon DEF ParticipatedIn
              <8> QED
                BY <7>a, BallotTransLtLe, BallotTransLtLt, Z3
                DEF STypeOK, ATypeOK, Messages, AMsgInv, AStateInv
            <7>b. CASE a # a_1
              BY <7>b, Z3 
              DEF STypeOK, ATypeOK, Messages, AStateInv, WontVoteIn, ParticipatedIn, AMsgInv
            <7> QED
              BY <7>a, <7>b
          <6>5b. (\A b \in Ballots : b \prec aBal[a_1] => WontVoteIn(a_1, b))'
            <7> SUFFICES ASSUME NEW b \in Ballots,
                                b \prec aBal[a_1]'
                         PROVE  WontVoteIn(a_1, b)'
              OBVIOUS
            <7>a. CASE a = a_1
              <8> USE <7>a
              <8> DEFINE m1b == [type |-> "1b", from |-> a, to |-> m.from,
                                 bal |-> aBal[a]', vbal |-> aVBal[a], vval |-> aVVal[a]]
              <8> PICK mx \in msgs' : mx = m1b \* Witness for \E below.
                BY Zenon
              <8> ParticipatedIn(a, m.bal)'
                BY DEF ParticipatedIn, ATypeOK
              <8> QED
                BY Z3 DEF STypeOK, ATypeOK, Messages, WontVoteIn
            <7>b. CASE a # a_1
              BY <7>b, Z3T(30) DEF STypeOK, ATypeOK, WontVoteIn, ParticipatedIn, PStateInv, AStateInv
            <7> QED
              BY <7>a, <7>b
          <6>6. (\A b \in Ballots: 
                   DidntVoteIn(a_1, b) => aVBal[a_1] = NoBallot \/ aVBal[a_1] # b)'
            BY DEF AStateInv, STypeOK, ATypeOK, Messages, DidntVoteIn
          <6>7. (\A mm \in msgs: mm.from = a_1 /\ mm.type = "1b" => mm.bal \preceq aBal[a_1])'
            BY BallotLtProps, Z3 DEFS STypeOK, ATypeOK, Messages, AStateInv
          <6>8. (\A mm \in msgs: mm.from = a_1 /\ mm.type = "2b" /\ mm.val \in Values 
                  => mm.bal \preceq aVBal[a_1])'
            BY DEF AStateInv
          <6> QED
            BY <6>1, <6>2, <6>3, <6>4, <6>5a, <6>5b, <6>6, <6>7, <6>8
      <4>b. CASE ~ (aBal[a] \prec m.bal)
        <5> UNCHANGED aBal 
          BY <4>b
        <5>4. (\A b \in Ballots : aVBal[a_1] \prec b => DidntVoteIn(a_1, b))'
          BY DEF AStateInv, STypeOK, ATypeOK, Messages, DidntVoteIn
        <5>5a. \A b \in Ballots : WontVoteIn(a_1, b)' => b \prec aBal[a_1]'
          <6>1. \A q \in Acceptors: aVBal[q] = NoBallot 
                  => \A bb \in ValidBallots: DidntVoteIn(q, bb)
            BY NoBallotLowest DEF AStateInv
          <6> SUFFICES ASSUME NEW b \in Ballots,
                              NEW d \in ValidBallots,
                              b \prec d,
                              NEW m_2 \in msgs',
                              m_2.from = a_1,
                              m_2.bal = d,
                              \/ m_2.type = "1b"
                              \/ m_2.type = "2b" /\ m_2.val \in Values
                       PROVE  b \prec aBal[a_1]'
            BY DEF ParticipatedIn, WontVoteIn
          <6>a. CASE m_2.type = "1b"
            BY <6>a, <4>b, <6>1, Z3 DEF AStateInv, WontVoteIn, ParticipatedIn
          <6>b. CASE m_2.type = "2b" /\ m_2.val \in Values
            BY <6>b, <4>b, Z3 DEF AStateInv, WontVoteIn, ParticipatedIn
          <6> QED
            BY <6>a, <6>b
        <5>5b. \A b \in Ballots : b \prec aBal[a_1]' => WontVoteIn(a_1, b)'
          <6> SUFFICES ASSUME NEW b \in Ballots, b \prec aBal[a_1]
                       PROVE  WontVoteIn(a_1, b)'
            OBVIOUS
          <6>a. CASE a = a_1
            <7>a. CASE aVBal[a] = NoBallot
              BY <4>b, <6>a, <7>a, SMT DEF AStateInv, WontVoteIn, ParticipatedIn
            <7>b. CASE aVBal[a] \in ValidBallots
              BY <4>b, <6>a, <7>b, SMT DEF AStateInv, WontVoteIn, ParticipatedIn
            <7> QED
              BY <7>a, <7>b DEF STypeOK, ATypeOK
          <6>b. CASE a # a_1
            BY <4>b, <6>b, Z3 DEF AStateInv, STypeOK, ATypeOK, WontVoteIn, ParticipatedIn
          <6> QED
            BY <6>a, <6>b
        <5>6. ASSUME NEW mm \in msgs' 
              PROVE mm.from = a_1 /\ mm.type = "1b" => mm.bal \preceq aBal[a_1]'
          <6> DEFINE M == [type |-> "1b", from |-> a, to |-> m.from,
                           bal |-> aBal'[a], vbal |-> aVBal[a], vval |-> aVVal[a]]
          <6>a. CASE mm \in msgs
            BY <6>a, BallotTransLeLt, BallotLtIsLe, Z3
            DEF STypeOK, ATypeOK, Messages, AStateInv
          <6>b. CASE mm = M
            BY <6>b, BallotLeRefl DEFS STypeOK, ATypeOK, Messages, AMsgInv
          <6> QED
            BY <6>a, <6>b
        <5> QED
          BY <5>4, <5>5a, <5>5b, <5>6 DEF AStateInv
      <4> QED
        BY <4>a, <4>b DEF STypeOK, ATypeOK, Messages
    <3>b. CASE A1(a)!2!(m)!2
      <4>1. SUFFICES 
              ASSUME m.type = "2a",
                     IF aBal[a] \preceq m.bal
                       THEN /\ aBal' = [aBal EXCEPT ![a] = m.bal]
                            /\ aVBal' = [aVBal EXCEPT ![a] = m.bal]
                            /\ aVVal' = [aVVal EXCEPT ![a] = m.val]
                            /\ Send([type |-> "2b", from |-> a, to |-> m.from,
                                     bal |-> m.bal, val |-> m.val])
                       ELSE /\ Send([type |-> "2b", from |-> a, to |-> m.from,
                                     bal |-> aBal[a], val |-> NoValue])
                            /\ UNCHANGED << aBal, aVBal, aVVal >>,
                     NEW a_1 \in Acceptors
              PROVE  AStateInv!(a_1)'
        BY <2>0, <3>b DEF AStateInv
      <4>a. CASE aBal[a] \preceq m.bal
        <5> DEFINE M == [type |-> "2b", from |-> a, to |-> m.from,
                         bal |-> m.bal, val |-> m.val]
        <5> /\ m.type = "2a"
            /\ aBal' = [aBal EXCEPT ![a] = m.bal]
            /\ aVBal' = [aVBal EXCEPT ![a] = m.bal]
            /\ aVVal' = [aVVal EXCEPT ![a] = m.val]
            /\ msgs' = msgs \cup {M}
          BY <4>1, <4>a, Zenon
        <5>a. CASE a = a_1
          <6> USE <5>a
          <6>1. (aVVal[a_1] = NoValue <=> aVBal[a_1] = NoBallot)'
            <7> SUFFICES m.val = NoValue <=> m.bal = NoBallot
              BY DEF STypeOK, ATypeOK
            <7> m.type = "2a" => m.val \in Values /\ m.bal \in ValidBallots
              BY DEF STypeOK, ATypeOK, Messages
            <7> QED
              BY NoValueNotAValue, NoBallotNotInValidBallots
          <6>2. (aVBal[a_1] \preceq aBal[a_1])'
            BY <4>a, BallotLeRefl DEF STypeOK, ATypeOK, Messages
          <6>3. (aVBal[a_1] \in ValidBallots => VotedForIn(a_1, aVVal[a_1], aVBal[a_1]))'
            <7> SUFFICES VotedForIn(a, m.val, m.bal)'
              BY DEF STypeOK, ATypeOK, Messages
            <7> M \in msgs' /\ m.val \in Values
              BY DEF STypeOK, ATypeOK, Messages
            <7> PICK mx \in msgs' : mx = M
              BY Zenon
            <7> QED
              BY DEF VotedForIn
          <6>4. \A c \in Ballots : aVBal[a_1]' \prec c => DidntVoteIn(a_1, c)'
            <7> SUFFICES ASSUME NEW c \in Ballots, m.bal \prec c
                         PROVE  DidntVoteIn(a_1, c)'
              BY DEF STypeOK, ATypeOK
            <7>1. aVBal[a] \preceq aBal[a]
              BY DEF AStateInv
            <7>2. aVBal[a] \prec c
              BY <4>a, <7>1, BallotTransLeLe, BallotTransLeLt, Z3 
              DEF STypeOK, ATypeOK, Messages
            <7>3. m.bal # c
              BY BallotLtNe, Z3 DEF STypeOK, ATypeOK, Messages
            <7> QED
              BY <7>2, <7>3 DEF AMsgInv, VotedForIn, DidntVoteIn, AStateInv
          <6>5. (\A b \in Ballots : WontVoteIn(a_1, b) <=> b \prec aBal[a_1])'
            <7> SUFFICES ASSUME NEW b \in Ballots
                         PROVE  WontVoteIn(a_1, b)' <=> b \prec m.bal
              BY DEF STypeOK, ATypeOK, Messages
            <7>a. WontVoteIn(a_1, b)' => b \prec m.bal
              BY <4>a, BallotTransLtLt, BallotTransLtLe, BallotTransLeLt, Z3 
              DEF WontVoteIn, ParticipatedIn, STypeOK, ATypeOK, Messages, AStateInv
            <7>b. b \prec m.bal => WontVoteIn(a_1, b)'
              <8> SUFFICES ASSUME b \prec m.bal PROVE WontVoteIn(a_1, b)'
                OBVIOUS
              <8> m.val \in Values
                BY DEF STypeOK, Messages, AMsgInv
              <8> PICK mx \in msgs' : mx = M \* Witness for \E below.
                BY Zenon
              <8> SUFFICES ParticipatedIn(a_1, m.bal)'
                BY <4>a, Z3 DEF WontVoteIn, STypeOK, ATypeOK, Messages
              <8> QED
                BY <4>a, Z3 DEF ParticipatedIn, STypeOK, ATypeOK, Messages
            <7> QED
              BY <7>a, <7>b
          <6>6. (\A mm \in msgs: mm.from = a_1 /\ mm.type = "1b" => mm.bal \preceq aBal[a_1])'
            BY <4>a, BallotLtProps, Z3 DEFS STypeOK, ATypeOK, Messages, AStateInv
          <6>7. (\A mm \in msgs: mm.from = a_1 /\ mm.type = "2b" /\ mm.val \in Values
                  => mm.bal \preceq aVBal[a_1])'
            BY <4>a, BallotLtProps, Z3 DEF STypeOK, ATypeOK, Messages, AStateInv
          <6> QED
            BY <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7
        <5>b. CASE a # a_1
          <6> USE <5>b DEFS STypeOK, ATypeOK, Messages
          <6>1. (aVBal[a_1] = NoBallot <=> aVVal[a_1] = NoValue)'
            BY DEF AStateInv
          <6>2. (aVBal[a_1] \preceq aBal[a_1])'
            BY DEF AStateInv
          <6>3. (aVBal[a_1] \in ValidBallots => VotedForIn(a_1, aVVal[a_1], aVBal[a_1]))'
            BY DEF AStateInv, VotedForIn
          <6>4. (\A c \in Ballots : aVBal[a_1] \prec c => DidntVoteIn(a_1, c))'
            <7> SUFFICES ASSUME NEW c \in Ballots,
                                aVBal[a_1] \prec c
                         PROVE  DidntVoteIn(a_1, c)'
              OBVIOUS
            <7> QED
              BY DEF AStateInv, VotedForIn, DidntVoteIn
          <6>5. (\A b \in Ballots : WontVoteIn(a_1, b) <=> b \prec aBal[a_1])'
            <7> SUFFICES ASSUME NEW b \in Ballots
                         PROVE  WontVoteIn(a_1, b)' <=> b \prec aBal[a_1]
              OBVIOUS
            <7> QED
              BY DEF AStateInv, WontVoteIn, ParticipatedIn
          <6>6. (\A b \in Ballots: 
                   DidntVoteIn(a_1, b) => aVBal[a_1] = NoBallot \/ aVBal[a_1] # b)'
            <7> SUFFICES ASSUME NEW b \in Ballots,
                                \A v \in Values : ~ VotedForIn(a_1, v, b)'
                         PROVE  aVBal[a_1] = NoBallot \/ aVBal[a_1] # b
              BY DEF DidntVoteIn
            <7> QED
              BY DEFS AStateInv, AMsgInv, VotedForIn
          <6>7. (\A mm \in msgs :
                  mm.from = a_1 /\ mm.type = "1b" => mm.bal \preceq aBal[a_1])'
            BY <4>a, BallotLtProps, Z3 DEF AStateInv
          <6>8. (\A mm \in msgs: mm.from = a_1 /\ mm.type = "2b" /\ mm.val \in Values
                  => mm.bal \preceq aVBal[a_1])'
            BY <4>a, BallotLtProps, Z3 DEF AStateInv              
          <6> QED
            BY <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, Zenon
        <5>5. QED
          BY <5>a, <5>b
      <4>b. CASE ~ (aBal[a] \preceq m.bal)
        <5> DEFINE M == [type |-> "2b", from |-> a, to |-> m.from,
                         bal |-> aBal[a], val |-> NoValue]
        <5> /\ Send(M)
            /\ UNCHANGED <<aBal, aVBal, aVVal>>
          BY <4>1, <4>b DEF STypeOK, ATypeOK, Messages
        <5>3. (aVBal[a_1] \in ValidBallots => VotedForIn(a_1, aVVal[a_1], aVBal[a_1]))'
          BY DEF AStateInv, VotedForIn, ATypeOK
        <5>4. (\A c \in Ballots : aVBal[a_1] \prec c => DidntVoteIn(a_1, c))'
          BY NoValueNotAValue DEF VotedForIn, DidntVoteIn, AStateInv
        <5>5. (\A b \in Ballots : WontVoteIn(a_1, b) <=> b \prec aBal[a_1])'
          BY DEF WontVoteIn, ParticipatedIn, AStateInv
        <5>6. (\A mm \in msgs: mm.from = a_1 /\ mm.type = "1b" => mm.bal \preceq aBal[a_1])'
          BY <4>b, BallotLtProps DEF AStateInv
        <5>7. (\A mm \in msgs: mm.from = a_1 /\ mm.type = "2b" /\ mm.val \in Values
                => mm.bal \preceq aVBal[a_1])'
          BY <4>b, BallotLtProps, NoValueNotAValue DEF AStateInv
        <5> QED
          BY <5>3, <5>4, <5>5, <5>6, <5>7 DEF AStateInv
      <4> QED
        BY <4>a, <4>b DEF STypeOK, ATypeOK, Messages
    <3> QED
      BY <2>0, <3>a, <3>b DEF ANext
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF AInv
<1> QED
  BY <1>1, <1>2, PTL DEF ASpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* The proofs of the main (safety) properties for this spec, consistency   *)
(* of acceptors and proposers.                                             *)
(***************************************************************************)
(***************************************************************************)
(* To prove that the consistency property of the acceptors is an invariant *)
(* over the acceptor spec, we need to assume that the invariant about      *)
(* messages sent by proposers holds.                                       *)
(***************************************************************************)
THEOREM AConsistent == ASSUME PMsgInv PROVE ASpec => []AConsistency
<1> USE DEF ValidBallots, AInv
<1>1. AInv => AConsistency
  <2> SUFFICES ASSUME AInv,
                      NEW v1 \in Values,  NEW v2 \in Values, 
                      NEW b1 \in ValidBallots, NEW b2 \in ValidBallots,
                      ChosenIn(v1, b1), ChosenIn(v2, b2),
                      b1 \preceq b2
               PROVE  v1 = v2
    BY BallotLtProps DEF AConsistency, Chosen
  <2>1. CASE b1 = b2
    BY <2>1, VotedOnce, QuorumAssumption1, QuorumNonEmpty DEF ChosenIn, AInv
  <2>2. CASE b1 \prec b2
    <3>1. SafeAt(v2, b2)
      BY VotedInv, QuorumAssumption1, QuorumNonEmpty DEF ChosenIn
    <3>2. PICK Q2 \in Quorums : 
                 \A a \in Q2 : VotedForIn(a, v2, b1) \/ DidntVoteIn(a, b1)
      BY <3>1, <2>2 DEF SafeAt
    <3>3. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
      BY DEF ChosenIn
    <3>4. QED
      BY <3>2, <3>3, QuorumAssumption1, QuorumAssumption2, VotedOnce, Z3 
      DEF DidntVoteIn
  <2>3. QED
    BY <2>1, <2>2, BallotLeDef
<1>2. QED
  BY AInvariant, <1>1, PTL

(***************************************************************************)
(* Likewise, to prove that the consistency property of the proposers is an *)
(* invariant over the proposer spec, we assume the invariant about         *)
(* messages sent by acceptors.                                             *)
(***************************************************************************)
THEOREM PConsistent == ASSUME AMsgInv PROVE PSpec => []PConsistency
<1> USE DEF ValidBallots, PInv
<1>1. PInv => PConsistency
  <2> SUFFICES ASSUME PInv,
                      NEW p1 \in Proposers, NEW p2 \in Proposers,
                      NEW v1 \in Values,  NEW v2 \in Values, 
                      NEW b1 \in ValidBallots, NEW b2 \in ValidBallots,
                      PKnowsIn(p1,v1,b1), PKnowsIn(p2,v2,b2),
                      b1 \preceq b2
               PROVE  v1 = v2
    BY BallotLtProps DEF PConsistency, PKnows
  <2>1. CASE b1 = b2
    BY <2>1, KnowsSameValue, QuorumAssumption1, QuorumNonEmpty
  <2>2. CASE b1 \prec b2
    <3>1. SafeAt(v2, b2)
      <4>1. pQ2[p1] \in Quorums /\ \A a \in pQ2[p1]: VotedForIn(a,v1,b1)
        BY PKnowsIn(p1,v1,b1) DEF PKnowsIn, PStateInv, STypeOK, PTypeOK
      <4>2. pQ2[p2] \in Quorums /\ \A a \in pQ2[p2]: VotedForIn(a,v2,b2)
        BY PKnowsIn(p2,v2,b2) DEF PKnowsIn, PStateInv, STypeOK, PTypeOK
      <4>3. QED
        BY VotedInv, QuorumAssumption1, QuorumNonEmpty, <4>1, <4>2 
    <3>2. PICK Q2 \in Quorums : 
                 \A a \in Q2 : \/ VotedForIn(a, v2, b1)
                               \/ DidntVoteIn(a, b1) \* /\ WontVoteIn(a, b1) not needed
      BY <3>1, <2>2 DEF SafeAt
    <3>3. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
      BY DEF PKnowsIn, PStateInv
    <3>4. QED
      BY <3>2, <3>3, QuorumAssumption1, QuorumAssumption2, VotedOnce, Z3 DEF DidntVoteIn
  <2>3. QED
    BY <2>1, <2>2, BallotLeDef
<1>2. QED
  BY PInvariant, <1>1, PTL

=============================================================================
\* Modification History
\* Last modified Wed Sep 19 20:40:08 CEST 2018 by hernanv
\* Created Fri Dec 8 12:29:00 EDT 2017 by hernanv
