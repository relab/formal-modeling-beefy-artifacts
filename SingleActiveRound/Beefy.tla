--------------------- MODULE Beefy -----------------------------------------
EXTENDS Integers, FiniteSets, typedefs

(***************************************************************************)
(* PROTOCOL PARAMETERS                                                     *)
(***************************************************************************)
CONSTANTS
    \* Set of correct nodes.
    \* @type: Set($node);
    CNodes,
    \* Set of faulty nodes (unknown to correct nodes).
    \* @type: Set($node);
    FNodes,
    \* Set of all quorums in the system.
    \* @type: Set(Set($node));
    Quorums,
    \* The set of all blocks in the system.
    \* @type: Set($block);
    Blocks

(***************************************************************************)
(* Definitions                                                             *)
(***************************************************************************)
\* The set of all nodes (correct + faulty).
\* @type: Set($node);
Nodes == CNodes \cup FNodes

\* Each block b in Blocks must have an associated height.
\* @type: Set($height);
Heights == {-1} \cup Nat

\* The set of epochs.
\* @type: Set($epoch);
Epochs == {-1} \cup Nat

\* A value representing infinity (used for next mandatory block).
\* @type: $height;
Infinity == CHOOSE i : (i \notin Nat) /\ (\A r \in Nat : i > r)

(***************************************************************************)
(* Assume Statements                                                       *)
(***************************************************************************)

\* Assume the sets of correct and faulty nodes are disjoint.
ASSUME CNodes \cap FNodes = {}

\* Quorum Assumption:
\*  - Every quorum is a subset of Nodes.
\*  - Any two quorums intersect in at least one correct node.
\*  - Any superset of a quorum is also a quorum.
\*  - The set of all nodes is a quorum.
ASSUME QuorumAssumption == 
    /\ \A Q \in Quorums : Q \subseteq Nodes
    /\ \A Q1, Q2 \in Quorums : \E n \in CNodes: n \in (Q1 \cap Q2)
    /\ \A Q \in Quorums: \A S \in SUBSET Nodes: 
                        Q \subseteq S => S \in Quorums
    /\ Nodes \in Quorums

\* Assume there is at least one block.
ASSUME NonEmptyBlocks == Blocks /= {}

\* Assume the set of blocks is finite. This is needed to guarantee that the set
\* of finalized blocks with epoch greater than any given epoch has a minimum-height
\* element, which is required for findMandatoryBlock to be well-defined.
ASSUME FiniteBlocks == IsFiniteSet(Blocks)

\* Choose a genesis block from the set of blocks.
\* @type: () => $block;
gen == CHOOSE b \in Blocks : TRUE

(***************************************************************************)
(* Protocol State Variables                                                *)
(***************************************************************************)
VARIABLES
    \* A node's view of active rounds (set of heights).
    \* @type: $node -> Set($height);
    round,
    \* A node's view of best BEEFY block.
    \* @type: $node -> $block;
    bestBEEFY,
    \* A node's view of best GRANDPA block.
    \* @type: $node -> $block;
    bestGRANDPA,
    \* The mandatory block that starts the current session for a node.
    \* @type: $node -> $block;
    sessionStart,
    \* A mapping of each node to the mandatory blocks it has a BEEFY
    \* Justification for.
    \* @type: $node -> Set($block);
    mandatoryBlocks,
    \* Program counter for each node, indicating the current step in the
    \* protocol ("Receive" or "Vote").
    \* @type: $node -> $pc;
    pc,
    \* Votes for each block, mapping of block to set of nodes that have
    \* voted for it.
    \* @type: $block -> Set($node);
    votes,
    \* Blocks height, mapping of block to height.
    \* @type: $block -> $height;
    height,
    \* Parent block mapping, mapping of block to its parent block.
    \* @type: $block -> $block;
    parent,
    \* Block status, mapping of block to its status (None or Finalized).
    \* @type: $block -> $status;
    status,
    \* Block epoch, mapping of block to its epoch.
    \* @type: $block -> $epoch;
    epoch

\* Tuple of all state variables.
vars == <<round, bestBEEFY, bestGRANDPA, sessionStart, mandatoryBlocks, pc, 
            votes, height, status, parent, epoch>>

(***************************************************************************)
(* The type invariant                                                      *)
(***************************************************************************)
TypeOK ==
    /\ round \in [CNodes -> SUBSET Heights]
    /\ bestBEEFY \in [CNodes -> Blocks]
    /\ bestGRANDPA \in [CNodes -> Blocks]
    /\ sessionStart \in [CNodes -> Blocks]
    /\ mandatoryBlocks \in [CNodes -> SUBSET Blocks]
    /\ pc \in [CNodes -> {"Receive", "Vote"}]
    /\ votes \in [Blocks -> SUBSET Nodes]
    /\ height \in [Blocks -> Heights]
    /\ status \in [Blocks -> {"None", "Finalized"}]
    /\ parent \in [Blocks -> Blocks]
    /\ epoch \in [Blocks -> Epochs]

(***************************************************************************)
(* The initial state of the system.                                        *)
(* Node State:                                                             *)
(*  - round: All honest nodes start with no active rounds (empty set).     *)
(*  - bestBEEFY: All honest nodes initialize to the genesis block.         *)
(*  - bestGRANDPA: All honest nodes initialize to the genesis block.       *)
(*  - sessionStart: All honest nodes initialize to the genesis block.      *)
(*  - mandatoryBlocks: All honest nodes have genesis in their set of       *)
(*    mandatory blocks.                                                    *)
(*  - pc: pc: All honest nodes are ready to receive blocks ("Receive").    *)
(*                                                                         *)
(* Block State:                                                            *)
(*  - height: Genesis has height 0; all other blocks have height -1        *)
(*    (not yet proposed).                                                  *)
(*  - status: Genesis is "Finalized"; all other blocks are "None".         *)
(*  - parent: All blocks are their own parent initially (only valid for    *)
(*    genesis; others will be updated when proposed).                      *)
(*  - epoch: Genesis has epoch 0; all other blocks have epoch -1 (not      *)
(*    yet proposed).                                                       *)
(*  - votes: Genesis has votes from all nodes; all other blocks have no    *)
(*    votes.                                                               *)
(***************************************************************************)
Init ==
    \* Node State
    /\ round = [n \in CNodes |-> {}]
    /\ bestBEEFY = [n \in CNodes |-> gen]
    /\ bestGRANDPA = [n \in CNodes |-> gen]
    /\ sessionStart = [n \in CNodes |-> gen]
    /\ mandatoryBlocks = [n \in CNodes |-> {gen}]
    /\ pc = [n \in CNodes |-> "Receive"]
    \* Block State
    /\ height = [[b \in Blocks |-> -1] EXCEPT ![gen] = 0]
    /\ status = [[b \in Blocks |-> "None"] EXCEPT ![gen] = "Finalized"]
    /\ parent = [b \in Blocks |-> b]
    /\ epoch = [[b \in Blocks |-> -1] EXCEPT ![gen] = 0]
    /\ votes = [[b \in Blocks |-> {}] EXCEPT ![gen] = Nodes]
                
(***************************************************************************)
(* A block b is proposed iff:                                              *)
(*  - Block b has been assigned a valid height (height[b] > -1).           *)
(*  - Block b has been assigned a valid epoch (epoch[b] > -1).             *)
(*                                                                         *)
(* Note: The initial value -1 indicates that a block has not yet been      *)
(* proposed. Once proposed, both height and epoch must be non-negative.    *)
(***************************************************************************)
Proposed(b) == 
    /\ b \in Blocks
    /\ height[b] > -1
    /\ epoch[b] > -1

(***************************************************************************)
(* A block p is a valid parent for a block with height h and epoch e iff:  *)
(*  - The parent block p has already been proposed.                        *)
(*  - The parent block's height is exactly one less than h.                *)
(*  - The parent block's epoch is less than or equal to e.                 *)
(*                                                                         *)
(* Note: Epochs can remain constant across multiple blocks (e.g., 0 -> 0   *)
(* -> 0 -> 0) or skip epochs entirely (e.g., 0 -> 0 -> 2 -> 2 -> 2).       *)
(***************************************************************************)
ValidParent(p, h, e) == 
    /\ Proposed(p)
    /\ h = height[p] + 1
    /\ epoch[p] <= e

(***************************************************************************)
(* Helper operator to update the state when proposing a new block.         *)
(***************************************************************************)
propose(b, p, h, e) ==
    /\ height' = [height EXCEPT ![b] = h]
    /\ parent' = [parent EXCEPT ![b] = p]
    /\ epoch' = [epoch EXCEPT ![b] = e]
    /\ status' = [status EXCEPT ![b] = "Finalized"]

(***************************************************************************)
(* Proposes a new block b with parent p in epoch e iff:                    *)
(*  - Block b has not been proposed yet.                                   *)
(*  - Block p is a valid parent.                                           *)
(*  - There does not exists a block with height[p] + 1 that is proposed.   *)
(*                                                                         *)
(* The newly proposed block is immediately marked as "Finalized" to        *)
(* model GRANDPA finalization occurring simultaneously with proposal.      *)
(***************************************************************************)
Propose(b, p, e) ==
    /\ ~Proposed(b)
    /\ ValidParent(p, height[p] + 1, e)
    /\ \A c \in Blocks : Proposed(c) => height[c] < height[p] + 1
    /\ propose(b, p, height[p] + 1, e)
    /\ UNCHANGED <<round, bestBEEFY, bestGRANDPA, sessionStart, pc,
                    mandatoryBlocks, votes>>

(***************************************************************************)
(* Block b is finalized (GRANDPA Finalized) iff:                           *)
(*  - Block b has been proposed.                                           *)
(*  - Block b's status is explicitly set to "Finalized".                   *)
(***************************************************************************)
Finalized(b) == 
    /\ Proposed(b)
    /\ status[b] = "Finalized"

(***************************************************************************)
(* Block b is Justified (BEEFY Justified) iff:                             *)
(*  - Block b is finalized (which implies it is proposed).                 *)
(*  - A quorum of nodes has voted for it (quorum certificate).             *)
(*  - Quorum certificate corresponds to N - T = 2f + 1 votes.              *)
(***************************************************************************)
Justified(b) == 
    /\ Finalized(b)
    /\ votes[b] \in Quorums

(***************************************************************************)
(* Updates the status of block b to "Finalized" iff:                       *)
(*   - Block b has been proposed.                                          *)
(*   - Block b is not already finalized.                                   *)
(*   - The parent block of b is finalized.                                 *)
(*   - All finalized blocks have height strictly less than b's height.     *)
(*                                                                         *)
(* Note: While GRANDPA can finalize multiple blocks simultaneously, this   *)
(* specification assumes that only one block is finalized at a time. This  *)
(* operator ensures that at most one block per height is updated to        *)
(* "Finalized" and that all finalized blocks lie on a single chain.        *)
(***************************************************************************)
UpdateBlock(b) ==
    /\ Proposed(b)
    /\ ~Finalized(b)
    /\ Finalized(parent[b])
    /\ \A c \in Blocks :
        Finalized(c) => height[c] < height[b] 
    /\ status' = [status EXCEPT ![b] = "Finalized"]
    /\ UNCHANGED <<round, bestBEEFY, bestGRANDPA, sessionStart, pc,
                    mandatoryBlocks, votes, height, parent, epoch>>

(***************************************************************************)
(* Returns the first finalized block in the first epoch greater than e.    *)
(*                                                                         *)
(* The mandatory block for epoch e is defined as the finalized block with  *)
(* the smallest height among all finalized blocks in epochs > e.           *)
(***************************************************************************)
\* @type: ($epoch) => $block;
findMandatoryBlock(e) ==
    LET 
        \* Set of finalized blocks in epoch greater than e.
        \* @type: Set($block);
        B == {b \in Blocks : epoch[b] > e /\ Finalized(b)}
    IN 
        CHOOSE b \in B : (\A c \in B : height[b] <= height[c])

(***************************************************************************)
(* Updates the session start (mandatory block) for node n iff:             *)
(*  - The current mandatory block m has a BEEFY Justification              *)
(*    (height[b] >= height[m]).                                            *)
(*  - The best GRANDPA finalized block g belongs to a higher epoch than    *)
(*    m (epoch[g] > epoch[m]).                                             *)
(*                                                                         *)
(* If both conditions hold, sessionStart[n] is updated to the first        *)
(* finalized block in the first epoch greater than m's epoch.              *)
(*                                                                         *)
(* Note: Parameters b and g must be passed explicitly rather than accessed *)
(* via bestBEEFY[n] and bestGRANDPA[n] because we want their primed        *)
(* (updated) values. Direct access would return stale values. Only one of  *)
(* b or g will be primed depending on which view was just updated, but the *)
(* operator cannot determine which without explicit parameters.            *)
(***************************************************************************)
updateSessionStart(n, b, g) ==
    LET 
        \* Current mandatory block for node n.
        \* @type: $block;
        m == sessionStart[n]
    IN
    IF 
        height[b] >= height[m] /\ epoch[g] > epoch[m]
    THEN
        sessionStart' = [sessionStart EXCEPT ![n] = findMandatoryBlock(epoch[m])]
    ELSE 
        sessionStart' = sessionStart

(***************************************************************************)
(* Updates the best GRANDPA finalized block for node n to block b iff:     *)
(*  - Node n is ready to receive a block (pc[n] = "Receive").              *)
(*  - Block b is GRANDPA finalized.                                        *)
(*  - Block b has a higher height than the current best GRANDPA block      *)
(*    tracked by node n.                                                   *)
(*                                                                         *)
(* If these conditions hold, then:                                         *)
(*  - The best GRANDPA block for node n is updated to block b.             *)
(*  - The program counter is set to "Vote" to indicate readiness to cast a *)
(*    vote.                                                                *)
(*  - The sessionStart (mandatory block) is updated if necessary.          *)
(***************************************************************************)
UpdateGRANDPAView(n, b) ==
    /\ pc[n] = "Receive"
    /\ Finalized(b)
    /\ height[b] > height[bestGRANDPA[n]]
    /\ bestGRANDPA' = [bestGRANDPA EXCEPT ![n] = b]
    /\ pc' = [pc EXCEPT ![n] = "Vote"]
    /\ updateSessionStart(n, bestBEEFY[n], b)
    /\ UNCHANGED <<round, bestBEEFY, mandatoryBlocks, votes, height, 
                    status, parent, epoch>>

(***************************************************************************)
(* Helper operator to remove stale rounds for node n up to and including   *)
(* round r by discarding all rounds with height ≤ r from the active set.   *)
(***************************************************************************)
removeStaleRounds(n, r) ==
    /\ round' = [round EXCEPT ![n] = @ \ 0..r]

(***************************************************************************)
(* Helper operator to add block b to the set of mandatory blocks for node  *)
(* n iff b equals the current sessionStart block (mandatory block).        *)
(***************************************************************************)
updateMandatorySet(n, b) ==
    LET 
        \* Current mandatory block for node n.
        \* @type: $block;
        m == sessionStart[n]
    IN 
    IF 
        m = b 
    THEN 
        mandatoryBlocks' = [mandatoryBlocks EXCEPT ![n]=@ \cup {b}]
    ELSE
        mandatoryBlocks' = mandatoryBlocks

(***************************************************************************)
(* Updates bestBEEFY for node n to block b iff:                            *)
(*  - Node n is ready to receive a block (pc[n] = "Receive"), or node n    *)
(*    is waiting to vote with a non-empty active round                     *)
(*    (pc[n] = "Vote" /\ round[n] /= {}). The second condition allows a    *)
(*    node to consume a justification proof that arrives for its current   *)
(*    round (or a later one), clearing the active round and unblocking     *)
(*    CastVote.                                                             *)
(*  - Block b is BEEFY Justified (which implies GRANDPA Finalized).        *)
(*  - Block b has a higher height than the current best BEEFY block        *)
(*    tracked by node n.                                                   *)
(*  - Block b does not exceed the height of the best GRANDPA block         *)
(*    tracked by node n (bestGRANDPA[n] ≥ b).                              *)
(*  - One of these conditions holds:                                       *)
(*      • Block b is the current mandatory block (sessionStart).           *)
(*      • The current mandatory block is already BEEFY Justified and       *)
(*        block b is in the same epoch as the mandatory block.             *)
(*                                                                         *)
(* If these conditions hold, then:                                         *)
(*  - The bestBEEFY for node n is updated to block b.                      *)
(*  - The program counter is set to "Vote" to check whether a new round    *)
(*    should be activated.                                                 *)
(*  - Stale rounds are removed from the active round set.                  *)
(*  - The sessionStart (mandatory block) is updated if necessary.          *)
(*  - Block b is added to the mandatory blocks set if it is mandatory.     *)
(*                                                                         *)
(* Note: If the current mandatory block does not have a BEEFY              *)
(* Justification, bestBEEFY will not be updated until the mandatory block  *)
(* receives one, regardless of whether blocks at higher heights are        *)
(* justified. In an actual implementation, the node would likely query     *)
(* other nodes to obtain the missing BEEFY Justification.                  *)
(***************************************************************************)
UpdateBEEFYView(n, b) ==
    LET
        \* Current mandatory block for node n.
        \* @type: $block;
        m == sessionStart[n]
    IN
    /\ (pc[n] = "Receive" \/ (pc[n] = "Vote" /\ round[n] /= {}))
    /\ Justified(b)
    /\ height[b] > height[bestBEEFY[n]]
    /\ height[bestGRANDPA[n]] >= height[b]
     \* The justified block $b$ is the current mandatory block $m$, or the
     \* mandatory block $m$ is already justified and block $b$ is in the same
     \* epoch as mandatory block $m$.
     /\ \/ b = m
        \/ /\ m \in mandatoryBlocks[n]
           /\ epoch[b] = epoch[m]
    /\ bestBEEFY' = [bestBEEFY EXCEPT ![n] = b]
    /\ pc' = [pc EXCEPT ![n] = "Vote"]
    /\ removeStaleRounds(n, height[b])
    /\ updateSessionStart(n, b, bestGRANDPA[n])
    /\ updateMandatorySet(n, b)
    /\ UNCHANGED <<bestGRANDPA, votes, height, status, parent, epoch>>

(***************************************************************************)
(* Returns the minimum of two numbers x and y.                             *)
(***************************************************************************)
Min(x, y) == IF x <= y THEN x ELSE y 

(***************************************************************************)
(* Returns the height of the next mandatory block for node n, if one       *)
(* exists:                                                                 *)
(*  - If the best GRANDPA block is in a higher epoch than the              *)
(*    sessionStart block, return the height of the first finalized block   *)
(*    in the first epoch greater than sessionStart's epoch.                *)
(*  - Otherwise, return Infinity (no next mandatory block exists yet).     *)
(*                                                                         *)
(* Note: This operator returns the height of the block, not the block      *)
(* itself.                                                                 *)
(***************************************************************************)
\* @type: ($node) => $height;
nextMandatoryBlock(n) == 
    LET 
        \* Current mandatory block for node n.
        \* @type: $block;
        m == sessionStart[n]
        \* Best GRANDPA block for node n.
        \* @type: $block;
        g == bestGRANDPA[n]
        \* Next mandatory block after m.
        \* @type: $block;
        e == findMandatoryBlock(epoch[m])
    IN
        IF epoch[g] > epoch[m] THEN height[e] ELSE Infinity

(***************************************************************************)
(* Returns the smallest power of two greater than or equal to x.           *)
(* This is a recursive function definition.                                *)
(*                                                                         *)
(* Examples:                                                               *)
(*   NextPowerOfTwo(4)  = 4   (4 is already a power of 2)                  *)
(*   NextPowerOfTwo(5)  = 8   (next power of 2 after 5)                    *)
(*   NextPowerOfTwo(10) = 16  (next power of 2 after 10)                   *)
(***************************************************************************)
NextPowerOfTwo[x \in Nat, y \in Nat] ==
    IF y >= x THEN y ELSE NextPowerOfTwo[x, y*2]

(***************************************************************************)
(* Computes the next round number r for node n and casts a vote if         *)
(* appropriate.                                                            *)
(*                                                                         *)
(* Computing r:                                                            *)
(*  - M = 1 iff the mandatory block in the current session is already      *)
(*    BEEFY-justified; otherwise M = 0.                                    *)
(*  - If M = 0 (mandatory block not BEEFY-justified):                      *)
(*      r := height of that mandatory block.                               *)
(*  - If M = 1 (mandatory block BEEFY-justified):                          *)
(*      r := Min(height(next mandatory block),                             *)
(*               height(bestBEEFY[n]) + NEXT_POWER_OF_TWO(x))              *)
(*      where x = (height(bestGRANDPA[n]) − height(bestBEEFY[n]) + 1)/2    *)
(*      If no next mandatory block exists, its height is Infinity.         *)
(*                                                                         *)
(* After r is chosen:                                                      *)
(*  - If r > height(bestGRANDPA[n]): no action is taken.                   *)
(*  - Otherwise:                                                           *)
(*      • Add r to the set of active rounds for node n.                    *)
(*      • Cast a vote for the finalized block at height r.                 *)
(*                                                                         *)
(* Reference:                                                              *)
(*   https://spec.polkadot.network/sect-finality#defn-beefy-round-number   *)
(***************************************************************************)
(***************************************************************************)
(* Helper operator that performs the actual vote for round r:              *)
(*  - If r <= height[bestGRANDPA[n]]:                                      *)
(*      • Add r to the set of active rounds for node n.                    *)
(*      • Cast a vote for the finalized block at height r.                 *)
(*  - Otherwise: no changes to round or votes.                             *)
(***************************************************************************)
castVote(n, r) ==
    IF r <= height[bestGRANDPA[n]]
    THEN
        /\ round' = [round EXCEPT ![n] = @ \cup {r}]
        /\ votes' = [b \in Blocks |-> 
            IF height[b] = r
            THEN votes[b] \cup {n}
            ELSE votes[b]]
    ELSE
        /\ votes' = votes
        /\ round' = round

(***************************************************************************)
(* Computes round number and votes when M = 0 (mandatory block not yet     *)
(* BEEFY-justified). The round number is simply the height of the          *)
(* mandatory block (sessionStart).                                         *)
(*                                                                         *)
(* Guard: height[bestBEEFY[n]] < height[sessionStart[n]]                   *)
(***************************************************************************)
VoteMandatory(n) ==
    /\ height[bestBEEFY[n]] < height[sessionStart[n]]
    /\ castVote(n, height[sessionStart[n]])

(***************************************************************************)
(* Computes round number and votes when M = 1 (mandatory block already     *)
(* BEEFY-justified). The round number is:                                  *)
(*   r := Min(nextMandatoryBlock(n),                                       *)
(*            height(bestBEEFY[n]) + NEXT_POWER_OF_TWO(x))                 *)
(*   where x = (height(bestGRANDPA[n]) - height(bestBEEFY[n]) + 1) / 2     *)
(*                                                                         *)
(* Guard: height[bestBEEFY[n]] >= height[sessionStart[n]]                  *)
(***************************************************************************)
VoteNonMandatory(n) ==
    LET
        \* @type: Int;
        x == ((height[bestGRANDPA[n]] - height[bestBEEFY[n]]) + 1) \div 2
        \* @type: $height;
        e == nextMandatoryBlock(n)
        \* @type: $height;
        r == Min(e, (height[bestBEEFY[n]] + NextPowerOfTwo[x, 1]))
    IN
    /\ height[bestBEEFY[n]] >= height[sessionStart[n]]
    /\ castVote(n, r)

(***************************************************************************)
(* Casts a vote for node n iff:                                            *)
(*  - Node n is at the "Vote" step (i.e., just received a BEEFY or         *)
(*    GRANDPA block).                                                      *)
(*  - Node n has no currently active round (round[n] = {}).                *)
(*    This enforces the single-active-round invariant: a new vote may      *)
(*    only be cast once the previous active round has been cleared by      *)
(*    receiving a BEEFY justification for that round or a later round.    *)
(*  - Either the mandatory block is not yet BEEFY-justified (M=0),         *)
(*    in which case the vote is for the mandatory block height, or the     *)
(*    mandatory block is already justified (M=1), in which case the vote   *)
(*    is for Min(nextMandatoryBlock, bestBEEFY + NextPowerOfTwo(x)).       *)
(*                                                                         *)
(* If these conditions hold, then:                                         *)
(*  - Node n casts a vote for the finalized block at the computed height.  *)
(*  - The round is added to the set of active rounds for node n.           *)
(*  - The program counter is set to "Receive" to signal the node is        *)
(*    ready to receive a new block.                                        *)
(***************************************************************************)
CastVote(n) ==
    /\ pc[n] = "Vote"
    /\ round[n] = {}
    /\ \/ VoteMandatory(n)
       \/ VoteNonMandatory(n)
    /\ pc' = [pc EXCEPT ![n] = "Receive"]
    /\ UNCHANGED <<bestGRANDPA, bestBEEFY, sessionStart, mandatoryBlocks,
                    height, status, parent, epoch>>

(***************************************************************************)
(* Models the behavior of a faulty node.                                   *)
(*  - A faulty node can vote for any block finalized at any time.          *)
(*                                                                         *)
(* Note: Faulty nodes may also choose to remain silent (not vote).         *)
(***************************************************************************)
FaultyStep == 
    /\ \E n \in FNodes : \E b \in Blocks : 
        /\ Finalized(b)
        /\ votes' = [votes EXCEPT ![b] = votes[b] \cup {n}]
    /\ UNCHANGED <<round,bestGRANDPA, bestBEEFY, sessionStart, pc,
                    mandatoryBlocks, height, status, parent, epoch>>

(***************************************************************************)
(* Environment actions model external events that affect the system:       *)
(*  - Propose(e): Propose a new block in epoch e.                          *)
(*  - UpdateBlock(b): Update a proposed block b's status to "Finalized".   *)
(***************************************************************************)
Environment ==
    \/ \E b, p \in Blocks : \E e \in Epochs : Propose(b, p, e)
    \*\/ \E b \in Blocks : UpdateBlock(b)

(***************************************************************************)
(* Correct node actions model the behavior of honest nodes:                *)
(*  - UpdateGRANDPAView(n, b): Node n receives a GRANDPA finalized block b.*)
(*  - UpdateBEEFYView(n, b): Node n receives a BEEFY Justified block b.    *)
(*  - CastVote(n): Node n casts a vote for a round if conditions are met.  *)
(***************************************************************************)
CorrectStep == 
    \E n \in CNodes : 
        \/ \E b \in Blocks :
            \/ UpdateGRANDPAView(n, b)
            \/ UpdateBEEFYView(n, b)
        \/ CastVote(n)

(***************************************************************************)
(* System actions combine correct node behavior and faulty node behavior:  *)
(*  - CorrectStep: Actions performed by honest nodes.                      *)
(*  - FaultyStep: Actions performed by faulty nodes.                       *)
(***************************************************************************)
System == 
    \/ CorrectStep
    \/ FaultyStep
    
(***************************************************************************)
(* The next-state relation combines environment and system actions.        *)
(***************************************************************************)
Next == Environment \/ System

(***************************************************************************)
(* Weak fairness constraints applied to the specification:                 *)
(*  - Propose(e): Every epoch e will eventually propose a block.           *)
(*  - CastVote(n): Every honest node n will eventually cast a vote when    *)
(*    conditions are met.                                                  *)
(*  - UpdateGRANDPAView(n, b): Every honest node n will eventually update  *)
(*    its GRANDPA view when a finalized block b is available.              *)
(*  - UpdateBEEFYView(n, b): Every honest node n will eventually update    *)
(*    its BEEFY view when a justified block b is available.                *)
(*                                                                         *)
(* Note: Faulty nodes have no fairness constraints as they may choose to   *)
(* remain silent or vote arbitrarily at any time.                          *)
(***************************************************************************)
L == 
    /\ \A b, p \in Blocks : \A e \in Epochs : WF_vars(Propose(b, p, e))
    \*/\ \A b \in Blocks : WF_vars(UpdateBlock(b))
    /\ \A n \in CNodes : WF_vars(CastVote(n))
    /\ \A n \in CNodes : \A b \in Blocks : 
            /\ SF_vars(UpdateGRANDPAView(n, b))
            /\ SF_vars(UpdateBEEFYView(n, b))

(***************************************************************************)
(* The overall specification of the BEEFY protocol.                        *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ L

(***************************************************************************)
(* Helper definition to check if a given block b is mandatory:             *)
(*  - Block b must be GRANDPA Finalized.                                   *)
(*  - There must not exist another block c such that:                      *)
(*       1. c has the same epoch as b.                                     *)
(*       2. c has a lower height than b.                                   *)
(*       3. c is GRANDPA Finalized.                                        *)
(***************************************************************************)
IsMandatory(b) ==
    /\ Finalized(b)
    /\ ~\E c \in Blocks : 
        /\ epoch[c] = epoch[b]
        /\ height[c] < height[b]
        /\ Finalized(c)

=============================================================================