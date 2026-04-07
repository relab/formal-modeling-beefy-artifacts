--------------------- MODULE MC_Beefy ----------------------------------------
EXTENDS Beefy, FiniteSets, TLC

(***************************************************************************)
(* Model Checking Constants                                                *)
(***************************************************************************)
-----------------------------------------------------------------------------
\* Nodes.
CONSTANTS c1, c2, c3, f1
\* Blocks.
CONSTANTS b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10

\* Correct nodes.
MC_CNodes == {c1, c2, c3}
\* Faulty nodes.
MC_FNodes == {f1}
\* Set of quorums.
MC_Quorums == {{c1, c2, f1}, {c1, c3, f1}, {c2, c3, f1}, {c1, c2, c3}, {c1, c2, c3, f1}}
\* Set of blocks.
MC_Blocks == {b0, b1, b2, b3}
\* Symmetry set for model checking.
MC_Symmetry == Permutations(MC_CNodes)
\* A large number to represent "infinity" for heights in the model.
MC_Infinity == Cardinality(MC_Blocks) * 2

MaxEpoch == 2
MC_Epochs == -1..MaxEpoch
MC_Heights == -1..(Cardinality(MC_Blocks) - 1)

(***************************************************************************)
(* Proposes a new block in epoch e iff:                                    *)
(*  - There exists at least one block b that has not been proposed yet.    *)
(*  - Block b (chosen from unproposed blocks) is not already proposed.     *)
(*  - Block b has a valid parent p (the block with maximum height among    *)
(*    all proposed blocks).                                                *)
(*  - The parent block satisfies the ValidParent predicate for height      *)
(*     h = height[p] + 1 and epoch e.                                      *)
(*                                                                         *)
(* The newly proposed block is immediately marked as "Finalized" to        *)
(* model GRANDPA finalization occurring simultaneously with proposal.      *)
(***************************************************************************)
MC_Propose(e) ==
    LET 
        \* Set of blocks that have not yet been proposed.
        \* @type: Set($block);
        B == {c \in Blocks : ~Proposed(c)}
        \* Parent block for the new proposed block.
        \* @type: $block;
        p == CHOOSE blk \in Blocks \ B : \A c \in Blocks : height[blk] >= height[c]
        \* New block to be proposed.
        \* @type: $block;
        b == CHOOSE blk \in B : TRUE
        \* Height for the new proposed block.
        \* @type: $height;
        h == height[p] + 1
    IN
    /\ B /= {}
    /\ ~Proposed(b)
    /\ ValidParent(p, h, e)
    /\ propose(b, p, h, e)
    /\ UNCHANGED <<round, bestBEEFY, bestGRANDPA, sessionStart, pc,
                    mandatoryBlocks, votes>>

MC_Next ==
    \/ \E e \in MC_Epochs : MC_Propose(e)
    \/ System

MC_L == 
    /\ \A e \in Epochs : WF_vars(MC_Propose(e))
    /\ \A n \in CNodes : WF_vars(CastVote(n))
    /\ \A n \in CNodes : \A b \in Blocks : 
            /\ WF_vars(UpdateGRANDPAView(n, b))
            /\ WF_vars(UpdateBEEFYView(n, b))

MC_Spec == Init /\ [][MC_Next]_vars /\ MC_L

(***************************************************************************)
(* Invariants (Safety)                                                     *)
(***************************************************************************)

(***************************************************************************)
(* Honest nodes should only store mandatory block in the mandatoryBlocks   *)
(* set that are actually BEEFY Justified.                                  *)
(***************************************************************************)
MandatorySet == 
    \A n \in CNodes : \A b \in mandatoryBlocks[n] : /\ IsMandatory(b)
                                                    /\ Justified(b)

(***************************************************************************)
(* All mandatory blocks should be less or equal to a nodes view of best    *)
(* BEEFY should be in the mandatory blocks set.                            *)
(***************************************************************************)
AllMandatoryBlocksStored ==
    \A n \in CNodes : \A b \in Blocks : 
        /\ IsMandatory(b)
        /\ height[b] <= height[bestBEEFY[n]]
        => b \in mandatoryBlocks[n]

(***************************************************************************)
(* All Proposed blocks are on a single chain.                              *)
(*  - If blocks b1 and b2 have the same height and both are Proposed, they *)
(*    must be the same block.                                              *)
(***************************************************************************)
SingleChain == 
    \A b_1, b_2 \in Blocks :
        /\ height[b_1] = height[b_2]
        /\ Proposed(b_1)
        /\ Proposed(b_2)
        => b_1 = b_2

(***************************************************************************)
(* All Proposed blocks form a valid chain.                                 *)
(* - Every proposed block must have a parent that is also Proposed.        *)
(* - Enforces parent-child consistency for proposed blocks.                *)
(***************************************************************************)
ProposedChain ==
    \A b \in Blocks :
        /\ Proposed(b)
        /\ height[b] > 0
        =>
         LET p == parent[b] IN 
            /\ Proposed(b)
            /\ height[p] = height[b] - 1

(***************************************************************************)
(* No two blocks have been GRANDPA Finalized on different chains.          *)
(* - If blocks b1 and b2 have the same height and both are Finalized,      *)
(*   they must be the same block.                                          *)
(* - This property depends on the underlying Finality Gadget.              *)
(***************************************************************************)
NoConflictingFinalizedBlocks == 
    \A b_1, b_2 \in Blocks : 
        /\ height[b_1] = height[b_2]
        /\ Finalized(b_1)
        /\ Finalized(b_2)
        => b_1 = b_2

(***************************************************************************)
(* All Finalized blocks form a valid chain.                                *)
(* - Every finalized block must have a parent that is also finalized.      *)
(* - Prevents finalized blocks from forming disconnected forks.            *)
(***************************************************************************)
FinalizedChain ==
    \A b \in Blocks :
        /\ Finalized(b)
        /\ height[b] > 0
        =>
         LET p == parent[b] IN 
            /\ Finalized(p)
            /\ height[p] = height[b] - 1

(***************************************************************************)
(* No two blocks have been Justified on different chains.                  *)
(* - If blocks b1 and b2 have the same height and both are justified, they *)
(*   must be the same block.                                               *)
(***************************************************************************)
NoConflictingJustifiedBlocks == 
    \A b_1, b_2 \in Blocks : 
        /\ height[b_1] = height[b_2]
        /\ Justified(b_1)
        /\ Justified(b_2)
        => b_1 = b_2

(***************************************************************************)
(* Only GRANDPA Finalized blocks can be BEEFY Justified.                   *)
(* - If a block is justified, it must also be finalized.                   *)
(***************************************************************************)
JustifiedBlockImpliesFinalized == 
    \A b \in Blocks : Justified(b) => Finalized(b)

(***************************************************************************)
(* For an honest round, all its active rounds should correspond to a       *)
(* Grandpa Finalized block with the same height.                           *)
(***************************************************************************)
NodeAtRoundImpliesFinalizedBlockAtRound ==
    \A n \in CNodes : \A r \in round[n] : \E b \in Blocks :
        /\ Finalized(b) 
        /\ r = height[b]

(***************************************************************************)
(* No honest node is on a round that is not GRANDPA Finalized.             *)
(* - An honest node cannot be on a round greater than the height of        *)
(*   its best GRANDPA Finalized block.                                     *)
(***************************************************************************)
NoHonestNodeWithRoundGreaterThanBestFinalized ==
    \A n \in CNodes : ~\E r \in round[n] : r > height[bestGRANDPA[n]]

(***************************************************************************)
(* If an honest node n is on round r, then all mandatory blocks with       *)
(* height less than r must have a BEEFY Justification.                     *)
(***************************************************************************)
HonestRoundImpliesMandatoryBlocksJustified ==
    \A n \in CNodes : \A r \in round[n] : \A b \in Blocks : 
        /\ IsMandatory(b)
        /\ height[b] < r
        => b \in mandatoryBlocks[n]

(***************************************************************************)
(* If a block has a BEEFY Justification b, then all mandatory blocks with  *)
(* height less or equal to b must have a BEEFY Justification.              *)
(***************************************************************************)
AllPreviousMandatoryBlocksJustified == 
    \A b \in Blocks : Justified(b) => \A c \in Blocks :
        /\ IsMandatory(c)
        /\ height[c] <= height[b]
        => Justified(c)

(*********************************************************************)
(* Check that all stale rounds are removed from set of active rounds *)
(*********************************************************************)
StaleRoundsRemoved ==
    \A n \in CNodes : \A r \in round[n] : 
        r > height[bestBEEFY[n]]

(***************************************************************************)
(* Safety Properties                                                       *)
(***************************************************************************)

\* Previous mandatory blocks are justified.
PreviousMandatoryBlocksJustified == 
    \A b \in Blocks : 
        Justified(b) 
        => 
        \A c \in Blocks :
            /\ IsMandatory(c)
            /\ height[c] <= height[b]
            => 
            Justified(c)

\* If a block is mandatory, and its height is less than an active round
\* for an honest node, then that block is in the mandatoryBlocks set
\* for that node.
ActiveRoundMandatory ==
    \A n \in CNodes : 
        \A r \in round[n] : 
            \A b \in Blocks : 
                /\ IsMandatory(b)
                /\ height[b] < r
                => b \in mandatoryBlocks[n]

(***************************************************************************)
(* Temporal Properties (Liveness)                                          *)
(***************************************************************************)

(***************************************************************************)
(* Eventually, all mandatory blocks should be Justified.                   *)
(*  - We use the leadsto (~>) operator which is defined as: [](F => <>G).  *)
(***************************************************************************)
MandatoryBlocksJustified ==
    \A b \in Blocks : IsMandatory(b) ~> Justified(b)

MandatoryBlocksReceived ==
    \A b \in Blocks : IsMandatory(b) /\ Justified(b)
        ~> \A n \in CNodes : b \in mandatoryBlocks[n]

BlockEventuallyConfirmed ==
    <>\E b \in Blocks : Justified(b) /\ b /= gen

=============================================================================