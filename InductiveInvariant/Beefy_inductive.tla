--------------------- MODULE Beefy_inductive --------------------------------
EXTENDS Beefy, typedefs

(***************************************************************************)
(* Invariants that constitute the inductive invariant                      *)
(***************************************************************************)

\* Blocks that are not finalized have default values.
NonProposed ==
    \A b \in Blocks :
        ~Finalized(b)
        =>
        /\ height[b] = -1
        /\ epoch[b] = -1
        /\ status[b] = "None"
        /\ parent[b] = b

\* The genesis block is properly initialized.
GenesisBlock ==
    /\ Finalized(gen)
    /\ height[gen] = 0
    /\ parent[gen] = gen
    /\ epoch[gen] = 0
    /\ votes[gen] = Nodes

\* Every finalized block (except genesis) has a finalized parent.
NonGenesisParentExists ==
    \A b \in Blocks :
        /\ Finalized(b)
        /\ height[b] > 0
        =>
        /\ ValidParent(parent[b], height[b], epoch[b])
        /\ Finalized(parent[b])

\* Each height has at most one finalized block (linear chain structure).
UniqueBlockHeights ==
    \A b1, b2 \in Blocks :
        /\ Finalized(b1)
        /\ Finalized(b2)
        /\ height[b1] = height[b2]
        => b1 = b2

\* For all honest nodes, bestGRANDPA is finalized, bestBEEFY is justified, and
\* bestGRANDPA is at least as high as bestBEEFY.
HonestFinalizedAndJustified ==
    \A n \in CNodes :
        /\ Finalized(bestGRANDPA[n])
        /\ Justified(bestBEEFY[n])
        /\ height[bestGRANDPA[n]] >= height[bestBEEFY[n]]

\* Set of mandatory blocks for each honest node should only contain mandatory blocks.
MandatorySets ==
    \A n \in CNodes :
        \A b \in mandatoryBlocks[n] :
            IsMandatory(b)

\* The set of active rounds is always between height of bestBEEFY and height of bestGRANDPA.
\* And vote exists for each active round.
ActiveRoundsBetweenBest ==
    \A n \in CNodes :
        \A r \in round[n] :
            /\ r > height[bestBEEFY[n]]
            /\ r <= height[bestGRANDPA[n]]
            /\ \E b \in Blocks : height[b] = r /\ n \in votes[b]

\* If an honest node has voted for a block, and the block height is greater than bestBEEFY
\* for that node, then the round must be in the active round set for that node.
VotesImplyActiveRounds ==
    \A n \in CNodes :
        \A b \in Blocks :
            /\ n \in votes[b]
            /\ height[b] > height[bestBEEFY[n]]
            => height[b] \in round[n]

\* No votes from the future from honest nodes.
NoFutureVotes ==
    \A b \in Blocks :
        \A n \in votes[b] :
            n \in CNodes => height[b] <= height[bestGRANDPA[n]] /\ Finalized(b)

\* For all correct nodes, all mandatory blocks up to and including bestBEEFY
\* must be justified and stored in mandatoryBlocks.
MandatoryBlocksJustifiedUpToBestBEEFY ==
    \A n \in CNodes :
        \A b \in Blocks :
            /\ IsMandatory(b)
            /\ height[b] <= height[bestBEEFY[n]]
            => Justified(b) /\ b \in mandatoryBlocks[n]

\* For all correct nodes, sessionStart must point to a mandatory block.
SessionStartPointsToMandatory ==
    \A n \in CNodes :
        IsMandatory(sessionStart[n])

\* For all honest nodes if sessionStart is not justified, then there are no active
\* rounds for a height greater than sessionStart.
ActiveRoundsAfterJustifiedSessionStart ==
    \A n \in CNodes :
        height[bestBEEFY[n]] < height[sessionStart[n]]
        =>
        \A r \in round[n] :
            r <= height[sessionStart[n]]

\* All earlier mandatory blocks than sessionStart must be justified and stored
\* in mandatoryBlocks.
MandatoryEarlierBlocksJustified ==
    \A n \in CNodes :
        \A b \in Blocks :
            /\ IsMandatory(b)
            /\ height[b] < height[sessionStart[n]]
            => 
            /\ Justified(b)
            /\ b \in mandatoryBlocks[n]

\* All blocks in mandatoryBlocks have height at most bestBEEFY.
MandatoryBlocksBelowBestBEEFY ==
    \A n \in CNodes :
        \A b \in mandatoryBlocks[n] :
            height[b] <= height[bestBEEFY[n]]

\* If sessionStart is justified for a node (bestBEEFY >= sessionStart), then
\* bestGRANDPA must be in the same epoch as sessionStart.
SessionStartJustifiedEpoch ==
    \A n \in CNodes :
        height[bestBEEFY[n]] >= height[sessionStart[n]]
        =>
        epoch[bestGRANDPA[n]] = epoch[sessionStart[n]]

\* Epochs are monotonically non-decreasing with block height along the chain.
EpochMonotone ==
    \A b1, b2 \in Blocks :
        /\ Finalized(b1)
        /\ Finalized(b2)
        /\ height[b1] <= height[b2]
        => epoch[b1] <= epoch[b2]

\* The finalized chain has no gaps: for every finalized block, every
\* height up to its height is occupied by a finalized block.
\* Only needed for TLAPS to verify the inductive invariant.
FinalizedChainComplete ==
    \A b \in Blocks :
        Finalized(b)
        =>
        \A h \in Nat :
            h <= height[b]
            => \E c \in Blocks : height[c] = h /\ Finalized(c)

(***************************************************************************)
(* The inductive invariant: conjunction of all invariant clauses above.    *)
(***************************************************************************)
IndInv ==
    /\ NonProposed
    /\ GenesisBlock
    /\ NonGenesisParentExists
    /\ UniqueBlockHeights
    /\ HonestFinalizedAndJustified
    /\ MandatorySets
    /\ ActiveRoundsBetweenBest
    /\ VotesImplyActiveRounds
    /\ NoFutureVotes
    /\ MandatoryBlocksJustifiedUpToBestBEEFY
    /\ SessionStartPointsToMandatory
    /\ ActiveRoundsAfterJustifiedSessionStart
    /\ MandatoryEarlierBlocksJustified
    /\ MandatoryBlocksBelowBestBEEFY
    /\ SessionStartJustifiedEpoch
    /\ EpochMonotone

(***************************************************************************)
(* IndInit is used as the --init predicate for the inductive step check.   *)
(* It asserts TypeOK together with IndInv, giving Apalache a symbolic      *)
(* starting state that already satisfies the full inductive invariant.     *)
(***************************************************************************)
IndInit ==
    /\ TypeOK
    /\ IndInv

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

\* Safety property: conjunction of key safety conditions.
Safe ==
    /\ PreviousMandatoryBlocksJustified
    /\ ActiveRoundMandatory

=============================================================================