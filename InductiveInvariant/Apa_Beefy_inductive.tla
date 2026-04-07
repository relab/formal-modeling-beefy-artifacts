--------------------- MODULE Apa_Beefy_inductive -----------------------------
EXTENDS Beefy, typedefs, Beefy_inductive

(***************************************************************************)
(* Model Checking Type Definitions                                         *)
(***************************************************************************)

\* Correct nodes.
MC_CNodes == {"c1", "c2", "c3"}
\* Faulty nodes.
MC_FNodes == {"f1"}
\* Set of quorums.
MC_Quorums == {{"c1", "c2", "f1"}, {"c1", "c3", "f1"}, {"c2", "c3", "f1"}, {"c1", "c2", "c3"}, {"c1", "c2", "c3", "f1"}}
\* Set of blocks.
MC_Blocks == {"b0", "b1", "b2", "b3"}
MCTBlocks == 4
MaxEpoch == 2
MC_Epochs == -1..MaxEpoch
MC_Heights == -1..(MCTBlocks - 1)
MC_Infinity == MCTBlocks * 2

(***************************************************************************)
(* Override Constants for Model Checking                                   *)
(***************************************************************************)
OVERRIDE_CNodes == MC_CNodes
OVERRIDE_FNodes == MC_FNodes
OVERRIDE_Quorums == MC_Quorums
OVERRIDE_Blocks == MC_Blocks
OVERRIDE_Epochs == MC_Epochs
OVERRIDE_Heights == MC_Heights
OVERRIDE_Infinity == MC_Infinity
OVERRIDE_TBlocks == MCTBlocks
OVERRIDE_gen == "b0"

=============================================================================   