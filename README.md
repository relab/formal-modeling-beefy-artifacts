# BEEFY Protocol — Formal Specification

This repository contains TLA+ formal specifications and verification artifacts
for **BEEFY**, a justification layer protocol that provides compact proofs of
finality for light clients on Polkadot.

---

## Repository Structure

```
.
├── MultipleActiveRounds/     # Main spec from the paper
├── SingleActiveRound/        # Variant: at most one active round per node
└── InductiveInvariant/       # Inductive invariant for Apalache
```

### `MultipleActiveRounds/`

The canonical specification of the BEEFY protocol as described in the paper.
A node's `round` variable is a *set* of heights, so a node may participate in
several rounds simultaneously.

| File | Purpose |
|------|---------|
| `Beefy.tla` | Core protocol operators and transition relation |
| `typedefs.tla` | Apalache type aliases |
| `MC_Beefy.tla` | Model-checking harness with concrete constants, invariants, and liveness properties |
| `MC_Beefy_Safety.tla` | Thin wrapper — extends `MC_Beefy` for safety runs |
| `MC_Beefy_Liveness.tla` | Thin wrapper — extends `MC_Beefy` for liveness runs |

### `SingleActiveRound/`

A variant that naively enforces **at most one active round** per node by adding
a single guard `round[n] = {}` to `CastVote`. This is intentionally
**incomplete** and TLC will report a **deadlock**.

**How the deadlock arises — validators stuck on different rounds:**

1. Different correct nodes vote for different round heights (the round-number
   algorithm can legally produce different values depending on each node's
   local view of `bestGRANDPA` and `bestBEEFY`).
2. Each node's active round holds a different height, so no single round
   accumulates enough votes to form a quorum — no round ever becomes BEEFY
   Justified.
3. `UpdateBEEFYView` is guarded by `pc[n] = "Receive" \/ (pc[n] = "Vote" /\ round[n] /= {})`,
   so the action is syntactically enabled for nodes in `"Vote"` state with an
   active round. However, it also requires `Justified(b)` for some block `b`
   at a higher height than `bestBEEFY[n]` — a precondition that is never
   satisfied because no round reached quorum.
4. Nodes move to `pc = "Vote"` (via `UpdateGRANDPAView`) and cannot cast a new
   vote (`CastVote` is blocked by `round[n] /= {}`). The only escape —
   receiving a BEEFY justification — is permanently unavailable. All nodes are
   stuck: deadlock.

The purpose of this variant is to show that even with a mechanism for consuming
an incoming justification proof while waiting to vote, the system deadlocks if
validators happen to vote for different rounds and no justification is ever
produced.

| File | Purpose |
|------|---------|
| `Beefy.tla` | Protocol with single-active-round enforcement |
| `typedefs.tla` | Apalache type aliases |
| `MC_Beefy.tla` | Harness with `RoundsMaxOne` invariant |

### `InductiveInvariant/`

Contains the inductive invariant used to verify safety properties via
**Apalache** without bounding the number of steps.  
`Beefy.tla` here replaces the recursive `NextPowerOfTwo` function with a
finite `MC_NextPowerOfTwo` that Apalache can handle.

| File | Purpose |
|------|---------|
| `Beefy.tla` | Protocol adapted for Apalache (finite `NextPowerOfTwo`) |
| `Beefy_inductive.tla` | Inductive invariant clauses (`IndInv`, `IndInit`, `Safe`) |
| `Apa_Beefy_inductive.tla` | Top-level file with concrete `OVERRIDE_*` constants |
| `typedefs.tla` | Apalache type aliases |

---

## Prerequisites

| Tool | Notes |
|------|-------|
| Java 11+ | Required by TLC and Apalache |
| [`tla2tools.jar`](https://github.com/tlaplus/tlaplus/releases) | TLC model checker |
| [Apalache](https://github.com/informalsystems/apalache/releases) (≥ 0.44) | Symbolic model checker |

---

## Running TLC (Explicit-State Model Checking)

TLC requires a `.cfg` file that binds the abstract `CONSTANTS` to concrete
values defined in each `MC_*.tla` file.  Create the files below before running.

### `MultipleActiveRounds` — Safety

**`MultipleActiveRounds/MC_Beefy_Safety.cfg`**

```
SPECIFICATION MC_Spec

CONSTANTS
    CNodes  <- MC_CNodes
    FNodes  <- MC_FNodes
    Quorums <- MC_Quorums
    Blocks  <- MC_Blocks

SYMMETRY MC_Symmetry

INVARIANTS
    TypeOK
    SingleChain
    NoConflictingFinalizedBlocks
    NoConflictingJustifiedBlocks
    JustifiedBlockImpliesFinalized
    NodeAtRoundImpliesFinalizedBlockAtRound
    NoHonestNodeWithRoundGreaterThanBestFinalized
    HonestRoundImpliesMandatoryBlocksJustified
    AllPreviousMandatoryBlocksJustified
    PreviousMandatoryBlocksJustified
    ActiveRoundMandatory
    MandatorySet
    StaleRoundsRemoved
```

```bash
cd MultipleActiveRounds
java -jar /path/to/tla2tools.jar -config MC_Beefy_Safety.cfg MC_Beefy_Safety.tla
```

### `MultipleActiveRounds` — Liveness

**`MultipleActiveRounds/MC_Beefy_Liveness.cfg`**

```
SPECIFICATION MC_Spec

CONSTANTS
    CNodes  <- MC_CNodes
    FNodes  <- MC_FNodes
    Quorums <- MC_Quorums
    Blocks  <- MC_Blocks

PROPERTIES
    MandatoryBlocksJustified
    MandatoryBlocksReceived
    BlockEventuallyConfirmed
```

```bash
cd MultipleActiveRounds
java -jar /path/to/tla2tools.jar -config MC_Beefy_Liveness.cfg MC_Beefy_Liveness.tla
```

### `SingleActiveRound`

**`SingleActiveRound/MC_Beefy.cfg`**

```
SPECIFICATION MC_Spec

CONSTANTS
    CNodes  <- MC_CNodes
    FNodes  <- MC_FNodes
    Quorums <- MC_Quorums
    Blocks  <- MC_Blocks

INVARIANTS
    TypeOK
    RoundsMaxOne
    PreviousMandatoryBlocksJustified
    ActiveRoundMandatory

PROPERTIES
    MandatoryBlocksJustified
    BlockEventuallyConfirmed
```

```bash
cd SingleActiveRound
java -jar /path/to/tla2tools.jar -config MC_Beefy.cfg MC_Beefy.tla
```

---

## Running Apalache (Inductive Invariant Checking)

Apalache reads constant overrides directly from `Apa_Beefy_inductive.tla`
(`OVERRIDE_*` bindings). No extra `.cfg` file is needed.

Run all commands from the `InductiveInvariant/` directory.

### 1 — Type check

```bash
apalache-mc typecheck Apa_Beefy_inductive.tla
```

### 2 — Base case: `Init ⇒ IndInv`

Verifies that every initial state satisfies the inductive invariant.

```bash
apalache-mc check \
  --init=Init \
  --inv=IndInv \
  --next=Next \
  --length=0 \
  Apa_Beefy_inductive.tla
```

### 3 — Inductive step: `IndInv ∧ Next ⇒ IndInv′`

Verifies that one transition preserves the invariant.

```bash
apalache-mc check \
  --init=IndInit \
  --inv=IndInv \
  --next=Next \
  --length=1 \
  Apa_Beefy_inductive.tla
```

### 4 — Safety follows: `IndInv ⇒ Safe`

Verifies that the inductive invariant implies the safety property.

```bash
apalache-mc check \
  --init=IndInit \
  --inv=Safe \
  --next=Next \
  --length=0 \
  Apa_Beefy_inductive.tla
```

---

## Customising the Constants

All concrete values live in the `MC_Beefy.tla` file for each variant (and in
`Apa_Beefy_inductive.tla` for Apalache). Edit those files, then regenerate the
`.cfg` file if needed.

### Nodes and quorums

```tla
\* MultipleActiveRounds/MC_Beefy.tla  (identical layout in SingleActiveRound/)
CONSTANTS c1, c2, c3, f1   \* declare one CONSTANT per node

MC_CNodes  == {c1, c2, c3}
MC_FNodes  == {f1}
MC_Quorums == {{c1, c2, f1}, {c1, c3, f1}, {c2, c3, f1},
               {c1, c2, c3}, {c1, c2, c3, f1}}
```

For `n` total nodes tolerating `f` Byzantine faults, a quorum requires
`2f + 1` nodes. The quorum set must satisfy the intersection assumption in
`Beefy.tla`: any two quorums share at least one correct node.

> **Note:** Adding nodes grows the state space exponentially. Start with ≤ 4
> nodes and monitor memory/time before scaling up.

### Blocks

```tla
CONSTANTS b0, b1, b2, b3   \* declare one CONSTANT per block

MC_Blocks == {b0, b1, b2, b3}
```

For Apalache, also update the derived constants in
`InductiveInvariant/Apa_Beefy_inductive.tla`:

```tla
MCTBlocks   == 4               \* total number of blocks
MC_Infinity == MCTBlocks * 2
MC_Heights  == -1..(MCTBlocks - 1)
```

### Epoch range

```tla
MaxEpoch  == 2
MC_Epochs == -1..MaxEpoch
```

### Symmetry reduction (TLC safety only)

```tla
MC_Symmetry == Permutations(MC_CNodes)
```

Adding `SYMMETRY MC_Symmetry` to the `.cfg` file tells TLC to collapse
symmetric states, which can reduce the state space by a factor of `|CNodes|!`.

> **Important:** symmetry reduction is only sound for **safety** (invariant)
> checking. It must **not** be used when checking liveness (temporal)
> properties, as TLC's symmetry reduction is unsound for liveness and can
> produce false results.
