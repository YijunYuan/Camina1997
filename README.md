# Camina1997

Lean formalization of Rachel Camina, *Subgroups of the Nottingham Group*,
Journal of Algebra **196** (1997), 101–113,
[doi:10.1006/jabr.1997.7082](https://doi.org/10.1006/jabr.1997.7082).

## Main theorem

For each prime `p`, every countably based pro-`p` group admits a continuous
injective homomorphism into the Nottingham group over `F_p`, which is a
homeomorphism onto a closed subgroup. This is the paper's introductory theorem,
restated as Corollary 2 on page 112.

The full theorem is
[`Camina1997.Nottingham.exists_closedEmbedding`](Camina1997/Main.lean).
It constructs a `ContinuousMonoidHom G (Nottingham p)` satisfying
`Topology.IsClosedEmbedding`. The Nottingham group is the normalized
power-series automorphism group with its congruence topology.

The theorem and its dependencies use only Lean's standard foundational axioms
`propext`, `Classical.choice`, and `Quot.sound`; there are no added mathematical
axioms or `sorryAx` dependencies.

## Proof route

1. Define the normalized automorphism group, filtration, topology and depth.
2. Prove the Artin–Schreier/Witt finite realization and ramification results.
3. Prove depth-preserving extension steps (Camina Theorem 4).
4. Establish the finitely generated case (Theorem 5), including continuity.
5. Construct a finitely generated pro-`p` group containing the given countably
   based group, using the Lubotzky–Wilson sparse wreath-product construction.
6. Compose the closed embeddings to obtain the full Corollary 2.

All six steps are implemented. The auxiliary Lubotzky–Wilson group is constructed
for each input group; the stronger source statement giving one universal
two-generator group is not needed for Camina's conclusion.

## Build and verify

- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib: `1e75e9dd53d483fa01eff9ac7d4ea0472ce9d1fa`, pinned in Lake.

From this repository, run:

```sh
lake build
```

To inspect the main theorem and its transitive axiom dependencies:

```sh
lake env lean --stdin <<'EOF'
import Camina1997
#print Camina1997.Nottingham.exists_closedEmbedding
#print axioms Camina1997.Nottingham.exists_closedEmbedding
EOF
```

## History

The formalization was developed with Archon Horizon. Project commits were
transplanted from its workspace ledger onto this repository's original history,
preserving their authors, timestamps, and messages. Blueprint, graph, and helper
directories were removed from the final source tree; their tracked contents
remain available in earlier commits.
