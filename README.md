# Camina1997

Formalization project for Rachel Camina, *Subgroups of the Nottingham Group*,
Journal of Algebra **196** (1997), 101–113,
[doi:10.1006/jabr.1997.7082](https://doi.org/10.1006/jabr.1997.7082).

This project proves the introductory theorem, restated as Corollary 2 on printed
page 112: for each prime `p`, every countably based pro-`p` group admits a
continuous injective homomorphism into the Nottingham group over `F_p`,
which is a homeomorphism onto a closed subgroup.

## Current status

The full unconditional theorem is
[`Camina1997.Nottingham.exists_closedEmbedding`](Camina1997/Main.lean).
For every prime `p` and every pro-`p` group `G` with a countable neighborhood
basis at the identity, it constructs a `ContinuousMonoidHom G (Nottingham p)`
whose underlying map satisfies `Topology.IsClosedEmbedding`. This includes
injectivity and the homeomorphism onto a closed subgroup. The target is the
normalized power-series automorphism group with its congruence topology.

The configured build and the transitive axiom audit pass. The theorem and
its producers use only `propext`, `Classical.choice`, and `Quot.sound`;
there are no added mathematical axioms or `sorryAx` dependencies.

- [Blueprint](blueprint/src/content.tex) and full roadmap: `CAMINA`.
- Source library: [manifest](../references/manifest.yaml), including Camina
  (1997), Witt (1936), and Lubotzky–Wilson (1984).
- Camina vision transcriptions: all 13 PDF pages; printed page = PDF page + 100.
- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib: `1e75e9dd53d483fa01eff9ac7d4ea0472ce9d1fa`, pinned in Lake and Horizon.
- Horizon tasks: `CAM-001` (foundations) and `CAM-MAIN` (the entire theorem).

## Proof route

1. Define the normalized automorphism group, filtration, topology and depth.
2. Prove the Artin–Schreier/Witt finite realization and ramification results.
3. Prove depth-preserving extension steps (Camina Theorem 4).
4. Establish the finitely generated case (Theorem 5), including continuity.
5. Construct a finitely generated pro-`p` group containing the given countably
   based group, using the Lubotzky–Wilson sparse wreath-product construction.
6. Compose embeddings and verify the full Corollary 2 and its dependency cone.

All six steps are implemented. The blueprint supplies complete proofs with
original-source references. The auxiliary Lubotzky–Wilson group is constructed
for each input group; the stronger source statement giving one universal
two-generator group is not needed for Camina's conclusion. Continuity and
closedness are proved explicitly, and no cited theorem is accepted as a new
Lean axiom.

## Reproduce the verification

From this project directory, with the pinned Lean toolchain and Lake
dependencies available:

```sh
lake build
lake env lean scripts/CheckAxioms.lean
```

The audit script prints the exact main theorem and the transitive axioms of
the theorem and its main producers. Every axiom list contains only the three
standard foundational axioms listed above.

## Working in Horizon

Run these commands from the workspace root, one directory above this file:

```sh
horizon roadmap list --focus CAMINA
horizon task show CAM-MAIN --json
horizon graph -p Camina1997 frontier
```

Run the kernel build from this project directory:

```sh
horizon --root .. check --json
```

The theorem task has been managed by the user service
`camina-horizon-prover.service`. Check its status or stop it with:

```sh
systemctl --user status camina-horizon-prover
systemctl --user stop camina-horizon-prover
journalctl --user -u camina-horizon-prover
```

After that service has stopped, the same continuation can be run in the
foreground from the workspace root:

```sh
python3 scripts/continue_camina.py --run 0002
```

The continuing run uses Codex `gpt-6-astra` with explicit `xhigh` effort and
one concurrent session. At the user's request, **there is no local session,
run token, or cost ceiling** (`workspace.budget: {}`). Run `0002` originally
paused at 100,165 output tokens because of the former 100,000-token session
ceiling; continuation resumes the same run and preserves its progress.

The controller drives 50 rounds per batch and automatically resumes another
batch while `CAM-MAIN` remains unfinished. Completing a sub-milestone does
not complete this task; its objective is the full, unconditional theorem.
It exits when the task is done, or records an actual blocker, engine failure,
or external account limit. It does not blindly retry failures or override a
user stop. The service is independent of this chat but does not start
automatically after a reboot. Agent-launched extra tasks/runs and GitHub issue
synchronization are disabled.
The configured GitHub repository is `YijunYuan/Camina1997`.
The existing ChatGPT login supplies Codex authentication; `.env` has no active
keys and remains excluded from version control.

The live dashboard is at <http://127.0.0.1:8765>, managed by the transient
user service `camina-horizon-dashboard.service` for the current login/boot.

```sh
systemctl --user status camina-horizon-dashboard
systemctl --user stop camina-horizon-dashboard
journalctl --user -u camina-horizon-dashboard
```

After a reboot or after stopping the transient service, start a foreground
dashboard with `horizon dashboard --host 127.0.0.1 --port 8765` from the
workspace root.

Horizon commits source changes to `../.archon-horizon/vcs/workspace.git`.
The original project Git history and remote are preserved in `.git.disabled`;
they are not the active Horizon ledger. Inspect that history explicitly with
`git --git-dir=.git.disabled --work-tree=. log`. Nothing is pushed automatically.
