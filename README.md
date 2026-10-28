# Camina1997

Formalization project for Rachel Camina, *Subgroups of the Nottingham Group*,
Journal of Algebra **196** (1997), 101–113,
[doi:10.1006/jabr.1997.7082](https://doi.org/10.1006/jabr.1997.7082).

The goal is the introductory theorem, restated as Corollary 2 on printed
page 112: for each prime `p`, every countably based pro-`p` group admits a
continuous injective homomorphism into the Nottingham group over `F_p`,
which is a homeomorphism onto a closed subgroup.

## Current status

The Nottingham group, congruence topology, compactness, finite quotients,
depth, and Laurent-series automorphism correspondence are formalized.
The cyclic Artin–Schreier quotient, its Galois action, complete weighted
valuation, residue field, and topological Laurent coordinates are also proved.
The construction now gives actual cyclic Nottingham subgroups at every positive
prime-to-`p` depth. Unique reduced Artin–Schreier representatives and explicit
trace-one solutions of Witt's equations are formalized, together with the
semilinear automorphisms they induce on the concrete quotient.
These units passed serialized kernel builds, standard-axiom audits, and
independent honesty/source review.

The unconditional universality theorem remains **unproved**. Current work
builds the action of a given central extension from Witt's equations and the
Artin–Schreier quotient basis. The value-group index equals the cyclic extension degree.
Finite-group realization, depth-preserving lifts, and both infinite-group
embedding steps remain open in Lean.

- [Blueprint](blueprint/src/content.tex) and full roadmap: `CAMINA`.
- Source library: [manifest](../references/manifest.yaml), including Camina
  (1997), Witt (1936), and Lubotzky–Wilson (1984).
- Camina vision transcriptions: all 13 PDF pages; printed page = PDF page + 100.
- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib: `1e75e9dd53d483fa01eff9ac7d4ea0472ce9d1fa`, pinned in Lake and Horizon.
- Completed task: `CAM-001`; continuing task: `CAM-MAIN`, covering the entire
  theorem.

## Proof route

1. Define the normalized automorphism group, filtration, topology and depth.
2. Prove the Artin–Schreier/Witt finite realization and ramification results.
3. Prove depth-preserving extension steps (Camina Theorem 4).
4. Establish the finitely generated case (Theorem 5), including continuity.
5. Establish the Lubotzky–Wilson theorem quoted as Theorem 6.
6. Compose embeddings and verify the full Corollary 2 and its dependency cone.

The blueprint supplies detailed proofs for the chosen Witt and
Lubotzky–Wilson routes, with original-source references. Those arguments still
require Lean implementations and complete dependency audits. The continuity
and closedness of the final embeddings must be proved explicitly.
No cited theorem is accepted as a new Lean axiom.

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

The ongoing theorem task is managed by the user service
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
