# Camina1997

Formalization project for Rachel Camina, *Subgroups of the Nottingham Group*,
Journal of Algebra **196** (1997), 101–113,
[doi:10.1006/jabr.1997.7082](https://doi.org/10.1006/jabr.1997.7082).

The goal is the introductory theorem, restated as Corollary 2 on printed
page 112: for each prime `p`, every countably based pro-`p` group admits a
continuous injective homomorphism into the Nottingham group over `F_p`,
which is a homeomorphism onto a closed subgroup.

## Current status

Workspace setup and the first Horizon task are complete. Run `0001` proved
the algebraic Nottingham group, its normalization API, coefficient formulas,
and automatic continuity for the `t`-adic topology. The configured build and
the axiom audit of all 24 named declarations passed at commit `13e2fe9`;
the audit found only Lean's standard axioms, with no `sorryAx` or added axioms.
An independent honesty review approved the bounded task's completion.

The [blueprint](blueprint/src/content.tex) has six verified nodes. The
unconditional universality theorem remains **unproved**. The topology and
finite quotients of the Nottingham group, the Laurent-series model bridge,
and the embedding theorems are separate outstanding obligations.

- Source library: [manifest](../references/manifest.yaml) and
  [verified paper](../references/camina1997/camina1997.pdf).
- Vision transcriptions: PDF pages 1–2 and 9–12. Printed page = PDF page + 100.
- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib: `1e75e9dd53d483fa01eff9ac7d4ea0472ce9d1fa`, pinned in Lake and Horizon.
- Completed task: `CAM-001`; next milestone: `CAMINA.1.2` (congruence subgroups,
  topology and finite quotients). The complete roadmap is under `CAMINA`.

## Proof route

1. Define the normalized automorphism group, filtration, topology and depth.
2. Prove the Artin–Schreier/Witt finite realization and ramification results.
3. Prove depth-preserving extension steps (Camina Theorem 4).
4. Establish the finitely generated case (Theorem 5), including continuity.
5. Establish the Lubotzky–Wilson theorem quoted as Theorem 6.
6. Compose embeddings and verify the full Corollary 2 and its dependency cone.

Original Witt and Lubotzky–Wilson sources still need retrieval and proof
audits. Camina also invokes *Analytic pro-p Groups*, Corollary 1.21(i), for
continuity; that input must be proved or replaced by a documented argument.
The finite case of the inverse-limit construction needs explicit treatment.
No cited theorem is accepted as a new Lean axiom.

## Working in Horizon

Run these commands from the workspace root, one directory above this file:

```sh
horizon roadmap list --focus CAMINA
horizon task show CAM-001 --json
horizon graph -p Camina1997 frontier
```

Run the kernel build from this project directory:

```sh
horizon --root .. check --json
```

To work on the next mathematical milestone, run this command in the foreground
from the workspace root (Horizon creates a task from the roadmap item):

```sh
horizon run CAMINA.1.2 --no-dashboard
```

The pilot uses Codex `gpt-6-astra` with explicit `xhigh` effort, one round,
one concurrent session, and session/run ceilings of 100,000 output tokens.
These are Horizon stop thresholds, not guaranteed exact token or monetary
caps. Agent-launched tasks/runs and GitHub issue synchronization are disabled.
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
