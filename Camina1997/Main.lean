/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.ProPEmbedding
public import Camina1997.LubotzkyWilson.Embedding

/-!
# Camina's countably based universality theorem

Every countably based pro-`p` group admits a continuous homomorphism into the
Nottingham group over the prime field which is a homeomorphism onto a closed
subgroup. The proof combines the Lubotzky–Wilson construction with Camina's
embedding theorem for topologically finitely generated pro-`p` groups.

Reference: Camina (1997), introductory theorem and Corollary 2.
-/

@[expose] public section

open scoped Topology

namespace Camina1997.Nottingham

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]
  [IsProPGroup p G] [Filter.IsCountablyGenerated (𝓝 (1 : G))]

/-- Camina's full countably based universality theorem: every countably based pro-`p` group
admits a continuous injective homomorphism into the Nottingham group which is a homeomorphism
onto a closed subgroup. -/
theorem exists_closedEmbedding :
    ∃ f : ContinuousMonoidHom G (Nottingham p), Topology.IsClosedEmbedding f := by
  obtain ⟨H, hgroup, htopology, hpro, hfg, e, he⟩ :=
    LubotzkyWilson.exists_topologicallyFG_proP_closedEmbedding (p := p) (G := G)
  let := hgroup
  let := htopology
  let := hpro
  obtain ⟨f, hf⟩ := exists_closedEmbedding_of_topologicallyFG (p := p) hfg
  exact ⟨f.comp e, hf.comp he⟩

end Camina1997.Nottingham
