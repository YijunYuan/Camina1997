/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Pro-`p` groups

A pro-`p` group is a compact Hausdorff topological group with a neighborhood
basis at the identity consisting of open normal subgroups of finite `p`-power index.
This is the topological convention used in Camina (1997).
-/

@[expose] public section

open scoped Topology

namespace Camina1997

/-- A compact Hausdorff topological group with a basis of open normal subgroups
of `p`-power index. -/
class IsProPGroup (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [TopologicalSpace G] : Prop
    extends IsTopologicalGroup G, CompactSpace G, T2Space G where
  /-- Open normal subgroups of finite `p`-power index form an identity neighborhood basis. -/
  nhds_one_hasBasis : (𝓝 (1 : G)).HasBasis
    (fun N : OpenNormalSubgroup G ↦ ∃ n : ℕ, N.toSubgroup.index = p ^ n)
    (fun N ↦ (N : Set G))

namespace IsProPGroup

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]
  [IsProPGroup p G]

/-- Every open normal quotient of a pro-`p` group is a `p`-group. -/
theorem isPGroup_quotient (N : OpenNormalSubgroup G) : IsPGroup p (G ⧸ N.toSubgroup) := by
  obtain ⟨M, ⟨n, hn⟩, hMN⟩ :=
    (nhds_one_hasBasis (p := p) (G := G)).mem_iff.mp N.toOpenSubgroup.mem_nhds_one
  have hM : IsPGroup p (G ⧸ M.toSubgroup) := IsPGroup.of_card hn
  have hle : M.toSubgroup ≤ N.toSubgroup.comap (MonoidHom.id G) := hMN
  apply hM.of_surjective (QuotientGroup.map M.toSubgroup N.toSubgroup (MonoidHom.id G) hle)
  apply QuotientGroup.map_surjective_of_surjective
  intro q
  induction q using Quotient.inductionOn with
  | h g => exact ⟨g, rfl⟩

end IsProPGroup

end Camina1997
