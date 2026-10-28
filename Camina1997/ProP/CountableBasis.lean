/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ProP.Basic
public import Camina1997.ProP.FiniteGeneration
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Filter.CountablyGenerated

/-!
# Countable bases from topological finite generation

Finite permutation representations enumerate the open normal subgroups of a
topologically finitely generated compact group. In a pro-`p` group this gives a
countable neighborhood basis at the identity.
-/

@[expose] public section

open scoped Topology

namespace Camina1997

variable {G : Type*} [Group G] [TopologicalSpace G]

private def openNormalKernel {A : Type*} [Group A] [TopologicalSpace A]
    [DiscreteTopology A] (f : ContinuousMonoidHom G A) : OpenNormalSubgroup G where
  toSubgroup := f.toMonoidHom.ker
  isOpen' := f.continuous.isOpen_preimage _ (isOpen_discrete {1})

local instance (n : ℕ) : TopologicalSpace (Equiv.Perm (Fin n)) := ⊥
local instance (n : ℕ) : DiscreteTopology (Equiv.Perm (Fin n)) := ⟨rfl⟩

private theorem exists_perm_representation [IsTopologicalGroup G] [CompactSpace G]
    (N : OpenNormalSubgroup G) :
    ∃ n : ℕ, ∃ f : ContinuousMonoidHom G (Equiv.Perm (Fin n)),
      openNormalKernel f = N := by
  classical
  let Q := G ⧸ N.toSubgroup
  let : Finite Q := Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen
  let : Fintype Q := Fintype.ofFinite Q
  let : DiscreteTopology Q := QuotientGroup.discreteTopology N.isOpen
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let r : Q →* Equiv.Perm (Fin (Fintype.card Q)) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom Q Q)
  have hr : Function.Injective r := e.permCongrHom.injective.comp MulAction.toPerm_injective
  let f : ContinuousMonoidHom G (Equiv.Perm (Fin (Fintype.card Q))) :=
    { toMonoidHom := r.comp (QuotientGroup.mk' N.toSubgroup)
      continuous_toFun := (show Continuous r from continuous_of_discreteTopology).comp
        QuotientGroup.continuous_mk }
  refine ⟨Fintype.card Q, f, ?_⟩
  apply OpenNormalSubgroup.toSubgroup_injective
  ext g
  change r (QuotientGroup.mk' N.toSubgroup g) = 1 ↔ g ∈ N.toSubgroup
  rw [← map_one r, hr.eq_iff]
  exact QuotientGroup.eq_one_iff g

namespace TopologicallyFG

/-- A topologically finitely generated compact group has countably many open normal subgroups. -/
theorem countable_openNormalSubgroup [IsTopologicalGroup G] [CompactSpace G]
    (hG : TopologicallyFG G) : Countable (OpenNormalSubgroup G) := by
  let (n : ℕ) : Finite (ContinuousMonoidHom G (Equiv.Perm (Fin n))) :=
    hG.finite_continuousMonoidHom
  let k : (Σ n : ℕ, ContinuousMonoidHom G (Equiv.Perm (Fin n))) → OpenNormalSubgroup G :=
    fun f => openNormalKernel f.2
  have hk : Function.Surjective k := by
    intro N
    obtain ⟨n, f, hf⟩ := exists_perm_representation N
    exact ⟨⟨n, f⟩, hf⟩
  exact hk.countable

/-- A topologically finitely generated pro-`p` group has a countable identity neighborhood basis. -/
theorem isCountablyGenerated_nhds_one {p : ℕ} [Fact p.Prime] [IsProPGroup p G]
    (hG : TopologicallyFG G) : Filter.IsCountablyGenerated (𝓝 (1 : G)) := by
  let := hG.countable_openNormalSubgroup
  exact (IsProPGroup.nhds_one_hasBasis (p := p) (G := G)).isCountablyGenerated

end TopologicallyFG

end Camina1997
