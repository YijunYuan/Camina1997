/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ProP.Basic
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Countable towers of finite p-group quotients

A countably generated identity-neighborhood filter supplies a decreasing,
separating basis of open normal subgroups of p-power index. Inclusions give
continuous surjective homomorphisms between the corresponding finite quotients.
-/

@[expose] public section

open scoped Topology

namespace Camina1997.IsProPGroup

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]
  [IsProPGroup p G]

/-- A countably based pro-p group has a decreasing basis of open normal p-power-index subgroups. -/
theorem exists_antitone_openNormalBasis
    [Filter.IsCountablyGenerated (𝓝 (1 : G))] :
    ∃ N : ℕ → OpenNormalSubgroup G,
      (∀ n, ∃ k : ℕ, (N n).toSubgroup.index = p ^ k) ∧
      (𝓝 (1 : G)).HasAntitoneBasis (fun n => (N n : Set G)) :=
  (nhds_one_hasBasis (p := p) (G := G)).exists_antitone_subbasis

/-- The extracted set basis is antitone also as a sequence of open normal subgroups. -/
theorem antitone_of_openNormalBasis {N : ℕ → OpenNormalSubgroup G}
    (hN : (𝓝 (1 : G)).HasAntitoneBasis (fun n => (N n : Set G))) : Antitone N :=
  hN.antitone

/-- Any identity-neighborhood basis of open normal subgroups is cofinal among such subgroups. -/
theorem exists_le_of_openNormalBasis {N : ℕ → OpenNormalSubgroup G}
    (hN : (𝓝 (1 : G)).HasBasis (fun _ : ℕ => True) (fun n => (N n : Set G)))
    (M : OpenNormalSubgroup G) : ∃ n, N n ≤ M := by
  obtain ⟨n, _, hn⟩ := hN.mem_iff.mp M.toOpenSubgroup.mem_nhds_one
  exact ⟨n, hn⟩

/-- A Hausdorff identity-neighborhood basis separates group elements. -/
theorem iInf_eq_bot_of_openNormalBasis [T1Space G] {N : ℕ → OpenNormalSubgroup G}
    (hN : (𝓝 (1 : G)).HasBasis (fun _ : ℕ => True) (fun n => (N n : Set G))) :
    (⨅ n, (N n).toSubgroup) = ⊥ := by
  ext x
  simp only [Subgroup.mem_iInf, Subgroup.mem_bot]
  have hx := Set.ext_iff.mp (biInter_basis_nhds hN) x
  simp only [Set.mem_iInter, Set.mem_singleton_iff, forall_true_left] at hx
  exact hx

/-- Every nonidentity element eventually lies outside a decreasing open normal basis. -/
theorem eventually_not_mem_openNormalBasis [T1Space G] {N : ℕ → OpenNormalSubgroup G}
    (hN : (𝓝 (1 : G)).HasAntitoneBasis (fun n => (N n : Set G))) {x : G} (hx : x ≠ 1) :
    ∃ n, ∀ m, n ≤ m → x ∉ N m := by
  have hnot : ¬∀ n, x ∈ N n := by
    intro h
    have hm : x ∈ (⨅ n, (N n).toSubgroup) := Subgroup.mem_iInf.mpr h
    rw [iInf_eq_bot_of_openNormalBasis hN.toHasBasis] at hm
    exact hx hm
  obtain ⟨n, hn⟩ := not_forall.mp hnot
  exact ⟨n, fun m hnm hm => hn (hN.antitone hnm hm)⟩

include p in
/-- Each open normal quotient of a pro-p group is finite. -/
theorem finite_quotient (N : OpenNormalSubgroup G) : Finite (G ⧸ N.toSubgroup) :=
  inferInstanceAs (Finite (G ⧸ N.toOpenSubgroup.toSubgroup))

end Camina1997.IsProPGroup

namespace OpenNormalSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The continuous quotient projection associated to an open normal subgroup. -/
def quotientProjection (N : OpenNormalSubgroup G) : ContinuousMonoidHom G (G ⧸ N.toSubgroup) where
  toMonoidHom := QuotientGroup.mk' N.toSubgroup
  continuous_toFun := QuotientGroup.continuous_mk

@[simp]
theorem quotientProjection_apply (N : OpenNormalSubgroup G) (x : G) :
    N.quotientProjection x = QuotientGroup.mk x := rfl

theorem quotientProjection_surjective (N : OpenNormalSubgroup G) :
    Function.Surjective N.quotientProjection := QuotientGroup.mk_surjective

/-- Inclusion of open normal subgroups induces a continuous homomorphism of quotients. -/
def quotientTransition (N M : OpenNormalSubgroup G) (hNM : N ≤ M) :
    ContinuousMonoidHom (G ⧸ N.toSubgroup) (G ⧸ M.toSubgroup) where
  toMonoidHom := QuotientGroup.map N.toSubgroup M.toSubgroup (MonoidHom.id G) hNM
  continuous_toFun := (QuotientGroup.isQuotientMap_mk N.toSubgroup).continuous_iff.mpr
    QuotientGroup.continuous_mk

@[simp]
theorem quotientTransition_mk (N M : OpenNormalSubgroup G) (hNM : N ≤ M) (x : G) :
    N.quotientTransition M hNM (QuotientGroup.mk x) = QuotientGroup.mk x := rfl

/-- The quotient transition is surjective. -/
theorem quotientTransition_surjective (N M : OpenNormalSubgroup G) (hNM : N ≤ M) :
    Function.Surjective (N.quotientTransition M hNM) := by
  intro q
  induction q using Quotient.inductionOn with
  | h x => exact ⟨QuotientGroup.mk x, rfl⟩

@[simp]
theorem quotientTransition_comp_projection (N M : OpenNormalSubgroup G) (hNM : N ≤ M) :
    (N.quotientTransition M hNM).comp N.quotientProjection = M.quotientProjection := by
  ext x
  rfl

/-- The transition maps satisfy the inverse-system composition law. -/
theorem quotientTransition_comp (N M L : OpenNormalSubgroup G) (hNM : N ≤ M) (hML : M ≤ L) :
    (M.quotientTransition L hML).comp (N.quotientTransition M hNM) =
      N.quotientTransition L (hNM.trans hML) := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => rfl

@[simp]
theorem quotientTransition_self (N : OpenNormalSubgroup G) :
    N.quotientTransition N le_rfl = ContinuousMonoidHom.id (G ⧸ N.toSubgroup) := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => rfl

end OpenNormalSubgroup

namespace Camina1997.IsProPGroup

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]
  [IsProPGroup p G]

/-- The continuous diagonal map to a sequence of finite open-normal quotients. -/
def quotientDiagonal (N : ℕ → OpenNormalSubgroup G) :
    ContinuousMonoidHom G (∀ n, G ⧸ (N n).toSubgroup) where
  toFun x _ := QuotientGroup.mk x
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => QuotientGroup.continuous_mk

include p in
/-- A neighborhood basis makes the diagonal quotient map a closed embedding. -/
theorem isClosedEmbedding_quotientDiagonal (N : ℕ → OpenNormalSubgroup G)
    (hN : (𝓝 (1 : G)).HasBasis (fun _ : ℕ => True) (fun n => (N n : Set G))) :
    Topology.IsClosedEmbedding (quotientDiagonal N) := by
  let (n : ℕ) : DiscreteTopology (G ⧸ (N n).toSubgroup) :=
    inferInstanceAs (DiscreteTopology (G ⧸ (N n).toOpenSubgroup.toSubgroup))
  apply (quotientDiagonal N).continuous.isClosedEmbedding
  apply (MonoidHom.ker_eq_bot_iff (quotientDiagonal N).toMonoidHom).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxN : x ∈ (⨅ n, (N n).toSubgroup) := by
    apply Subgroup.mem_iInf.mpr
    intro n
    exact (QuotientGroup.eq_one_iff x).mp (congrFun hx n)
  simpa only [iInf_eq_bot_of_openNormalBasis hN, Subgroup.mem_bot] using hxN

/-- Countably based pro-p groups embed as closed subgroups of countable products
of finite p-groups. -/
theorem exists_closedEmbedding_quotient_product
    [Filter.IsCountablyGenerated (𝓝 (1 : G))] :
    ∃ N : ℕ → OpenNormalSubgroup G,
      (∀ n, Finite (G ⧸ (N n).toSubgroup)) ∧
      (∀ n, IsPGroup p (G ⧸ (N n).toSubgroup)) ∧
      Topology.IsClosedEmbedding (quotientDiagonal N) := by
  obtain ⟨N, _, hN⟩ := exists_antitone_openNormalBasis (p := p) (G := G)
  exact ⟨N, fun n => finite_quotient (p := p) (N n),
    fun n => isPGroup_quotient (p := p) (N n),
    isClosedEmbedding_quotientDiagonal (p := p) N hN.toHasBasis⟩

end Camina1997.IsProPGroup
