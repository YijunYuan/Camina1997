/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.ProP
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# The Nottingham group as an inverse limit

The Nottingham group is isomorphic as a topological group to the inverse limit
of its finite congruence quotients. The isomorphism sends an automorphism to its
family of congruence classes.

Reference: Camina (1997), p. 102.
-/

@[expose] public section

namespace Camina1997.Nottingham

open CategoryTheory

variable {p : ℕ} [Fact p.Prime]

/-- The free coefficients exhibit the Nottingham group as a totally disconnected space. -/
instance instTotallyDisconnectedSpace : TotallyDisconnectedSpace (Nottingham p) :=
  (coefficientHomeomorph (p := p)).symm.totallyDisconnectedSpace

/-- The Nottingham group with its compact, totally disconnected group topology. -/
noncomputable def profiniteGrp (p : ℕ) [Fact p.Prime] : ProfiniteGrp :=
  ProfiniteGrp.of (Nottingham p)

/-- The congruence filtration is monotone when indexed by the reverse order on `ℕ`. -/
theorem openNormalCongruenceSubgroup_monotone :
    Monotone (fun n : ℕᵒᵈ ↦ openNormalCongruenceSubgroup (p := p) n) :=
  fun _ _ h ↦ congruenceSubgroup_antitone h

/-- The congruence chain as a diagram in the poset of open normal subgroups. -/
noncomputable def congruenceFunctor : ℕᵒᵈ ⥤ OpenNormalSubgroup (profiniteGrp p) :=
  openNormalCongruenceSubgroup_monotone.functor

/-- The congruence chain is coinitial among all open normal subgroups. -/
instance congruenceFunctor_initial : (congruenceFunctor (p := p)).Initial := by
  apply openNormalCongruenceSubgroup_monotone.initial_functor_iff.mpr
  intro N
  obtain ⟨n, hn⟩ := exists_openNormalCongruenceSubgroup_le N
  exact ⟨OrderDual.toDual n, hn⟩

/-- The inverse system of finite congruence quotients, with their discrete topologies. -/
noncomputable def congruenceQuotientDiagram : ℕᵒᵈ ⥤ ProfiniteGrp :=
  congruenceFunctor ⋙ ProfiniteGrp.diagram (profiniteGrp p)

/-- Each group in the congruence quotient diagram is a finite `p`-group. -/
theorem isPGroup_congruenceQuotientDiagram_obj (n : ℕᵒᵈ) :
    IsPGroup p ((congruenceQuotientDiagram (p := p)).obj n) :=
  isPGroup_quotient_congruenceSubgroup n

/-- The cone whose projections send an automorphism to its congruence classes. -/
noncomputable def congruenceLimitCone : Limits.Cone (congruenceQuotientDiagram (p := p)) :=
  (ProfiniteGrp.cone (profiniteGrp p)).whisker congruenceFunctor

/-- The Nottingham group is a limit of its finite congruence quotients. -/
noncomputable def isLimit_congruenceLimitCone :
    Limits.IsLimit (congruenceLimitCone (p := p)) :=
  (Functor.Initial.isLimitWhiskerEquiv congruenceFunctor
    (ProfiniteGrp.cone (profiniteGrp p))).symm (ProfiniteGrp.isLimitCone (profiniteGrp p))

/-- The subgroup of compatible congruence classes, with its inherited product topology. -/
noncomputable abbrev congruenceInverseLimit : ProfiniteGrp :=
  ProfiniteGrp.limit (congruenceQuotientDiagram (p := p))

/-- The Nottingham group and the compatible-tuple inverse limit are isomorphic. -/
noncomputable def congruenceLimitIso :
    profiniteGrp p ≅ congruenceInverseLimit (p := p) :=
  isLimit_congruenceLimitCone.conePointUniqueUpToIso
    (ProfiniteGrp.limitConeIsLimit congruenceQuotientDiagram)

/-- Every Nottingham automorphism is determined topologically and algebraically by its
compatible family of finite congruence classes. -/
noncomputable def congruenceLimitEquiv : Nottingham p ≃ₜ* congruenceInverseLimit (p := p) where
  toFun := (congruenceLimitIso (p := p)).hom
  invFun := (congruenceLimitIso (p := p)).inv
  left_inv := fun g ↦ ProfiniteGrp.inv_hom_apply (congruenceLimitIso (p := p)) g
  right_inv := fun g ↦ ProfiniteGrp.hom_inv_apply (congruenceLimitIso (p := p)) g
  map_mul' := (congruenceLimitIso (p := p)).hom.hom.map_mul'
  continuous_toFun := (congruenceLimitIso (p := p)).hom.hom.continuous_toFun
  continuous_invFun := (congruenceLimitIso (p := p)).inv.hom.continuous_toFun

/-- The inverse-limit isomorphism has the canonical quotient maps as coordinates. -/
@[simp]
theorem congruenceLimitEquiv_apply (g : Nottingham p) (n : ℕ) :
    (congruenceLimitEquiv g).val n = QuotientGroup.mk g := by
  exact congrArg (fun f : profiniteGrp p ⟶ (congruenceQuotientDiagram (p := p)).obj n ↦ f g)
    (Limits.IsLimit.conePointUniqueUpToIso_hom_comp
      (isLimit_congruenceLimitCone (p := p))
      (ProfiniteGrp.limitConeIsLimit congruenceQuotientDiagram) n)

/-- Every compatible family of congruence classes is represented by a unique
Nottingham automorphism. -/
theorem existsUnique_of_compatible_quotients
    (x : ∀ n : ℕ, Nottingham p ⧸ congruenceSubgroup n)
    (hx : ∀ m n (h : m ≤ n),
      QuotientGroup.map (congruenceSubgroup n) (congruenceSubgroup m)
        (MonoidHom.id (Nottingham p)) (congruenceSubgroup_antitone h) (x n) = x m) :
    ∃! g : Nottingham p, ∀ n, (QuotientGroup.mk g : Nottingham p ⧸ congruenceSubgroup n) =
      x n := by
  let y : congruenceInverseLimit (p := p) :=
    ⟨x, fun {_ _} f ↦ hx _ _ (leOfHom f)⟩
  obtain ⟨g, hg⟩ := (congruenceLimitEquiv (p := p)).surjective y
  have hg' : ∀ n, (QuotientGroup.mk g : Nottingham p ⧸ congruenceSubgroup n) = x n := by
    intro n
    exact (congruenceLimitEquiv_apply g n).symm.trans
      (congrArg (fun z : congruenceInverseLimit (p := p) ↦ z.val n) hg)
  refine ⟨g, hg', ?_⟩
  intro h hh
  apply (congruenceLimitEquiv (p := p)).injective
  apply ProfiniteGrp.limit_ext
  intro n
  exact (congruenceLimitEquiv_apply h n).trans
    ((hh n).trans ((hg' n).symm.trans (congruenceLimitEquiv_apply g n).symm))

end Camina1997.Nottingham
