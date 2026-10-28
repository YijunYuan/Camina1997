/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Quotient
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Restriction of Artin–Schreier classes

Restriction is induced by the field inclusion. For a finite Galois extension,
its kernel is finite: roots of kernel classes give functions on the Galois
group with values among the finitely many roots of `X ^ p - X`; equality of
these functions makes the difference of the roots belong to the base field.

Reference: Camina (1997), proof of Theorem 4, p. 109.
-/

@[expose] public section

namespace Camina1997.ArtinSchreier

variable {p : ℕ} [Fact p.Prime]

section RingHom

variable {A B : Type*} [CommRing A] [CommRing B]
  [Module (ZMod p) A] [Module (ZMod p) B] [CharP A p] [CharP B p]

/-- A ring homomorphism induces restriction of Artin–Schreier classes. -/
def quotientMap (f : A →+* B) : ASQuotient p A →ₗ[ZMod p] ASQuotient p B :=
  (wpLinearMap p A).range.mapQ (wpLinearMap p B).range
    (f.toAddMonoidHom.toZModLinearMap p) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨f x, by simp⟩)

@[simp] theorem quotientMap_classMap (f : A →+* B) (x : A) :
    quotientMap (p := p) f (classMap p A x) = classMap p B (f x) := rfl

end RingHom

section Field

variable (p) (F K : Type*) [Field F] [Field K] [Algebra F K]
  [Module (ZMod p) F] [Module (ZMod p) K] [CharP F p] [CharP K p]

/-- Restriction along a field inclusion. -/
def restriction : ASQuotient p F →ₗ[ZMod p] ASQuotient p K :=
  quotientMap (algebraMap F K)

@[simp] theorem restriction_classMap (a : F) :
    restriction p F K (classMap p F a) = classMap p K (algebraMap F K a) := rfl

/-- Each class killed by restriction has a representative with an actual root upstairs. -/
theorem exists_root_of_mem_ker_restriction (q : (restriction p F K).ker) :
    ∃ z : F × K, classMap p F z.1 = q.val ∧
      z.2 ^ p - z.2 = algebraMap F K z.1 := by
  obtain ⟨a, ha⟩ := (wpLinearMap p F).range.mkQ_surjective q.val
  change classMap p F a = q.val at ha
  have hk : classMap p K (algebraMap F K a) = 0 := by
    rw [← restriction_classMap, ha]
    exact q.property
  obtain ⟨x, hx⟩ := (classMap_eq_zero_iff p K _).mp hk
  exact ⟨⟨a, x⟩, ha, hx⟩

/-- The kernel of the Artin–Schreier map is a finite set of polynomial roots. -/
instance finite_wpKernel : Finite (wpLinearMap p K).ker := by
  have hp := (Polynomial.monic_X_pow_sub_X_sub_C (p := p) (0 : K)).ne_zero
  have hf := Polynomial.finite_setOfPred_isRoot hp
  have hs : ((wpLinearMap p K).ker : Set K) =
      {x : K | (Polynomial.X ^ p - Polynomial.X - Polynomial.C (0 : K)).IsRoot x} := by
    ext x
    simp [LinearMap.mem_ker, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X]
  rw [← hs] at hf
  exact hf.to_subtype

variable [FiniteDimensional F K] [IsGalois F K]

/-- The restriction kernel injects into a finite set of Galois-difference functions. -/
theorem finite_ker_restriction : Finite (restriction p F K).ker := by
  classical
  let rootPair (q : (restriction p F K).ker) : F × K :=
    (exists_root_of_mem_ker_restriction p F K q).choose
  have hpair (q : (restriction p F K).ker) :
      classMap p F (rootPair q).1 = q.val ∧
      (rootPair q).2 ^ p - (rootPair q).2 = algebraMap F K (rootPair q).1 :=
    (exists_root_of_mem_ker_restriction p F K q).choose_spec
  let difference (q : (restriction p F K).ker) (g : K ≃ₐ[F] K) :
      (wpLinearMap p K).ker :=
    ⟨g (rootPair q).2 - (rootPair q).2, by
      change (g (rootPair q).2 - (rootPair q).2) ^ p -
        (g (rootPair q).2 - (rootPair q).2) = 0
      rw [sub_pow_char]
      have he := congrArg g (hpair q).2
      simp only [map_sub, map_pow, AlgEquiv.commutes] at he
      linear_combination he - (hpair q).2⟩
  apply Finite.of_injective difference
  intro q r h
  have hfix (g : K ≃ₐ[F] K) :
      g ((rootPair q).2 - (rootPair r).2) = (rootPair q).2 - (rootPair r).2 := by
    have he := congrArg (fun f => ((f g : (wpLinearMap p K).ker) : K)) h
    change g (rootPair q).2 - (rootPair q).2 =
      g (rootPair r).2 - (rootPair r).2 at he
    rw [map_sub]
    linear_combination he
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    ((rootPair q).2 - (rootPair r).2)).mpr hfix
  have hab : (rootPair q).1 - (rootPair r).1 = b ^ p - b := by
    apply (algebraMap F K).injective
    rw [map_sub, map_sub, map_pow, hb, sub_pow_char]
    linear_combination -(hpair q).2 + (hpair r).2
  apply Subtype.ext
  rw [← (hpair q).1, ← (hpair r).1]
  exact (Submodule.Quotient.eq _).mpr ⟨b, hab.symm⟩

/-- For a finite Galois extension, the restriction kernel is finite-dimensional. -/
theorem moduleFinite_ker_restriction : Module.Finite (ZMod p) (restriction p F K).ker := by
  let := finite_ker_restriction p F K
  exact Module.Finite.of_finite

/-- Infinite-dimensional Artin–Schreier quotients retain infinite-dimensional image in finite
Galois extensions. -/
theorem not_moduleFinite_range_restriction
    (hF : ¬Module.Finite (ZMod p) (ASQuotient p F)) :
    ¬Module.Finite (ZMod p) (restriction p F K).range := by
  intro h
  let := h
  let := moduleFinite_ker_restriction p F K
  let : Module.Finite (ZMod p) (ASQuotient p F ⧸ (restriction p F K).ker) :=
    Module.Finite.equiv (restriction p F K).quotKerEquivRange.symm
  exact hF (Module.Finite.of_submodule_quotient (restriction p F K).ker)

end Field

section Laurent

local notation "L" => LaurentSeries (ZMod p)

/-- Bounded reduced parameters form a finite set, since the coefficient field is finite. -/
theorem finite_set_reduced_orderTop_ge (B : ℕ) :
    Set.Finite {r : reducedSubmodule p |
      ((-(B : ℤ) : ℤ) : WithTop ℤ) ≤ (r : L).orderTop} := by
  classical
  let S := {r : reducedSubmodule p |
    ((-(B : ℤ) : ℤ) : WithTop ℤ) ≤ (r : L).orderTop}
  let f : S → (Fin (B + 1) → ZMod p) :=
    fun r i => (r.val : L).coeff (-(i.val : ℤ))
  have hf : Function.Injective f := by
    intro r s h
    apply Subtype.ext
    apply Subtype.ext
    ext i
    by_cases hi : 0 < i
    · rw [r.val.property.1 i hi, s.val.property.1 i hi]
    · by_cases hib : i < -(B : ℤ)
      · have hr : (i : WithTop ℤ) < (r.val : L).orderTop :=
          (WithTop.coe_lt_coe.mpr hib).trans_le r.property
        have hs : (i : WithTop ℤ) < (s.val : L).orderTop :=
          (WithTop.coe_lt_coe.mpr hib).trans_le s.property
        rw [HahnSeries.coeff_eq_zero_of_lt_orderTop hr,
          HahnSeries.coeff_eq_zero_of_lt_orderTop hs]
      · have he : -(i.natAbs : ℤ) = i := by
          rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hi), neg_neg]
        have hn : i.natAbs < B + 1 := by
          have : (i.natAbs : ℤ) = -i := by omega
          omega
        have hc := congrFun h ⟨i.natAbs, hn⟩
        change (r.val : L).coeff (-(i.natAbs : ℤ)) =
          (s.val : L).coeff (-(i.natAbs : ℤ)) at hc
        rwa [he] at hc
  have : Finite S := Finite.of_injective f hf
  exact Set.toFinite S

/-- Every coset of an infinite-dimensional quotient subspace contains reduced parameters of
arbitrarily large pole order. -/
theorem exists_reduced_pole_lt_in_coset
    (U : Submodule (ZMod p) (ASQuotient p L)) (hU : ¬Module.Finite (ZMod p) U)
    (q : ASQuotient p L) (B : ℕ) :
    ∃ r : reducedSubmodule p, classMap p L (r : L) - q ∈ U ∧
      (r : L).orderTop < ((-(B : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  by_contra h
  push Not at h
  let S := {r : reducedSubmodule p |
    ((-(B : ℤ) : ℤ) : WithTop ℤ) ≤ (r : L).orderTop}
  have hS : S.Finite := finite_set_reduced_orderTop_ge B
  let : Finite S := hS.to_subtype
  let f : U → S := fun u => ⟨(reducedQuotientEquiv (p := p)).symm (q + u.val), by
    apply h
    change reducedQuotientEquiv ((reducedQuotientEquiv (p := p)).symm (q + u.val)) - q ∈ U
    rw [LinearEquiv.apply_symm_apply, add_sub_cancel_left]
    exact u.property⟩
  have hf : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    apply add_left_cancel (a := q)
    apply (reducedQuotientEquiv (p := p)).symm.injective
    exact congrArg Subtype.val he
  let : Finite U := Finite.of_injective f hf
  exact hU Module.Finite.of_finite

/-- Every infinite-dimensional quotient subspace contains arbitrarily large reduced poles. -/
theorem exists_reduced_pole_lt_of_not_moduleFinite
    (U : Submodule (ZMod p) (ASQuotient p L)) (hU : ¬Module.Finite (ZMod p) U) (B : ℕ) :
    ∃ r : reducedSubmodule p, classMap p L (r : L) ∈ U ∧
      (r : L).orderTop < ((-(B : ℤ) : ℤ) : WithTop ℤ) := by
  simpa using exists_reduced_pole_lt_in_coset U hU 0 B

variable (F : Type*) [Field F] [Module (ZMod p) F] [CharP F p]
  [Algebra F (LaurentSeries (ZMod p))]
  [FiniteDimensional F (LaurentSeries (ZMod p))] [IsGalois F (LaurentSeries (ZMod p))]

/-- A parameter can be adjusted by a base-field element and an Artin–Schreier image to have
an arbitrarily deep reduced pole. -/
theorem exists_reduced_pole_adjustment
    (hF : ¬Module.Finite (ZMod p) (ASQuotient p F)) (γ : L) (B : ℕ) :
    ∃ (b : F) (μ r : L), IsReduced r ∧
      r = γ + algebraMap F L b - (μ ^ p - μ) ∧
      r.orderTop < ((-(B : ℤ) : ℤ) : WithTop ℤ) := by
  have hU := not_moduleFinite_range_restriction p F L hF
  obtain ⟨r, hr, hord⟩ := exists_reduced_pole_lt_in_coset
    (restriction p F L).range hU (classMap p L γ) B
  obtain ⟨q, hq⟩ := hr
  obtain ⟨b, hb⟩ := (wpLinearMap p F).range.mkQ_surjective q
  change classMap p F b = q at hb
  have hclass : classMap p L (γ + algebraMap F L b - (r : L)) = 0 := by
    rw [map_sub, map_add, ← restriction_classMap, hb, hq]
    abel
  obtain ⟨μ, hμ⟩ := (classMap_eq_zero_iff p L _).mp hclass
  refine ⟨b, μ, r, r.property, ?_, hord⟩
  linear_combination hμ

/-- The adjusted parameter has an explicit prime-to-p pole order beyond the prescribed bound. -/
theorem exists_reduced_pole_adjustment_order
    (hF : ¬Module.Finite (ZMod p) (ASQuotient p F)) (γ : L) (B : ℕ) :
    ∃ (b : F) (μ r : L) (m : ℕ), IsReduced r ∧
      r = γ + algebraMap F L b - (μ ^ p - μ) ∧ B < m ∧ ¬p ∣ m ∧
      r.orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨b, μ, r, hr, he, hord⟩ := exists_reduced_pole_adjustment F hF γ B
  rcases hr.eq_single_or_exists_pole with hc | ⟨m, _, hpm, hm⟩
  · have hnonneg : (0 : WithTop ℤ) ≤ r.orderTop := by
      rw [hc]
      exact HahnSeries.orderTop_single_le
    have hbound : ((-(B : ℤ) : ℤ) : WithTop ℤ) ≤ 0 := by
      exact_mod_cast neg_nonpos.mpr (Int.natCast_nonneg B)
    exact False.elim ((not_lt_of_ge (hbound.trans hnonneg)) hord)
  · refine ⟨b, μ, r, m, hr, he, ?_, hpm, hm⟩
    rw [hm] at hord
    have h : -(m : ℤ) < -(B : ℤ) := WithTop.coe_lt_coe.mp hord
    omega

end Laurent

end Camina1997.ArtinSchreier
