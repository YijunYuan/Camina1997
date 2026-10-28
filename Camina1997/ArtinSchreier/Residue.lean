/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Valuation
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The residue field of a reduced Artin–Schreier extension

Every integral element is congruent to a unique constant modulo the positive
weighted-order ideal. This identifies the residue field with the coefficient field.
-/

@[expose] public section

open Polynomial

namespace Camina1997.ArtinSchreier

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]

local notation "K" => LaurentSeries k

variable (γ : LaurentSeries k) (m : ℕ)

local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)

private theorem repr_algebraMap (a : K) (i : Fin p) :
    (rootBasis (p := p) γ).repr (algebraMap K L a) i =
      if (⟨0, (Fact.out : p.Prime).pos⟩ : Fin p) = i then a else 0 := by
  have he : algebraMap K L a = a • rootBasis γ ⟨0, (Fact.out : p.Prime).pos⟩ := by
    simp [Algebra.smul_def]
  rw [he]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- A nonconstant root-basis term cannot have weighted order zero. -/
theorem termWeight_ne_zero_of_index_ne_zero (hpm : ¬p ∣ m) {i : Fin p}
    (hi : i ≠ ⟨0, (Fact.out : p.Prime).pos⟩) (a : K) :
    termWeight (p := p) m i a ≠ 0 := by
  intro he
  have ha : a ≠ 0 := by
    intro ha
    simp [ha] at he
  apply hi
  apply termWeight_eq_imp_index_eq hpm ha (one_ne_zero : (1 : K) ≠ 0)
  simpa [termWeight] using he

private theorem orderTop_sub_constant_pos {a : K} (ha : 0 ≤ a.orderTop) :
    0 < (a - HahnSeries.C (a.coeff 0)).orderTop := by
  have hc : (0 : WithTop ℤ) ≤ (HahnSeries.C (a.coeff 0) : K).orderTop := by
    by_cases h : a.coeff 0 = 0
    · simp [h]
    · change 0 ≤ (HahnSeries.single 0 (a.coeff 0) : K).orderTop
      rw [HahnSeries.orderTop_single h]
      exact le_rfl
  have hle := (le_min ha hc).trans
    (HahnSeries.min_orderTop_le_orderTop_sub (x := a) (y := HahnSeries.C (a.coeff 0)))
  apply lt_of_le_of_ne hle
  exact Ne.symm (HahnSeries.orderTop_ne_of_coeff_eq_zero (by simp))

/-- Every integral element differs from a coefficient-field constant by positive order. -/
theorem exists_constant_sub_weightedOrder_pos (hpm : ¬p ∣ m)
    {x : AdjoinRoot ((X : (LaurentSeries k)[X]) ^ p - X - C γ)}
    (hx : 0 ≤ weightedOrder (p := p) γ m x) :
    ∃ c : k, 0 < weightedOrder (p := p) γ m (x - algebraMap K L (HahnSeries.C c)) := by
  classical
  let z : Fin p := ⟨0, (Fact.out : p.Prime).pos⟩
  let a : K := (rootBasis γ).repr x z
  have ha : (0 : WithTop ℤ) ≤ a.orderTop := by
    have h := hx.trans (weightedOrder_le_term γ m x z)
    by_cases ha : a = 0
    · simp [ha]
    · change 0 ≤ termWeight (p := p) m z a at h
      rw [termWeight_of_ne_zero m z ha] at h
      have hi : (z : ℤ) = 0 := rfl
      rw [hi, mul_zero, sub_zero] at h
      have h' : (0 : ℤ) ≤ (p : ℤ) * a.order := by exact_mod_cast h
      have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero ha]
      exact_mod_cast (show (0 : ℤ) ≤ a.order by nlinarith)
  refine ⟨a.coeff 0, ?_⟩
  obtain ⟨i, hi⟩ := exists_termWeight_eq γ m (x - algebraMap K L (HahnSeries.C (a.coeff 0)))
  rw [hi, map_sub, Finsupp.sub_apply, repr_algebraMap]
  by_cases hiz : z = i
  · subst i
    simp only [show (⟨0, (Fact.out : p.Prime).pos⟩ : Fin p) = z from rfl, ite_true]
    change 0 < termWeight (p := p) m z (a - HahnSeries.C (a.coeff 0))
    have hpos := orderTop_sub_constant_pos ha
    by_cases hz : a - HahnSeries.C (a.coeff 0) = 0
    · rw [hz, termWeight_zero]
      exact WithTop.coe_lt_top 0
    · rw [termWeight_of_ne_zero m z hz]
      have hi : (z : ℤ) = 0 := rfl
      rw [hi, mul_zero, sub_zero]
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz] at hpos
      have hpos' : 0 < (a - HahnSeries.C (a.coeff 0)).order := by exact_mod_cast hpos
      exact_mod_cast mul_pos (show (0 : ℤ) < p by exact_mod_cast (Fact.out : p.Prime).pos) hpos'
  · have hiz' : (⟨0, (Fact.out : p.Prime).pos⟩ : Fin p) ≠ i := hiz
    rw [ite_eq_right hiz', sub_zero]
    exact lt_of_le_of_ne (hx.trans (weightedOrder_le_term γ m x i))
      (termWeight_ne_zero_of_index_ne_zero m hpm (Ne.symm hiz) _).symm

/-- Every nonzero coefficient-field constant has weighted order zero. -/
theorem weightedOrder_constant {c : k} (hc : c ≠ 0) :
    weightedOrder (p := p) γ m (algebraMap K L (HahnSeries.C c)) = 0 := by
  rw [weightedOrder_algebraMap]
  change p • (HahnSeries.single 0 c : K).orderTop = 0
  rw [HahnSeries.orderTop_single hc]
  simp

theorem weightedOrder_constant_nonneg (c : k) :
    0 ≤ weightedOrder (p := p) γ m (algebraMap K L (HahnSeries.C c)) := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (weightedOrder_constant γ m hc).ge

/-- Every integral element has a unique constant representative modulo positive order. -/
theorem exists_unique_constant_sub_weightedOrder_pos (hpm : ¬p ∣ m) {x : L}
    (hx : 0 ≤ weightedOrder γ m x) :
    ∃! c : k, 0 < weightedOrder γ m (x - algebraMap K L (HahnSeries.C c)) := by
  obtain ⟨c, hc⟩ := exists_constant_sub_weightedOrder_pos γ m hpm hx
  refine ⟨c, hc, ?_⟩
  intro d hd
  by_contra hdc
  have he : algebraMap K L (HahnSeries.C (d - c)) =
      (x - algebraMap K L (HahnSeries.C c)) + -(x - algebraMap K L (HahnSeries.C d)) := by
    simp only [map_sub]
    ring
  have hmin := min_weightedOrder_le_add γ m
    (x - algebraMap K L (HahnSeries.C c)) (-(x - algebraMap K L (HahnSeries.C d)))
  rw [weightedOrder_neg] at hmin
  have hpos := (lt_min hc hd).trans_le hmin
  rw [← he, weightedOrder_constant γ m (sub_ne_zero.mpr hdc)] at hpos
  exact lt_irrefl _ hpos

/-- The canonical valuation subring for the explicit weighted valuation. -/
noncomputable def weightedInteger (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) : Subring L :=
  (weightedValuation γ m hm hpm hγ).toValuation.integer

@[simp]
theorem mem_weightedInteger (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) (x : L) :
    x ∈ weightedInteger γ m hm hpm hγ ↔ 0 ≤ weightedOrder γ m x := Iff.rfl

/-- Coefficient constants lie in the valuation ring. -/
noncomputable def constantIntegerHom (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) :
    k →+* weightedInteger (p := p) γ m hm hpm hγ :=
  ((algebraMap K L).comp HahnSeries.C).codRestrict _
    (fun c => weightedOrder_constant_nonneg γ m c)

@[simp]
theorem coe_constantIntegerHom (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) (c : k) :
    (constantIntegerHom (p := p) γ m hm hpm hγ c : L) =
      algebraMap K L (HahnSeries.C c) := rfl

variable [CharP k p]

noncomputable instance weightedInteger_isLocalRing (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) :
    IsLocalRing (weightedInteger (p := p) γ m hm hpm hγ) := by
  let : Fact (Irreducible ((X : K[X]) ^ p - X - C γ)) :=
    ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm γ hγ⟩
  exact inferInstanceAs (IsLocalRing (weightedValuation γ m hm hpm hγ).toValuation.integer)

/-- Positive weighted order is exactly membership in the valuation ring's maximal ideal. -/
theorem mem_maximalIdeal_weightedInteger (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))
    (x : weightedInteger (p := p) γ m hm hpm hγ) :
    x ∈ IsLocalRing.maximalIdeal (weightedInteger γ m hm hpm hγ) ↔
      0 < weightedOrder γ m (x : L) := by
  let : Fact (Irreducible ((X : K[X]) ^ p - X - C γ)) :=
    ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm γ hγ⟩
  change ¬IsUnit x ↔ 0 < weightedOrder γ m (x : L)
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

/-- Reduction of coefficient-field constants into the canonical residue field. -/
noncomputable def residueConstantHom (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) :
    k →+* IsLocalRing.ResidueField (weightedInteger (p := p) γ m hm hpm hγ) :=
  (IsLocalRing.residue _).comp (constantIntegerHom γ m hm hpm hγ)

/-- Every residue class is represented by a coefficient-field constant. -/
theorem residueConstantHom_surjective (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) :
    Function.Surjective (residueConstantHom (p := p) γ m hm hpm hγ) := by
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hc⟩ := exists_constant_sub_weightedOrder_pos γ m hpm x.property
  refine ⟨c, ?_⟩
  change IsLocalRing.residue _ (constantIntegerHom γ m hm hpm hγ c) =
    IsLocalRing.residue _ x
  apply (sub_eq_zero.mp ?_).symm
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff,
    mem_maximalIdeal_weightedInteger]
  exact hc

/-- The residue field of the reduced Artin–Schreier extension is the coefficient field. -/
noncomputable def residueFieldEquiv (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) :
    k ≃+* IsLocalRing.ResidueField (weightedInteger (p := p) γ m hm hpm hγ) :=
  RingEquiv.ofBijective (residueConstantHom γ m hm hpm hγ)
    ⟨(residueConstantHom γ m hm hpm hγ).injective,
      residueConstantHom_surjective γ m hm hpm hγ⟩

@[simp]
theorem residueFieldEquiv_apply (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) (c : k) :
    residueFieldEquiv (p := p) γ m hm hpm hγ c =
      IsLocalRing.residue _ (constantIntegerHom γ m hm hpm hγ c) := rfl

end Camina1997.ArtinSchreier
