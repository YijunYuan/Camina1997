/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Parameters
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Order.Setoid.Basic

/-!
# Finite congruence quotients

The quotient of the Nottingham group by its `n`th congruence subgroup has
`p^(n-1)` elements, parametrized by the coefficients of degrees two through `n`.
Reference: Camina (1997), p. 102.
-/

@[expose] public section

namespace Camina1997.Nottingham

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The coefficients visible in the quotient modulo the `n`th congruence subgroup. -/
noncomputable def truncatedCoefficients (n : ℕ) (g : Nottingham p) : Fin (n - 1) → ZMod p :=
  fun i ↦ coeff (i.val + 2) (g X)

theorem truncatedCoefficients_surjective (n : ℕ) :
    Function.Surjective (truncatedCoefficients (p := p) n) := by
  intro a
  refine ⟨ofCoefficients (fun i ↦ if h : i < n - 1 then a ⟨i, h⟩ else 0), ?_⟩
  funext i
  simp [truncatedCoefficients, i.isLt, coeff_X]

theorem leftRel_congruenceSubgroup_iff (n : ℕ) (g h : Nottingham p) :
    QuotientGroup.leftRel (congruenceSubgroup n) g h ↔
      truncatedCoefficients n g = truncatedCoefficients n h := by
  rw [QuotientGroup.leftRel_apply, inv_mul_mem_congruenceSubgroup_iff_coeff]
  constructor
  · intro hgh
    funext i
    exact (hgh i i.isLt).symm
  · intro hgh i hi
    exact (congrFun hgh ⟨i, hi⟩).symm

/-- Congruence cosets are parametrized by a finite tuple of coefficients.
This is an equivalence of sets; the coefficient tuple does not have componentwise group law. -/
noncomputable def quotientCoefficientEquiv (n : ℕ) :
    (Nottingham p ⧸ congruenceSubgroup n) ≃ (Fin (n - 1) → ZMod p) :=
  (Quotient.congrRight (fun g h ↦ leftRel_congruenceSubgroup_iff n g h)).trans
    (Setoid.quotientKerEquivOfSurjective (truncatedCoefficients n)
      (truncatedCoefficients_surjective n))

instance finite_quotient (n : ℕ) : Finite (Nottingham p ⧸ congruenceSubgroup n) :=
  Finite.of_equiv (Fin (n - 1) → ZMod p) (quotientCoefficientEquiv n).symm

/-- The exact order of each finite congruence quotient. -/
theorem card_quotient (n : ℕ) :
    Nat.card (Nottingham p ⧸ congruenceSubgroup n) = p ^ (n - 1) := by
  rw [Nat.card_congr (quotientCoefficientEquiv n), Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem index_congruenceSubgroup (n : ℕ) :
    (congruenceSubgroup (p := p) n).index = p ^ (n - 1) := card_quotient n

end Camina1997.Nottingham
