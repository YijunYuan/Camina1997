/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.LaurentParameter
public import Camina1997.ArtinSchreier.Ramification

/-!
# The lower parameter in upper uniformizer coordinates

The base parameter has order p in the power-series coordinates of a reduced
Artin–Schreier extension. Evaluation transfers every finite displacement order.

Reference: Camina (1997), the hypothesis preceding Lemma 4, p. 106.
-/

@[expose] public section

open Polynomial

namespace Camina1997.ArtinSchreier

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
variable (γ : LaurentSeries k) (m : ℕ)
variable (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))

local notation "K" => LaurentSeries k
local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)
local notation "O" => weightedInteger (p := p) γ m hm hpm hγ

omit [CharP k p] in
/-- Any finite order computed after evaluation is the original power-series order. -/
theorem order_eq_of_weightedOrder_eval (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (f : PowerSeries k) (n : ℕ)
    (hf : weightedOrder γ m (powerSeriesEval γ m hm hpm hγ π hπ f : L) =
      (n : WithTop ℤ)) : f.order = (n : ℕ∞) := by
  have hf0 : f ≠ 0 := by
    intro h
    simp only [h, map_zero, ZeroMemClass.coe_zero, weightedOrder_zero] at hf
    exact WithTop.coe_ne_top hf.symm
  have ho := weightedOrder_powerSeriesEval γ m hm hpm hγ π hπ hf0
  rw [hf] at ho
  have hn : f.order.toNat = n := by exact_mod_cast ho.symm
  rw [← PowerSeries.coe_toNat_order hf0, hn]

/-- The original Laurent parameter, viewed as an integer of the extension. -/
noncomputable def baseParameterInteger : O :=
  ⟨algebraMap K L (HahnSeries.single 1 1), by
    rw [mem_weightedInteger, weightedOrder_algebraMap,
      HahnSeries.orderTop_single one_ne_zero]
    exact nsmul_nonneg zero_le_one p⟩

/-- The original parameter expressed in the upper power-series coordinate. -/
noncomputable def baseParameter (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) : PowerSeries k :=
  (powerSeriesEquiv γ m hm hpm hγ π hπ).symm (baseParameterInteger γ m hm hpm hγ)

/-- Evaluation identifies the lower parameter with its given inclusion in the extension. -/
theorem powerSeriesEval_baseParameter (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) :
    (powerSeriesEval γ m hm hpm hγ π hπ (baseParameter γ m hm hpm hγ π hπ) : L) =
      algebraMap K L (HahnSeries.single 1 1) := by
  exact congrArg Subtype.val
    ((powerSeriesEquiv γ m hm hpm hγ π hπ).apply_symm_apply
      (baseParameterInteger γ m hm hpm hγ))

/-- Total ramification makes the lower parameter start in degree p. -/
theorem order_baseParameter (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) :
    (baseParameter γ m hm hpm hγ π hπ).order = (p : ℕ∞) := by
  apply order_eq_of_weightedOrder_eval γ m hm hpm hγ π hπ
  rw [powerSeriesEval_baseParameter, weightedOrder_algebraMap,
    HahnSeries.orderTop_single one_ne_zero]
  simp

end Camina1997.ArtinSchreier
