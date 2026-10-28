/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Congruence
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Depth in the Nottingham group

Depth is the order of the parameter difference minus one. Its inequalities
are exactly membership in the congruence filtration, with infinite depth
precisely at the identity. Reference: Camina (1997), p. 102.
-/

@[expose] public section

namespace Camina1997.Nottingham

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The order of the parameter difference minus one, with infinite depth at the identity. -/
noncomputable def depth (g : Nottingham p) : ℕ∞ := (g X - X).order - 1

theorem two_le_order_sub (g : Nottingham p) : (2 : ℕ∞) ≤ (g X - X).order :=
  nat_le_order_iff.mpr (X_pow_dvd_iff.mp (X_sq_dvd_sub g X))

theorem mem_congruenceSubgroup_iff_le_depth (g : Nottingham p) (n : ℕ) :
    g ∈ congruenceSubgroup n ↔ (n : ℕ∞) ≤ depth g := by
  rw [mem_congruenceSubgroup_iff, X_pow_dvd_iff, ← nat_le_order_iff]
  have h2 := two_le_order_sub g
  unfold depth
  cases ho : (g X - X).order with
  | top => simp
  | coe m =>
    have hm : 2 ≤ m := by simpa [ho] using h2
    rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, ← ENat.natCast_sub]
    simp only [ENat.natCast_le_natCast]
    omega

theorem one_le_depth (g : Nottingham p) : 1 ≤ depth g :=
  (mem_congruenceSubgroup_iff_le_depth g 1).mp (by simp)

@[simp]
theorem depth_one : depth (1 : Nottingham p) = ⊤ := by simp [depth]

@[simp]
theorem depth_eq_top_iff (g : Nottingham p) : depth g = ⊤ ↔ g = 1 := by
  constructor
  · intro h
    apply eq_one_of_mem_congruenceSubgroup
    intro n
    exact (mem_congruenceSubgroup_iff_le_depth g n).mpr (by simp [h])
  · rintro rfl
    exact depth_one

theorem depth_eq_nat_iff (g : Nottingham p) (n : ℕ) :
    depth g = n ↔ g ∈ congruenceSubgroup n ∧ g ∉ congruenceSubgroup (n + 1) := by
  simp only [mem_congruenceSubgroup_iff_le_depth]
  cases hd : depth g with
  | top => simp
  | coe m => simp only [ENat.natCast_inj, ENat.natCast_le_natCast]; omega

@[simp]
theorem depth_inv (g : Nottingham p) : depth g⁻¹ = depth g := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  simp only [← mem_congruenceSubgroup_iff_le_depth, Subgroup.inv_mem_iff]

theorem min_depth_le_depth_mul (g h : Nottingham p) :
    min (depth g) (depth h) ≤ depth (g * h) := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  rw [le_min_iff] at hn
  simp only [← mem_congruenceSubgroup_iff_le_depth] at hn ⊢
  exact (congruenceSubgroup n).mul_mem hn.1 hn.2

end Camina1997.Nottingham
