/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Basic

/-!
# Congruence subgroups of the Nottingham group

The subgroups `Nottingham.congruenceSubgroup n` consist of automorphisms
fixing every power series modulo `X^(n+1)`. This agrees with the condition
on the image of `X` used by Camina (1997), p. 102.
-/

@[expose] public section

namespace PowerSeries

variable {k : Type*} [Field k]

/-- Algebra automorphisms preserve each power of the maximal ideal. -/
theorem X_pow_dvd_algEquiv (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) {n : ℕ} {f : k⟦X⟧}
    (h : X ^ n ∣ f) : X ^ n ∣ e f := by
  obtain ⟨u, rfl⟩ := h
  rw [map_mul, map_pow]
  exact dvd_mul_of_dvd_left
    (pow_dvd_pow_of_dvd (X_dvd_iff.mpr (constantCoeff_algEquiv_X e)) n) _

/-- Congruence of automorphisms on the parameter implies congruence on every series. -/
theorem X_pow_dvd_algEquiv_sub (e d : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (n : ℕ)
    (h : X ^ n ∣ e X - d X) (f : k⟦X⟧) : X ^ n ∣ e f - d f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    obtain ⟨u, hu⟩ := X_dvd_iff.mpr (constantCoeff_algEquiv_X d)
    have hn : X ^ n ∣ e X - d X := (pow_dvd_pow X (Nat.le_succ n)).trans h
    have hf := eq_X_mul_shift_add_const f
    obtain ⟨v, a, rfl⟩ : ∃ v : k⟦X⟧, ∃ a : k, f = X * v + C a := ⟨_, _, hf⟩
    have heq : e (X * v + C a) - d (X * v + C a) =
        (e X - d X) * e v + d X * (e v - d v) := by simp; ring
    rw [heq]
    apply dvd_add (dvd_mul_of_dvd_left h _) 
    rw [hu, pow_succ', mul_assoc]
    exact mul_dvd_mul_left X (dvd_mul_of_dvd_right (ih hn v) u)

end PowerSeries

namespace Camina1997.Nottingham

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The automorphisms acting trivially modulo `X^(n+1)`. At `n = 0` and `n = 1`
this is the whole Nottingham group. -/
def congruenceSubgroup (n : ℕ) : Subgroup (Nottingham p) where
  carrier := {g | ∀ f, X ^ (n + 1) ∣ g f - f}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh f
    have heq : (g * h) f - f = (g (h f) - h f) + (h f - f) := by
      rw [mul_apply]; ring
    rw [heq]
    exact dvd_add (hg (h f)) (hh f)
  inv_mem' := by
    intro g hg f
    have h := dvd_neg.mpr (hg (g⁻¹ f))
    simpa using h

theorem mem_congruenceSubgroup_iff (g : Nottingham p) (n : ℕ) :
    g ∈ congruenceSubgroup n ↔ X ^ (n + 1) ∣ g X - X := by
  constructor
  · exact fun h ↦ h X
  · intro h f
    exact X_pow_dvd_algEquiv_sub g.toAlgEquiv (AlgEquiv.refl) (n + 1) h f

instance congruenceSubgroup_normal (n : ℕ) : (congruenceSubgroup (p := p) n).Normal where
  conj_mem := by
    intro g hg h f
    have hd := X_pow_dvd_algEquiv h.toAlgEquiv (hg (h⁻¹ f))
    simpa [mul_apply, map_sub] using hd

theorem congruenceSubgroup_antitone : Antitone (congruenceSubgroup (p := p)) := by
  intro n m h g hg f
  exact (pow_dvd_pow X (Nat.add_le_add_right h 1)).trans (hg f)

@[simp]
theorem congruenceSubgroup_zero : congruenceSubgroup (p := p) 0 = ⊤ := by
  apply top_unique
  intro g _ f
  simp only [Nat.zero_add, pow_one]
  exact X_dvd_iff.mpr (by simp)

@[simp]
theorem congruenceSubgroup_one : congruenceSubgroup (p := p) 1 = ⊤ := by
  apply top_unique
  intro g _ f
  exact X_sq_dvd_sub g f

/-- The congruence filtration separates automorphisms. -/
theorem eq_one_of_mem_congruenceSubgroup {g : Nottingham p}
    (h : ∀ n, g ∈ congruenceSubgroup n) : g = 1 := by
  apply ext
  intro f
  apply sub_eq_zero.mp
  apply PowerSeries.ext
  intro n
  simpa using (X_pow_dvd_iff.mp (h n f) n (Nat.lt_succ_self n))

theorem iInf_congruenceSubgroup : (⨅ n, congruenceSubgroup (p := p) n) = ⊥ := by
  apply bot_unique
  intro g hg
  exact Subgroup.mem_bot.mpr (eq_one_of_mem_congruenceSubgroup (by simpa using hg))

/-- An automorphism of the Nottingham group is determined by its value on `X`. -/
theorem ext_X {g h : Nottingham p} (heq : g X = h X) : g = h := by
  apply ext
  intro f
  apply sub_eq_zero.mp
  apply PowerSeries.ext
  intro n
  have hd : X ^ (n + 1) ∣ g X - h X := by simp [heq]
  have hf := X_pow_dvd_algEquiv_sub g.toAlgEquiv h.toAlgEquiv (n + 1) hd f
  simpa using X_pow_dvd_iff.mp hf n (Nat.lt_succ_self n)

end Camina1997.Nottingham
