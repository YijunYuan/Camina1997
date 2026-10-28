/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Frobenius
public import Camina1997.Nottingham.Ramification
public import Camina1997.Nottingham.Depth

/-!
# Comparing depth through a degree-p parameter

The canonical Frobenius decomposition turns the first coefficient whose exponent
is not divisible by p into an exact ramification comparison. A nontrivial
normalized automorphism fixing a parameter of order p also proves that parameter
is not a p-th power.

Reference: Camina (1997), Lemmas 4–5, pp. 106–107.
-/

@[expose] public section

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime]
local notation "R" => PowerSeries (ZMod p)

/-- The two displacement orders give a lower bound for an actual degree-p parameter. -/
theorem le_order_displacement_of_first_nondivisible
    (e : R ≃ₐ[ZMod p] R) (he : IsNormalized e) {T : R} {u n : ℕ}
    (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hT : T.order = (p : ℕ∞)) (hu : ¬p ∣ u) (hc : coeff u T ≠ 0)
    (hlt : ∀ i < u, ¬p ∣ i → coeff i T = 0) :
    min ((p * (n + 1) : ℕ) : ℕ∞) ((u + n : ℕ) : ℕ∞) ≤ (e T - T).order := by
  have h := le_order_displacement_of_frobenius_split e he hδ
    (order_frobeniusRootPart_of_order_eq_prime hT)
    (order_frobeniusRemainder hu hc hlt) ((ZMod.natCast_eq_zero_iff u p).not.mpr hu)
  simpa only [← eq_frobeniusRootPart_pow_add T] using h

/-- Distinct possible leading orders give the exact displacement of a degree-p parameter. -/
theorem order_displacement_of_first_nondivisible
    (e : R ≃ₐ[ZMod p] R) (he : IsNormalized e) {T : R} {u n : ℕ}
    (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hT : T.order = (p : ℕ∞)) (hu : ¬p ∣ u) (hc : coeff u T ≠ 0)
    (hlt : ∀ i < u, ¬p ∣ i → coeff i T = 0) (hne : p * (n + 1) ≠ u + n) :
    (e T - T).order = min ((p * (n + 1) : ℕ) : ℕ∞) ((u + n : ℕ) : ℕ∞) := by
  have h := order_displacement_of_frobenius_split e he hδ
    (order_frobeniusRootPart_of_order_eq_prime hT)
    (order_frobeniusRemainder hu hc hlt) ((ZMod.natCast_eq_zero_iff u p).not.mpr hu) hne
  simpa only [← eq_frobeniusRootPart_pow_add T] using h

/-- An automorphism fixing a degree-p parameter determines its first non-Frobenius term. -/
theorem first_exponent_eq_of_fixed_parameter
    (e : R ≃ₐ[ZMod p] R) (he : IsNormalized e) {T : R} {u n : ℕ}
    (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hT : T.order = (p : ℕ∞)) (hu : ¬p ∣ u) (hc : coeff u T ≠ 0)
    (hlt : ∀ i < u, ¬p ∣ i → coeff i T = 0) (hfix : e T = T) :
    u = n * (p - 1) + p := by
  exact first_exponent_eq_of_fixed_frobenius_split e he hδ
    (order_frobeniusRootPart_of_order_eq_prime hT)
    (order_frobeniusRemainder hu hc hlt) ((ZMod.natCast_eq_zero_iff u p).not.mpr hu)
    (by simpa only [← eq_frobeniusRootPart_pow_add T] using hfix)

/-- The depth is unchanged below the ramification break measured by the first non-Frobenius term. -/
theorem depth_eq_of_first_nondivisible
    (e : R ≃ₐ[ZMod p] R) (he : IsNormalized e) {T : R} {u n r d : ℕ}
    (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hT : T.order = (p : ℕ∞)) (hu : ¬p ∣ u) (hc : coeff u T ≠ 0)
    (hlt : ∀ i < u, ¬p ∣ i → coeff i T = 0)
    (hur : u = r * (p - 1) + p) (hrd : d < r)
    (hord : (e T - T).order = ((p * (d + 1) : ℕ) : ℕ∞)) : n = d := by
  exact depth_eq_of_frobenius_split e he hδ
    (order_frobeniusRootPart_of_order_eq_prime hT)
    (order_frobeniusRemainder hu hc hlt) ((ZMod.natCast_eq_zero_iff u p).not.mpr hu) hur hrd
    (by simpa only [← eq_frobeniusRootPart_pow_add T] using hord)

/-- A degree-p parameter fixed by a nontrivial normalized automorphism is not a p-th power. -/
theorem not_pow_prime_of_fixed_parameter
    (e : R ≃ₐ[ZMod p] R) (he : IsNormalized e) {T : R} {r : ℕ}
    (hδ : (e X - X).order = ((r + 1 : ℕ) : ℕ∞))
    (hT : T.order = (p : ℕ∞)) (hfix : e T = T) :
    ∀ A : R, A ^ p ≠ T := by
  let : CharP R p := charP_of_injective_algebraMap (algebraMap (ZMod p) R).injective p
  intro A hA
  have hB := (frobeniusRemainder_eq_zero_iff T).mpr ⟨A, hA⟩
  have hroot : T = frobeniusRootPart T ^ p := by
    simpa only [hB, add_zero] using eq_frobeniusRootPart_pow_add T
  have hzero : (e (frobeniusRootPart T) - frobeniusRootPart T) ^ p = 0 := by
    rw [sub_pow_char, ← map_pow, ← hroot, hfix, sub_self]
  have hz : e (frobeniusRootPart T) - frobeniusRootPart T = 0 :=
    eq_zero_of_pow_eq_zero hzero
  have ho := order_algEquiv_sub_of_order e he hδ
    (order_frobeniusRootPart_of_order_eq_prime hT) (by simp)
  rw [hz, order_zero] at ho
  exact ENat.top_ne_natCast _ ho

/-- A kernel automorphism supplies the break and eliminates the auxiliary first exponent. -/
theorem depth_eq_of_fixed_parameter
    (e τ : R ≃ₐ[ZMod p] R) (he : IsNormalized e) (hτ : IsNormalized τ)
    {T : R} {n r d : ℕ}
    (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hδτ : (τ X - X).order = ((r + 1 : ℕ) : ℕ∞))
    (hT : T.order = (p : ℕ∞)) (hfix : τ T = T) (hrd : d < r)
    (hord : (e T - T).order = ((p * (d + 1) : ℕ) : ℕ∞)) : n = d := by
  obtain ⟨u, hu, hc, hlt, _⟩ := exists_frobeniusRemainder_order
    (not_pow_prime_of_fixed_parameter τ hτ hδτ hT hfix)
  have hur := first_exponent_eq_of_fixed_parameter τ hτ hδτ hT hu hc hlt hfix
  exact depth_eq_of_first_nondivisible e he hδ hT hu hc hlt hur hrd hord

end PowerSeries

namespace Camina1997.Nottingham

open PowerSeries

variable {p : ℕ} [Fact p.Prime]
local notation "R" => PowerSeries (ZMod p)

/-- A finite Nottingham depth is the parameter displacement order minus one. -/
theorem order_sub_eq_of_depth_eq (g : Nottingham p) {n : ℕ}
    (hn : depth g = (n : ℕ∞)) : (g X - X).order = ((n + 1 : ℕ) : ℕ∞) := by
  unfold depth at hn
  cases ho : (g X - X).order with
  | top => simp [ho] at hn
  | coe m =>
    have hm : 2 ≤ m := by simpa [ho] using two_le_order_sub g
    have hmn : m - 1 = n := by
      rw [ho, show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, ← ENat.natCast_sub] at hn
      exact_mod_cast hn
    norm_cast
    omega

/-- A fixed degree-p parameter transfers depth below the depth of a kernel element. -/
theorem depth_eq_of_fixed_degree_prime_parameter (g τ : Nottingham p) {T : R} {r d : ℕ}
    (hτ : depth τ = (r : ℕ∞)) (hT : T.order = (p : ℕ∞)) (hfix : τ T = T)
    (hrd : d < r) (hord : (g T - T).order = ((p * (d + 1) : ℕ) : ℕ∞)) :
    depth g = (d : ℕ∞) := by
  have hg : g ≠ 1 := by
    intro he
    rw [he] at hord
    change (T - T).order = ((p * (d + 1) : ℕ) : ℕ∞) at hord
    rw [sub_self, order_zero] at hord
    exact ENat.top_ne_natCast _ hord
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ((depth_eq_top_iff g).not.mpr hg)
  have hnd : n = d := PowerSeries.depth_eq_of_fixed_parameter g.toAlgEquiv τ.toAlgEquiv
    g.property τ.property (order_sub_eq_of_depth_eq g hn.symm)
    (order_sub_eq_of_depth_eq τ hτ) hT hfix hrd hord
  rw [← hn, hnd]

end Camina1997.Nottingham
