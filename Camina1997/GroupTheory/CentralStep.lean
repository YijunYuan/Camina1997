/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Mathlib.GroupTheory.Sylow

/-!
# Central prime-order quotients of finite p-groups

A nontrivial finite p-group has a central subgroup of order p. Its quotient
is a strictly smaller p-group, supplying the induction step for Witt realization.
-/

@[expose] public section

namespace IsPGroup

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- A nontrivial finite p-group contains a central subgroup of order p. -/
theorem exists_central_subgroup_card_prime [Nontrivial G] (hG : IsPGroup p G) :
    ∃ N : Subgroup G, N ≤ Subgroup.center G ∧ Nat.card N = p := by
  let : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  obtain ⟨n, hn, hcard⟩ :=
    (hG.to_subgroup (Subgroup.center G)).nontrivial_iff_card.mp inferInstance
  have hdiv : p ∣ Nat.card (Subgroup.center G) :=
    hcard.symm ▸ dvd_pow_self p hn.ne'
  have hle : p ^ 1 ≤ Nat.card (Subgroup.center G) := by
    simpa only [pow_one] using Nat.le_of_dvd Nat.card_pos hdiv
  simpa only [pow_one] using
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card (Fact.out : p.Prime) hG hle

/-- Quotienting by a subgroup of prime order strictly decreases the order of a finite group. -/
theorem _root_.Subgroup.card_quotient_lt_of_card_eq_prime (N : Subgroup G) [N.Normal]
    (hN : Nat.card N = p) : Nat.card (G ⧸ N) < Nat.card G := by
  have hprod : Nat.card (G ⧸ N) * p = Nat.card G := by
    simpa only [Subgroup.index_eq_card, hN] using N.index_mul_card
  calc
    Nat.card (G ⧸ N) = Nat.card (G ⧸ N) * 1 := (Nat.mul_one _).symm
    _ < Nat.card (G ⧸ N) * p :=
      Nat.mul_lt_mul_of_pos_left (Fact.out : p.Prime).one_lt Nat.card_pos
    _ = Nat.card G := hprod

/-- The central order-p step gives a normal kernel and a strictly smaller p-group quotient. -/
theorem exists_central_prime_step [Nontrivial G] (hG : IsPGroup p G) :
    ∃ (N : Subgroup G) (hN : N.Normal),
      N ≤ Subgroup.center G ∧ Nat.card N = p ∧
      letI := hN
      IsPGroup p (G ⧸ N) ∧ Nat.card (G ⧸ N) < Nat.card G := by
  obtain ⟨N, hc, hcard⟩ := hG.exists_central_subgroup_card_prime
  let : N.Normal := Subgroup.normal_of_le_center hc
  exact ⟨N, inferInstance, hc, hcard, hG.to_quotient N,
    N.card_quotient_lt_of_card_eq_prime hcard⟩

end IsPGroup
