/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Galois
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Lifting a surjection with prime-order kernel

A group of order p is identified with the additive prime field. This supplies
the exact-sequence interface consumed by the constructed Galois lift.
-/

@[expose] public section

namespace GroupExtension

variable {N E G : Type*} [Group N] [Group E] [Group G]

/-- Present a surjection as a group extension using an isomorphism onto its kernel. -/
noncomputable def ofSurjectiveKernelEquiv (q : E →* G) (hq : Function.Surjective q)
    (ι : N ≃* q.ker) : GroupExtension N E G where
  inl := q.ker.subtype.comp ι.toMonoidHom
  rightHom := q
  inl_injective := Subtype.val_injective.comp ι.injective
  range_inl_eq_ker_rightHom := by
    ext e
    constructor
    · rintro ⟨n, rfl⟩
      exact (ι n).property
    · intro he
      obtain ⟨n, hn⟩ := ι.surjective ⟨e, he⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  rightHom_surjective := hq

/-- A prime-order kernel admits the prime-field presentation required by Witt's formulas. -/
noncomputable def ofPrimeKernel {p : ℕ} [Fact p.Prime] (q : E →* G)
    (hq : Function.Surjective q) (hker : Nat.card q.ker = p) :
    GroupExtension (Multiplicative (ZMod p)) E G :=
  ofSurjectiveKernelEquiv q hq (mulEquivOfPrimeCardEq (by simp) hker)

@[simp]
theorem ofPrimeKernel_rightHom {p : ℕ} [Fact p.Prime] (q : E →* G)
    (hq : Function.Surjective q) (hker : Nat.card q.ker = p) :
    (ofPrimeKernel q hq hker).rightHom = q := rfl

end GroupExtension

namespace Camina1997.Witt

open Polynomial

variable {E F K : Type*} [Group E] [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [IsGalois F K] [Finite E]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- The full central Frattini lifting theorem starting from the original surjection and kernel. -/
theorem exists_galois_lift_of_prime_kernel (q : E →* (K ≃ₐ[F] K))
    (hq : Function.Surjective q) (hker : Nat.card q.ker = p)
    (hcentral : q.ker ≤ Subgroup.center E) (hfrattini : q.ker ≤ frattini E) :
    ∃ (γ : K) (hγ : ∀ β : K, β ^ p - β ≠ γ),
      letI : Fact (Irreducible (X ^ p - X - C γ)) :=
        ⟨Polynomial.irreducible_X_pow_sub_X_sub_C γ hγ⟩
      Module.finrank K (AdjoinRoot (X ^ p - X - C γ)) = p ∧
      IsGalois F (AdjoinRoot (X ^ p - X - C γ)) ∧
      ∃ ρ : E ≃* (AdjoinRoot (X ^ p - X - C γ) ≃ₐ[F]
        AdjoinRoot (X ^ p - X - C γ)),
        ∀ (e : E) (x : K), ρ e (algebraMap K _ x) = algebraMap K _ (q e x) := by
  let S := GroupExtension.ofPrimeKernel q hq hker
  have hr : S.inl.range = q.ker := S.range_inl_eq_ker_rightHom
  exact exists_galois_centralLift S (hr ▸ hcentral) (hr ▸ hfrattini)

end Camina1997.Witt
