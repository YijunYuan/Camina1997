/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Topology
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.PGroup

/-!
# Power-series actions of p-groups

In characteristic p, an automorphism of p-power order has linear coefficient
one. Thus a p-group action on the power-series algebra canonically factors
through the normalized automorphisms. Over the prime field this gives an
actual homomorphism into Nottingham, preserving faithfulness.

Reference: Camina (1997), normalization on p. 102 and finite-group realization on p. 105.
-/

@[expose] public section

namespace PowerSeries

variable {k : Type*} [Field k]

/-- The action on the cotangent space is the linear coefficient of the new parameter. -/
noncomputable def linearCoeffHom : (k⟦X⟧ ≃ₐ[k] k⟦X⟧) →* k where
  toFun e := coeff 1 (e X)
  map_one' := by simp
  map_mul' e f := coeff_one_algEquiv e (f X)

@[simp] theorem linearCoeffHom_apply (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) :
    linearCoeffHom e = coeff 1 (e X) := rfl

/-- A power-series automorphism of p-power order is normalized in characteristic p. -/
theorem isNormalized_of_pow_prime_pow_eq_one {p n : ℕ} [Fact p.Prime] [CharP k p]
    (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (he : e ^ (p ^ n) = 1) : IsNormalized e := by
  have hc : linearCoeffHom e ^ (p ^ n) = 1 := by
    rw [← map_pow, he, map_one]
  apply (iterateFrobenius k p n).injective
  change linearCoeffHom e ^ (p ^ n) = 1 ^ (p ^ n)
  simpa using hc

/-- Every p-group action on a power-series algebra in characteristic p is normalized. -/
theorem isNormalized_of_isPGroup_action {p : ℕ} [Fact p.Prime] [CharP k p]
    {G : Type*} [Group G] (hG : IsPGroup p G)
    (ρ : G →* (k⟦X⟧ ≃ₐ[k] k⟦X⟧)) (g : G) : IsNormalized (ρ g) := by
  obtain ⟨n, hn⟩ := hG.exists_pow_pow_eq_one g
  apply isNormalized_of_pow_prime_pow_eq_one (n := n) (ρ g)
  rw [← map_pow, hn, map_one]

end PowerSeries

namespace Camina1997.Nottingham

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- The canonical Nottingham action obtained from a prime-field power-series action of a p-group. -/
noncomputable def ofPGroupAction (hG : IsPGroup p G)
    (ρ : G →* (PowerSeries (ZMod p) ≃ₐ[ZMod p] PowerSeries (ZMod p))) : G →* Nottingham p :=
  ρ.codRestrict (PowerSeries.normalizedAutSubgroup (ZMod p))
    (PowerSeries.isNormalized_of_isPGroup_action hG ρ)

@[simp] theorem ofPGroupAction_toAlgEquiv (hG : IsPGroup p G)
    (ρ : G →* (PowerSeries (ZMod p) ≃ₐ[ZMod p] PowerSeries (ZMod p))) (g : G) :
    (ofPGroupAction hG ρ g).toAlgEquiv = ρ g := rfl

@[simp] theorem ofPGroupAction_apply (hG : IsPGroup p G)
    (ρ : G →* (PowerSeries (ZMod p) ≃ₐ[ZMod p] PowerSeries (ZMod p)))
    (g : G) (f : PowerSeries (ZMod p)) : ofPGroupAction hG ρ g f = ρ g f := rfl

/-- Factoring the action into Nottingham preserves and reflects injectivity. -/
theorem ofPGroupAction_injective_iff (hG : IsPGroup p G)
    (ρ : G →* (PowerSeries (ZMod p) ≃ₐ[ZMod p] PowerSeries (ZMod p))) :
    Function.Injective (ofPGroupAction hG ρ) ↔ Function.Injective ρ := by
  constructor
  · intro h g h' he
    apply h
    exact Subtype.ext he
  · intro h g h' he
    exact h (congrArg Subtype.val he)

/-- Discrete p-group actions give continuous maps into the Nottingham congruence topology. -/
theorem continuous_ofPGroupAction [TopologicalSpace G] [DiscreteTopology G]
    (hG : IsPGroup p G)
    (ρ : G →* (PowerSeries (ZMod p) ≃ₐ[ZMod p] PowerSeries (ZMod p))) :
    Continuous (ofPGroupAction hG ρ) := continuous_of_discreteTopology

/-- The image of a finite p-group action is a closed subgroup of Nottingham. -/
theorem isClosed_range_ofPGroupAction [Finite G] (hG : IsPGroup p G)
    (ρ : G →* (PowerSeries (ZMod p) ≃ₐ[ZMod p] PowerSeries (ZMod p))) :
    IsClosed (Set.range (ofPGroupAction hG ρ)) := (Set.finite_range _).isClosed

/-- A faithful finite discrete action gives a closed topological embedding into Nottingham. -/
theorem isClosedEmbedding_ofPGroupAction [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (hG : IsPGroup p G)
    (ρ : G →* (PowerSeries (ZMod p) ≃ₐ[ZMod p] PowerSeries (ZMod p)))
    (hρ : Function.Injective ρ) : Topology.IsClosedEmbedding (ofPGroupAction hG ρ) :=
  (continuous_ofPGroupAction hG ρ).isClosedEmbedding
    ((ofPGroupAction_injective_iff hG ρ).mpr hρ)

end Camina1997.Nottingham
