/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Finite
public import Camina1997.Nottingham.LaurentAction

/-!
# Finite p-groups embed in the Nottingham group

The totally ramified Galois realization supplies a faithful action on the
Laurent field preserving its order. Restriction to the valuation ring and
normalization of p-group actions give the Nottingham embedding.

Reference: Camina (1997), Theorem 3 (Leedham-Green and Weiss), p. 105.
-/

@[expose] public section

namespace Camina1997.Nottingham

variable {p : ℕ} [Fact p.Prime]
local notation "K" => LaurentSeries (ZMod p)

/-- Every finite p-group embeds into the Nottingham group over the prime field. -/
theorem exists_injective_hom_of_finite (G : Type*) [Group G] [Finite G]
    (hG : IsPGroup p G) :
    ∃ φ : G →* Nottingham p, Function.Injective φ := by
  obtain ⟨a, _, _, ρ, hval, _⟩ :=
    Witt.exists_laurent_galois_realization K (RingEquiv.refl K) G hG
  let := a
  let ψ : G →* (K ≃ₐ[ZMod p] K) :=
    { toFun := fun g => AlgEquiv.ofRingEquiv (f := (ρ g).toRingEquiv)
        (fun c => DFunLike.congr_fun (RingHom.ext_zmod
          ((ρ g).toRingHom.comp (algebraMap (ZMod p) K))
          (algebraMap (ZMod p) K)) c)
      map_one' := by
        ext x : 1
        exact DFunLike.congr_fun ρ.map_one x
      map_mul' := fun g h => by
        ext x : 1
        exact DFunLike.congr_fun (ρ.map_mul g h) x }
  have hψ : Function.Injective ψ := by
    intro g h he
    apply ρ.injective
    ext x : 1
    exact congrArg (fun e : K ≃ₐ[ZMod p] K => e x) he
  exact ⟨ofLaurentAction hG ψ hval,
    (ofLaurentAction_injective_iff hG ψ hval).mpr hψ⟩

/-- With its discrete topology, every finite p-group has a closed Nottingham embedding. -/
theorem exists_closedEmbedding_of_finite (G : Type*) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] (hG : IsPGroup p G) :
    ∃ φ : G →* Nottingham p, Continuous φ ∧ Topology.IsClosedEmbedding φ := by
  obtain ⟨φ, hφ⟩ := exists_injective_hom_of_finite G hG
  have hc : Continuous φ := continuous_of_discreteTopology
  exact ⟨φ, hc, hc.isClosedEmbedding hφ⟩

end Camina1997.Nottingham
