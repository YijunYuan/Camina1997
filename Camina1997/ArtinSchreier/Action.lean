/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Cyclic
public import Camina1997.Nottingham.LaurentAction

/-!
# Nottingham coordinates for actions on reduced Artin–Schreier fields

A weighted-order-preserving field action is transported through Laurent
coordinates and restricted to power series. Evaluation intertwines the resulting
action with the original one and transfers uniformizer displacement to depth.
-/

@[expose] public section

open Polynomial

namespace Camina1997.ArtinSchreier

variable {p : ℕ} [Fact p.Prime]
variable (γ : LaurentSeries (ZMod p)) (m : ℕ)
variable (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))

local notation "K" => LaurentSeries (ZMod p)
local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)
local notation "O" => weightedInteger (p := p) γ m hm hpm hγ
local notation "R" => PowerSeries (ZMod p)

variable {G : Type*} [Group G]

/-- Transport a field action to the Laurent coordinate determined by a uniformizer. -/
noncomputable def parameterAction (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (ρ : G →* (L ≃+* L)) :
    G →* (K ≃ₐ[ZMod p] K) where
  toFun g :=
    let e := (laurentParameterEquiv γ m hm hpm hγ π hπ).toRingEquiv
    let f := e.trans ((ρ g).trans e.symm)
    AlgEquiv.ofRingEquiv (f := f) (fun a =>
      DFunLike.congr_fun (RingHom.ext_zmod
        (f.toRingHom.comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) K)) a)
  map_one' := by
    ext x : 1
    change (laurentParameterEquiv γ m hm hpm hγ π hπ).symm
      (ρ 1 (laurentParameterEquiv γ m hm hpm hγ π hπ x)) = x
    rw [map_one]
    exact (laurentParameterEquiv γ m hm hpm hγ π hπ).symm_apply_apply x
  map_mul' g h := by
    ext x : 1
    change (laurentParameterEquiv γ m hm hpm hγ π hπ).symm
      (ρ (g * h) (laurentParameterEquiv γ m hm hpm hγ π hπ x)) =
      (laurentParameterEquiv γ m hm hpm hγ π hπ).symm
        (ρ g (laurentParameterEquiv γ m hm hpm hγ π hπ
          ((laurentParameterEquiv γ m hm hpm hγ π hπ).symm
            (ρ h (laurentParameterEquiv γ m hm hpm hγ π hπ x)))))
    rw [AlgEquiv.apply_symm_apply, map_mul]
    rfl

@[simp]
theorem laurentParameterEquiv_parameterAction (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (ρ : G →* (L ≃+* L)) (g : G) (x : K) :
    laurentParameterEquiv γ m hm hpm hγ π hπ
      (parameterAction γ m hm hpm hγ π hπ ρ g x) =
      ρ g (laurentParameterEquiv γ m hm hpm hγ π hπ x) :=
  (laurentParameterEquiv γ m hm hpm hγ π hπ).apply_symm_apply _

/-- A weighted-order-preserving action becomes an order-preserving Laurent action. -/
theorem orderTop_parameterAction (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x) (g : G) (x : K) :
    (parameterAction γ m hm hpm hγ π hπ ρ g x).orderTop = x.orderTop := by
  rw [← weightedOrder_laurentParameterEquiv γ m hm hpm hγ π hπ,
    laurentParameterEquiv_parameterAction, hρ, weightedOrder_laurentParameterEquiv]

/-- Conjugating an action into Laurent coordinates preserves and reflects faithfulness. -/
theorem parameterAction_injective_iff (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (ρ : G →* (L ≃+* L)) :
    Function.Injective (parameterAction γ m hm hpm hγ π hπ ρ) ↔ Function.Injective ρ := by
  constructor
  · intro h g g' he
    apply h
    ext x : 1
    apply (laurentParameterEquiv γ m hm hpm hγ π hπ).injective
    rw [laurentParameterEquiv_parameterAction, laurentParameterEquiv_parameterAction, he]
  · intro h g g' he
    apply h
    ext x : 1
    obtain ⟨y, rfl⟩ := (laurentParameterEquiv γ m hm hpm hγ π hπ).surjective x
    rw [← laurentParameterEquiv_parameterAction, ← laurentParameterEquiv_parameterAction, he]

/-- The power-series action in any chosen uniformizer of the reduced extension. -/
noncomputable def powerSeriesAction (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x) :
    G →* (R ≃ₐ[ZMod p] R) :=
  Nottingham.restrictLaurentAction (parameterAction γ m hm hpm hγ π hπ ρ)
    (orderTop_parameterAction γ m hm hpm hγ π hπ ρ hρ)

/-- Evaluation intertwines the power-series action with the original field action. -/
theorem powerSeriesEval_powerSeriesAction (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x) (g : G) (f : R) :
    (powerSeriesEval γ m hm hpm hγ π hπ
      (powerSeriesAction γ m hm hpm hγ π hπ ρ hρ g f) : L) =
      ρ g (powerSeriesEval γ m hm hpm hγ π hπ f : L) := by
  rw [← laurentParameterEquiv_algebraMap, ← laurentParameterEquiv_algebraMap]
  change laurentParameterEquiv γ m hm hpm hγ π hπ
      (Nottingham.restrictLaurentAction (parameterAction γ m hm hpm hγ π hπ ρ)
        (orderTop_parameterAction γ m hm hpm hγ π hπ ρ hρ) g f : K) = _
  rw [Nottingham.coe_restrictLaurentAction, laurentParameterEquiv_parameterAction]
  rfl

/-- Restricting the transported action preserves and reflects faithfulness. -/
theorem powerSeriesAction_injective_iff (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x) :
    Function.Injective (powerSeriesAction γ m hm hpm hγ π hπ ρ hρ) ↔
      Function.Injective ρ :=
  (Nottingham.restrictLaurentAction_injective_iff
    (parameterAction γ m hm hpm hγ π hπ ρ)
    (orderTop_parameterAction γ m hm hpm hγ π hπ ρ hρ)).trans
      (parameterAction_injective_iff γ m hm hpm hγ π hπ ρ)

/-- A finite uniformizer displacement becomes the same power-series displacement order. -/
theorem order_powerSeriesAction_sub (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x) (g : G) {n : ℕ}
    (hd : weightedOrder γ m (ρ g (π : L) - (π : L)) = (n : WithTop ℤ)) :
    (powerSeriesAction γ m hm hpm hγ π hπ ρ hρ g PowerSeries.X - PowerSeries.X).order =
      (n : ℕ∞) := by
  let f := powerSeriesAction γ m hm hpm hγ π hπ ρ hρ g PowerSeries.X - PowerSeries.X
  have he : (powerSeriesEval γ m hm hpm hγ π hπ f : L) =
      ρ g (π : L) - (π : L) := by
    simp [f, powerSeriesEval_powerSeriesAction]
  have hf : f ≠ 0 := by
    intro hf
    have hz : ρ g (π : L) - (π : L) = 0 := by simpa [hf] using he.symm
    rw [hz, weightedOrder_zero] at hd
    exact WithTop.coe_ne_top hd.symm
  have ho := weightedOrder_powerSeriesEval γ m hm hpm hγ π hπ hf
  rw [he, hd] at ho
  have hn : f.order.toNat = n := by exact_mod_cast ho.symm
  change f.order = _
  rw [← PowerSeries.coe_toNat_order hf, hn]

/-- The transported action specializes to the previously constructed translations. -/
theorem powerSeriesAction_eq_translationPowerSeries (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x) (g : G) (c : ZMod p)
    (he : ρ g = (translation γ c).toRingEquiv) :
    powerSeriesAction γ m hm hpm hγ π hπ ρ hρ g =
      translationPowerSeries γ m hm hpm hγ π hπ c := by
  ext f : 1
  apply powerSeriesEval_injective γ m hm hpm hγ π hπ
  apply Subtype.val_injective
  rw [powerSeriesEval_powerSeriesAction, powerSeriesEval_translationPowerSeries, he]
  rfl

/-- Every weighted-order-preserving p-group action gives a Nottingham action. -/
noncomputable def nottinghamAction (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (hG : IsPGroup p G) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x) : G →* Nottingham p :=
  Nottingham.ofPGroupAction hG (powerSeriesAction γ m hm hpm hγ π hπ ρ hρ)

/-- The Nottingham action is the original field action in the chosen power-series coordinates. -/
theorem powerSeriesEval_nottinghamAction (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (hG : IsPGroup p G) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x) (g : G) (f : R) :
    (powerSeriesEval γ m hm hpm hγ π hπ
      (nottinghamAction γ m hm hpm hγ π hπ hG ρ hρ g f) : L) =
      ρ g (powerSeriesEval γ m hm hpm hγ π hπ f : L) :=
  powerSeriesEval_powerSeriesAction γ m hm hpm hγ π hπ ρ hρ g f

/-- The Nottingham action preserves and reflects faithfulness of the field action. -/
theorem nottinghamAction_injective_iff (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (hG : IsPGroup p G) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x) :
    Function.Injective (nottinghamAction γ m hm hpm hγ π hπ hG ρ hρ) ↔
      Function.Injective ρ :=
  (Nottingham.ofPGroupAction_injective_iff hG
    (powerSeriesAction γ m hm hpm hγ π hπ ρ hρ)).trans
      (powerSeriesAction_injective_iff γ m hm hpm hγ π hπ ρ hρ)

/-- Uniformizer displacement gives the exact depth of the Nottingham action. -/
theorem depth_nottinghamAction (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (hG : IsPGroup p G) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x) (g : G) {n : ℕ}
    (hd : weightedOrder γ m (ρ g (π : L) - (π : L)) = ((n + 1 : ℕ) : WithTop ℤ)) :
    Nottingham.depth (nottinghamAction γ m hm hpm hγ π hπ hG ρ hρ g) = (n : ℕ∞) := by
  change (powerSeriesAction γ m hm hpm hγ π hπ ρ hρ g PowerSeries.X -
    PowerSeries.X).order - 1 = _
  rw [order_powerSeriesAction_sub γ m hm hpm hγ π hπ ρ hρ g hd]
  simp

/-- A finite faithful field action gives a closed topological Nottingham embedding. -/
theorem isClosedEmbedding_nottinghamAction [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (π : O) (hπ : weightedOrder γ m (π : L) = 1) (hG : IsPGroup p G)
    (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x)
    (hfaithful : Function.Injective ρ) :
    Topology.IsClosedEmbedding (nottinghamAction γ m hm hpm hγ π hπ hG ρ hρ) :=
  Nottingham.isClosedEmbedding_ofPGroupAction hG
    (powerSeriesAction γ m hm hpm hγ π hπ ρ hρ)
    ((powerSeriesAction_injective_iff γ m hm hpm hγ π hπ ρ hρ).mpr hfaithful)

end Camina1997.ArtinSchreier
