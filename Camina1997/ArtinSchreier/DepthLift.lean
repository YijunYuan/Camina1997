/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Action
public import Camina1997.ArtinSchreier.BaseParameter
public import Camina1997.Nottingham.DepthComparison

/-!
# Depth preservation in a reduced Artin–Schreier lift

The lower parameter has order p upstairs. A cyclic translation fixes it and
has depth equal to the reduced pole. The coefficient comparison therefore
preserves every lower depth below that pole for any compatible lifted action.

Reference: Camina (1997), Lemma 5 and Theorem 4, pp. 107–109.
-/

@[expose] public section

open Polynomial

namespace Camina1997.Nottingham

variable {p : ℕ} [Fact p.Prime]

/-- Finite Nottingham depth is the same Laurent displacement order at the parameter. -/
theorem orderTop_toLaurent_sub_parameter (g : Nottingham p) {n : ℕ}
    (hn : depth g = (n : ℕ∞)) :
    (toLaurent g (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) PowerSeries.X) -
      algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) PowerSeries.X).orderTop =
        ((n + 1 : ℕ) : WithTop ℤ) := by
  have ho := order_sub_eq_of_depth_eq g hn
  have hf : g PowerSeries.X - PowerSeries.X ≠ 0 := by
    intro hf
    rw [hf, PowerSeries.order_zero] at ho
    exact ENat.top_ne_natCast _ ho
  rw [toLaurent_algebraMap, ← map_sub, LaurentSeries.coe_algebraMap,
    LaurentSeries.orderTop_coe_of_ne_zero hf, ho]
  rfl

end Camina1997.Nottingham

namespace Camina1997.ArtinSchreier

variable {p : ℕ} [Fact p.Prime]
variable (γ : LaurentSeries (ZMod p)) (m : ℕ)
variable (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))

local notation "K" => LaurentSeries (ZMod p)
local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)
local notation "O" => weightedInteger (p := p) γ m hm hpm hγ
local notation "R" => PowerSeries (ZMod p)

/-- Every cyclic translation fixes the lower parameter in upper coordinates. -/
theorem translationPowerSeries_baseParameter (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (c : ZMod p) :
    translationPowerSeries γ m hm hpm hγ π hπ c (baseParameter γ m hm hpm hγ π hπ) =
      baseParameter γ m hm hpm hγ π hπ := by
  apply powerSeriesEval_injective γ m hm hpm hγ π hπ
  apply Subtype.val_injective
  rw [powerSeriesEval_translationPowerSeries, powerSeriesEval_baseParameter]
  exact (translation γ c).commutes _

variable {G : Type*} [Group G]

/-- A compatible field lift preserves every finite lower depth below its reduced pole. -/
theorem depth_nottinghamAction_of_restriction (π : O)
    (hπ : weightedOrder γ m (π : L) = 1)
    (hd : ∀ c : ZMod p, c ≠ 0 →
      weightedOrder γ m (translation γ c (π : L) - (π : L)) = ((m + 1 : ℕ) : WithTop ℤ))
    (hG : IsPGroup p G) (ρ : G →* (L ≃+* L))
    (hρ : ∀ g x, weightedOrder γ m (ρ g x) = weightedOrder γ m x)
    (q : G →* Nottingham p)
    (hrestrict : ∀ (g : G) (x : K),
      ρ g (algebraMap K L x) = algebraMap K L (Nottingham.toLaurent (q g) x))
    (g : G) {d : ℕ} (hqd : Nottingham.depth (q g) = (d : ℕ∞)) (hdm : d < m) :
    Nottingham.depth (nottinghamAction γ m hm hpm hγ π hπ hG ρ hρ g) = (d : ℕ∞) := by
  let T := baseParameter γ m hm hpm hγ π hπ
  let τ := cyclicNottinghamHom γ m hm hpm hγ π hπ hd (Multiplicative.ofAdd (1 : ZMod p))
  have hτ : Nottingham.depth τ = (m : ℕ∞) :=
    depth_cyclicNottinghamHom γ m hm hpm hγ π hπ hd
      (by change (1 : ZMod p) ≠ 0; exact one_ne_zero)
  have hfix : τ T = T := translationPowerSeries_baseParameter γ m hm hpm hγ π hπ 1
  apply Nottingham.depth_eq_of_fixed_degree_prime_parameter _ τ hτ
    (order_baseParameter γ m hm hpm hγ π hπ) hfix hdm
  apply order_eq_of_weightedOrder_eval γ m hm hpm hγ π hπ
  have he : (powerSeriesEval γ m hm hpm hγ π hπ
      (nottinghamAction γ m hm hpm hγ π hπ hG ρ hρ g T - T) : L) =
      algebraMap K L (Nottingham.toLaurent (q g) (HahnSeries.single 1 1) -
        HahnSeries.single 1 1) := by
    rw [map_sub]
    change (powerSeriesEval γ m hm hpm hγ π hπ
      (nottinghamAction γ m hm hpm hγ π hπ hG ρ hρ g T) : L) -
      (powerSeriesEval γ m hm hpm hγ π hπ T : L) = _
    rw [powerSeriesEval_nottinghamAction,
      powerSeriesEval_baseParameter, hrestrict, map_sub]
  rw [he, weightedOrder_algebraMap]
  have ho := Nottingham.orderTop_toLaurent_sub_parameter (q g) hqd
  rw [LaurentSeries.coe_algebraMap, PowerSeries.coe_X] at ho
  rw [ho]
  norm_cast

end Camina1997.ArtinSchreier
