/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.LaurentParameter
public import Camina1997.ArtinSchreier.Ramification
public import Camina1997.Nottingham.Depth

/-!
# Cyclic Nottingham subgroups with prescribed depth

Transport Artin–Schreier translations through the proved power-series coordinates.
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

/-- Translations restrict to the valuation ring because they preserve its valuation. -/
noncomputable def translationIntegerHom (c : ZMod p) : O →+* O where
  toFun x := ⟨translation γ c x, by
    rw [mem_weightedInteger, weightedOrder_translation γ m hm hpm hγ]
    exact (mem_weightedInteger γ m hm hpm hγ _).mp x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

/-- The restriction is an automorphism of the valuation ring. -/
noncomputable def translationIntegerEquiv (c : ZMod p) : O ≃+* O :=
  RingEquiv.ofBijective (translationIntegerHom γ m hm hpm hγ c) (by
    refine ⟨fun x y h => Subtype.ext ((translation γ c).injective
      (congrArg Subtype.val h)), ?_⟩
    intro x
    have hx : (translation γ c).symm x ∈ O := by
      rw [mem_weightedInteger]
      rw [← weightedOrder_translation γ m hm hpm hγ c, AlgEquiv.apply_symm_apply]
      exact (mem_weightedInteger γ m hm hpm hγ _).mp x.property
    exact ⟨⟨_, hx⟩, Subtype.ext ((translation γ c).apply_symm_apply x)⟩)

/-- The transported power-series algebra automorphism. -/
noncomputable def translationPowerSeries (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (c : ZMod p) :
    PowerSeries (ZMod p) ≃ₐ[ZMod p] PowerSeries (ZMod p) := by
  let e := (powerSeriesEquiv γ m hm hpm hγ π hπ).trans
    ((translationIntegerEquiv γ m hm hpm hγ c).trans
      (powerSeriesEquiv γ m hm hpm hγ π hπ).symm)
  exact AlgEquiv.ofRingEquiv (f := e) (fun a =>
    DFunLike.congr_fun (RingHom.ext_zmod
      (e.toRingHom.comp (algebraMap (ZMod p) (PowerSeries (ZMod p))))
      (algebraMap (ZMod p) (PowerSeries (ZMod p)))) a)

/-- Evaluation intertwines the transported automorphism with the original translation. -/
theorem powerSeriesEval_translationPowerSeries (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (c : ZMod p) (f : PowerSeries (ZMod p)) :
    (powerSeriesEval γ m hm hpm hγ π hπ
      (translationPowerSeries γ m hm hpm hγ π hπ c f) : L) =
      translation γ c (powerSeriesEval γ m hm hpm hγ π hπ f : L) := by
  change ((powerSeriesEquiv γ m hm hpm hγ π hπ)
    ((powerSeriesEquiv γ m hm hpm hγ π hπ).symm _) : L) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

@[simp]
theorem translationPowerSeries_zero (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) :
    translationPowerSeries γ m hm hpm hγ π hπ 0 = 1 := by
  ext f : 1
  apply powerSeriesEval_injective γ m hm hpm hγ π hπ
  apply Subtype.val_injective
  rw [powerSeriesEval_translationPowerSeries]
  have h := congrArg (fun e : L ≃ₐ[K] L => e
    (powerSeriesEval γ m hm hpm hγ π hπ f : L))
    (translationAction (p := p) γ).map_one
  exact h

theorem translationPowerSeries_add (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (c d : ZMod p) :
    translationPowerSeries γ m hm hpm hγ π hπ (c + d) =
      translationPowerSeries γ m hm hpm hγ π hπ c *
        translationPowerSeries γ m hm hpm hγ π hπ d := by
  ext f : 1
  apply powerSeriesEval_injective γ m hm hpm hγ π hπ
  apply Subtype.val_injective
  change (powerSeriesEval γ m hm hpm hγ π hπ
    (translationPowerSeries γ m hm hpm hγ π hπ (c + d) f) : L) =
    (powerSeriesEval γ m hm hpm hγ π hπ
      (translationPowerSeries γ m hm hpm hγ π hπ c
        (translationPowerSeries γ m hm hpm hγ π hπ d f)) : L)
  simp only [powerSeriesEval_translationPowerSeries]
  exact DFunLike.congr_fun (translationHom_add γ c d) _

/-- The exact displacement of a uniformizer is the order of the transported parameter. -/
theorem order_translationPowerSeries_sub (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (c : ZMod p)
    (hd : weightedOrder γ m (translation γ c (π : L) - (π : L)) =
      ((m + 1 : ℕ) : WithTop ℤ)) :
    (translationPowerSeries γ m hm hpm hγ π hπ c PowerSeries.X - PowerSeries.X).order =
      ((m + 1 : ℕ) : ℕ∞) := by
  let f := translationPowerSeries γ m hm hpm hγ π hπ c PowerSeries.X - PowerSeries.X
  have he : (powerSeriesEval γ m hm hpm hγ π hπ f : L) =
      translation γ c (π : L) - (π : L) := by
    simp [f, powerSeriesEval_translationPowerSeries]
  have hf : f ≠ 0 := by
    intro hf
    have hz : translation γ c (π : L) - (π : L) = 0 := by simpa [hf] using he.symm
    rw [hz, weightedOrder_zero] at hd
    exact WithTop.coe_ne_top hd.symm
  have ho := weightedOrder_powerSeriesEval γ m hm hpm hγ π hπ hf
  rw [he, hd] at ho
  have hn : f.order.toNat = m + 1 := by exact_mod_cast ho.symm
  change f.order = _
  rw [← PowerSeries.coe_toNat_order hf, hn]

/-- The prescribed positive depth forces the transported automorphism to be normalized. -/
theorem isNormalized_translationPowerSeries (π : O)
    (hπ : weightedOrder γ m (π : L) = 1)
    (hd : ∀ c : ZMod p, c ≠ 0 → weightedOrder γ m (translation γ c (π : L) - (π : L)) =
      ((m + 1 : ℕ) : WithTop ℤ)) (c : ZMod p) :
    PowerSeries.IsNormalized (translationPowerSeries γ m hm hpm hγ π hπ c) := by
  by_cases hc : c = 0
  · simp [hc]
  rw [PowerSeries.isNormalized_iff_X_sq_dvd, PowerSeries.X_pow_dvd_iff,
    ← PowerSeries.nat_le_order_iff, order_translationPowerSeries_sub γ m hm hpm hγ π hπ c
      (hd c hc)]
  exact_mod_cast (show 2 ≤ m + 1 by omega)

/-- The actual prime-field translation group, embedded into Nottingham coordinates. -/
noncomputable def cyclicNottinghamHom (π : O)
    (hπ : weightedOrder γ m (π : L) = 1)
    (hd : ∀ c : ZMod p, c ≠ 0 → weightedOrder γ m (translation γ c (π : L) - (π : L)) =
      ((m + 1 : ℕ) : WithTop ℤ)) : Multiplicative (ZMod p) →* Nottingham p where
  toFun c := ⟨translationPowerSeries γ m hm hpm hγ π hπ c.toAdd,
    isNormalized_translationPowerSeries γ m hm hpm hγ π hπ hd c.toAdd⟩
  map_one' := Subtype.ext (translationPowerSeries_zero γ m hm hpm hγ π hπ)
  map_mul' c d := Subtype.ext (translationPowerSeries_add γ m hm hpm hγ π hπ c.toAdd d.toAdd)

/-- Every nonidentity element has exactly the selected depth. -/
theorem depth_cyclicNottinghamHom (π : O)
    (hπ : weightedOrder γ m (π : L) = 1)
    (hd : ∀ c : ZMod p, c ≠ 0 → weightedOrder γ m (translation γ c (π : L) - (π : L)) =
      ((m + 1 : ℕ) : WithTop ℤ)) {c : Multiplicative (ZMod p)} (hc : c ≠ 1) :
    Nottingham.depth (cyclicNottinghamHom γ m hm hpm hγ π hπ hd c) = (m : ℕ∞) := by
  change (translationPowerSeries γ m hm hpm hγ π hπ c.toAdd PowerSeries.X -
    PowerSeries.X).order - 1 = _
  rw [order_translationPowerSeries_sub γ m hm hpm hγ π hπ c.toAdd (hd c.toAdd hc)]
  simp

theorem cyclicNottinghamHom_injective (π : O)
    (hπ : weightedOrder γ m (π : L) = 1)
    (hd : ∀ c : ZMod p, c ≠ 0 → weightedOrder γ m (translation γ c (π : L) - (π : L)) =
      ((m + 1 : ℕ) : WithTop ℤ)) :
    Function.Injective (cyclicNottinghamHom γ m hm hpm hγ π hπ hd) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  by_contra hc1
  have h := depth_cyclicNottinghamHom γ m hm hpm hγ π hπ hd hc1
  rw [hc, Nottingham.depth_one] at h
  exact ENat.top_ne_natCast m h

/-- Every positive prime-to-p integer is the common depth of a cyclic order-p subgroup. -/
theorem exists_cyclicNottinghamHom (m : ℕ) (hm : 0 < m) (hpm : ¬p ∣ m) :
    ∃ ι : Multiplicative (ZMod p) →* Nottingham p,
      Function.Injective ι ∧ ∀ c, c ≠ 1 → Nottingham.depth (ι c) = (m : ℕ∞) := by
  let γ : K := HahnSeries.single (-(m : ℤ)) 1
  have hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ) := HahnSeries.orderTop_single one_ne_zero
  obtain ⟨π, hπ, hd⟩ := exists_uniformizer_translation_depth γ m hm hpm
  have hπO : π ∈ weightedInteger (p := p) γ m hm hpm hγ := by
    rw [mem_weightedInteger, hπ]
    exact zero_le_one
  exact ⟨cyclicNottinghamHom γ m hm hpm hγ ⟨π, hπO⟩ hπ hd,
    cyclicNottinghamHom_injective γ m hm hpm hγ ⟨π, hπO⟩ hπ hd,
    fun _ hc => depth_cyclicNottinghamHom γ m hm hpm hγ ⟨π, hπO⟩ hπ hd hc⟩

end Camina1997.ArtinSchreier
