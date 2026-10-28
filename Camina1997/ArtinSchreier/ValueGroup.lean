/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Residue
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# The value-group index of a reduced Artin–Schreier extension

The actual finite values on the base field form `pℤ`, while those on the
extension fill `ℤ`. Their index is the extension degree.
-/

@[expose] public section

namespace AddValuation

variable {F : Type*} [Field F]

/-- The finite values of an integer-valued additive valuation form an additive subgroup. -/
def finiteValueSubgroup (v : AddValuation F (WithTop ℤ)) : AddSubgroup ℤ where
  carrier := {n | ∃ x : F, v x = (n : WithTop ℤ)}
  zero_mem' := ⟨1, v.map_one⟩
  add_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by rw [v.map_mul, hx, hy, WithTop.coe_add]⟩
  neg_mem' := by
    rintro a ⟨x, hx⟩
    exact ⟨x⁻¹, by rw [v.map_inv, hx]; rfl⟩

@[simp]
theorem mem_finiteValueSubgroup (v : AddValuation F (WithTop ℤ)) (n : ℤ) :
    n ∈ v.finiteValueSubgroup ↔ ∃ x : F, v x = (n : WithTop ℤ) := Iff.rfl

end AddValuation

namespace Camina1997.ArtinSchreier

open Polynomial

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]
variable (γ : LaurentSeries k) (m : ℕ)
variable (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))

local notation "K" => LaurentSeries k
local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)

/-- The base field contributes exactly the multiples of p to the normalized value group. -/
theorem finiteValueSubgroup_weighted_comap :
    ((weightedValuation γ m hm hpm hγ).comap (algebraMap K L)).finiteValueSubgroup =
      AddSubgroup.zmultiples (p : ℤ) := by
  ext n
  rw [AddValuation.mem_finiteValueSubgroup, Int.mem_zmultiples_iff]
  constructor
  · rintro ⟨x, hx⟩
    change weightedOrder γ m (algebraMap K L x) = (n : WithTop ℤ) at hx
    have hx0 : x ≠ 0 := by
      intro hz
      simp [hz, weightedOrder_zero] at hx
    rw [weightedOrder_algebraMap] at hx
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx0] at hx
    have hn : (p : ℤ) * x.order = n := by exact_mod_cast hx
    exact ⟨x.order, hn.symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨HahnSeries.single a 1, ?_⟩
    change weightedOrder γ m (algebraMap K L (HahnSeries.single a 1)) = _
    rw [weightedOrder_algebraMap, HahnSeries.orderTop_single one_ne_zero]
    norm_cast

/-- Consequently the base value subgroup has index p. -/
theorem index_finiteValueSubgroup_weighted_comap :
    ((weightedValuation γ m hm hpm hγ).comap (algebraMap K L)).finiteValueSubgroup.index = p := by
  rw [finiteValueSubgroup_weighted_comap, Int.index_zmultiples, Int.natAbs_natCast]

variable [CharP k p]

/-- The extension has the full normalized integer value group. -/
theorem finiteValueSubgroup_weighted :
    letI : Fact (Irreducible ((X : K[X]) ^ p - X - C γ)) :=
      ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm γ hγ⟩
    (weightedValuation γ m hm hpm hγ).finiteValueSubgroup = ⊤ := by
  let : Fact (Irreducible ((X : K[X]) ^ p - X - C γ)) :=
    ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm γ hγ⟩
  apply top_unique
  intro n _
  exact exists_weightedOrder_eq γ m hpm n

omit [CharP k p] in
/-- The value-group index equals the degree of the concrete field extension. -/
theorem index_finiteValueSubgroup_eq_finrank :
    ((weightedValuation γ m hm hpm hγ).comap (algebraMap K L)).finiteValueSubgroup.index =
      Module.finrank K L := by
  rw [index_finiteValueSubgroup_weighted_comap, finrank_adjoinRoot]

end Camina1997.ArtinSchreier
