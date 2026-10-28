/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Sparse coordinates for the Lubotzky–Wilson construction

Disjoint consecutive exponent blocks enumerate the finite groups. Powers with
these exponents give distinct positions in a sufficiently large cyclic group.
The sparse function takes the enumerated values at these positions and is one
elsewhere.

Reference: Lubotzky–Wilson (1984), p. 398.
-/

@[expose] public section

namespace Camina1997.LubotzkyWilson

variable (F : ℕ → Type*)

/-- The cumulative sizes of the preceding finite groups. -/
noncomputable def blockEnd : ℕ → ℕ
  | 0 => 0
  | n + 1 => blockEnd n + Nat.card (F n)

@[simp]
theorem blockEnd_zero : blockEnd F 0 = 0 := rfl

@[simp]
theorem blockEnd_succ (n : ℕ) : blockEnd F (n + 1) = blockEnd F n + Nat.card (F n) := rfl

theorem blockEnd_strictMono [∀ n, Nonempty (F n)] [∀ n, Finite (F n)] :
    StrictMono (blockEnd F) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [blockEnd_succ]
  exact Nat.lt_add_of_pos_right Nat.card_pos

/-- The exponent assigned to an index in the nth finite group. -/
noncomputable def blockIndex (n : ℕ) (i : Fin (Nat.card (F n))) : ℕ :=
  blockEnd F n + i.val + 1

theorem blockIndex_gt (n : ℕ) (i : Fin (Nat.card (F n))) :
    blockEnd F n < blockIndex F n i := by
  unfold blockIndex
  omega

theorem blockIndex_le (n : ℕ) (i : Fin (Nat.card (F n))) :
    blockIndex F n i ≤ blockEnd F (n + 1) := by
  rw [blockEnd_succ]
  unfold blockIndex
  omega

theorem blockIndex_pos (n : ℕ) (i : Fin (Nat.card (F n))) :
    0 < blockIndex F n i := lt_of_le_of_lt (Nat.zero_le _) (blockIndex_gt F n i)

theorem blockIndex_injective (n : ℕ) : Function.Injective (blockIndex F n) := by
  intro i j h
  apply Fin.ext
  unfold blockIndex at h
  omega

/-- Distinct blocks have disjoint exponent intervals. -/
theorem blockIndex_eq_implies_block_eq [∀ n, Nonempty (F n)] [∀ n, Finite (F n)] {m n : ℕ}
    (i : Fin (Nat.card (F m))) (j : Fin (Nat.card (F n)))
    (h : blockIndex F m i = blockIndex F n j) : m = n := by
  have hm := blockIndex_gt F m i
  have hn := blockIndex_gt F n j
  have hmi := blockIndex_le F m i
  have hnj := blockIndex_le F n j
  rcases lt_trichotomy m n with hmn | heq | hnm
  · have hmon : blockEnd F (m + 1) ≤ blockEnd F n :=
      (blockEnd_strictMono F).monotone (Nat.succ_le_of_lt hmn)
    omega
  · exact heq
  · have hmon : blockEnd F (n + 1) ≤ blockEnd F m :=
      (blockEnd_strictMono F).monotone (Nat.succ_le_of_lt hnm)
    omega

/-- The cyclic coordinate set for the nth block. -/
abbrev CyclicCoordinates (q n : ℕ) := ZMod (q ^ (blockEnd F (n + 1) + 1))

/-- The power coordinate assigned to a group index. -/
noncomputable def powerCoordinate (q n : ℕ) (i : Fin (Nat.card (F n))) :
    CyclicCoordinates F q n := (q ^ blockIndex F n i : ℕ)

theorem powerCoordinate_val {q : ℕ} (hq : 1 < q) (n : ℕ)
    (i : Fin (Nat.card (F n))) :
    (powerCoordinate F q n i).val = q ^ blockIndex F n i := by
  apply ZMod.val_natCast_of_lt
  exact Nat.pow_lt_pow_right hq (Nat.lt_succ_of_le (blockIndex_le F n i))

theorem powerCoordinate_injective {q : ℕ} (hq : 1 < q) (n : ℕ) :
    Function.Injective (powerCoordinate F q n) := by
  intro i j h
  have hp := congrArg ZMod.val h
  rw [powerCoordinate_val F hq, powerCoordinate_val F hq] at hp
  exact blockIndex_injective F n (Nat.pow_right_injective hq hp)

/-- Every exponent in a block comes from a unique finite index. -/
theorem exists_blockIndex_eq {n e : ℕ} (hlo : blockEnd F n < e)
    (hhi : e ≤ blockEnd F (n + 1)) :
    ∃! i : Fin (Nat.card (F n)), blockIndex F n i = e := by
  rw [blockEnd_succ] at hhi
  let i : Fin (Nat.card (F n)) := ⟨e - blockEnd F n - 1, by omega⟩
  have hi : blockIndex F n i = e := by
    dsimp [blockIndex, i]
    omega
  exact ⟨i, hi, fun j hj => blockIndex_injective F n (hj.trans hi.symm)⟩

/-- A fixed enumeration of the finite group. -/
noncomputable def enumeration (n : ℕ) [Finite (F n)] : Fin (Nat.card (F n)) ≃ F n :=
  (Finite.equivFin (F n)).symm

/-- The exponent assigned to an element of the nth finite group. -/
noncomputable def elementIndex (n : ℕ) [Finite (F n)] (a : F n) : ℕ :=
  blockIndex F n ((enumeration F n).symm a)

theorem elementIndex_gt (n : ℕ) [Finite (F n)] (a : F n) :
    blockEnd F n < elementIndex F n a := blockIndex_gt F n _

theorem elementIndex_le (n : ℕ) [Finite (F n)] (a : F n) :
    elementIndex F n a ≤ blockEnd F (n + 1) := blockIndex_le F n _

theorem elementIndex_pos (n : ℕ) [Finite (F n)] (a : F n) :
    0 < elementIndex F n a := blockIndex_pos F n _

theorem elementIndex_injective (n : ℕ) [Finite (F n)] :
    Function.Injective (elementIndex F n) :=
  (blockIndex_injective F n).comp (enumeration F n).symm.injective

/-- An element's assigned exponent belongs to no other block. -/
theorem block_eq_of_elementIndex_mem [∀ n, Nonempty (F n)] [∀ n, Finite (F n)]
    {m n : ℕ} (a : F n) (hlo : blockEnd F m < elementIndex F n a)
    (hhi : elementIndex F n a ≤ blockEnd F (m + 1)) : m = n := by
  obtain ⟨i, hi, _⟩ := exists_blockIndex_eq F hlo hhi
  exact blockIndex_eq_implies_block_eq F i ((enumeration F n).symm a) hi

/-- The sparse base function, equal to one off the selected power coordinates. -/
noncomputable def sparseFunction (q n : ℕ) [One (F n)] [Finite (F n)] :
    CyclicCoordinates F q n → F n :=
  Function.extend (powerCoordinate F q n) (enumeration F n) (fun _ => 1)

theorem sparseFunction_powerCoordinate {q : ℕ} (hq : 1 < q) (n : ℕ)
    [One (F n)] [Finite (F n)] (i : Fin (Nat.card (F n))) :
    sparseFunction F q n (powerCoordinate F q n i) = enumeration F n i :=
  (powerCoordinate_injective F hq n).extend_apply _ _ i

/-- The selected power for each element recovers that element. -/
theorem sparseFunction_elementIndex {q : ℕ} (hq : 1 < q) (n : ℕ)
    [One (F n)] [Finite (F n)] (a : F n) :
    sparseFunction F q n (q ^ elementIndex F n a : ℕ) = a := by
  change sparseFunction F q n (powerCoordinate F q n ((enumeration F n).symm a)) = a
  rw [sparseFunction_powerCoordinate F hq, Equiv.apply_symm_apply]

theorem sparseFunction_eq_one_of_not_range (q n : ℕ) [One (F n)] [Finite (F n)]
    (x : CyclicCoordinates F q n) (hx : x ∉ Set.range (powerCoordinate F q n)) :
    sparseFunction F q n x = 1 :=
  Function.extend_apply' _ _ _ hx

/-- A nonidentity value can occur only at a power from the assigned exponent block. -/
theorem sparseFunction_ne_one_imp (q n : ℕ) [One (F n)] [Finite (F n)]
    (x : CyclicCoordinates F q n) (hx : sparseFunction F q n x ≠ 1) :
    ∃ e : ℕ, blockEnd F n < e ∧ e ≤ blockEnd F (n + 1) ∧ x = (q ^ e : ℕ) := by
  have hxrange : x ∈ Set.range (powerCoordinate F q n) := by
    by_contra hn
    exact hx (sparseFunction_eq_one_of_not_range F q n x hn)
  obtain ⟨i, rfl⟩ := hxrange
  exact ⟨blockIndex F n i, blockIndex_gt F n i, blockIndex_le F n i, rfl⟩

/-- The same sparse function regarded as a base function on the multiplicative cyclic group. -/
noncomputable def sparseBase (q n : ℕ) [One (F n)] [Finite (F n)] :
    Multiplicative (CyclicCoordinates F q n) → F n :=
  fun x => sparseFunction F q n x.toAdd

@[simp]
theorem sparseBase_ofAdd (q n : ℕ) [One (F n)] [Finite (F n)]
    (x : CyclicCoordinates F q n) :
    sparseBase F q n (Multiplicative.ofAdd x) = sparseFunction F q n x := rfl

end Camina1997.LubotzkyWilson
