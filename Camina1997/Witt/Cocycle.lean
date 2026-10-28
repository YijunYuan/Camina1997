/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Extension
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.Ring.Action.Basic

/-!
# Explicit additive equations in Witt's construction

A trace-one element gives finite-sum solutions of the additive one- and
two-cocycle equations. Applying the Artin–Schreier map to the second solution
produces the first cocycle required in the central lifting construction.

Reference: Camina (1997), the Witt algorithm, steps (d)–(e), pp. 103–104.
-/

@[expose] public section

namespace Camina1997.Witt

variable {G L : Type*} [Group G] [Fintype G] [Field L] [MulSemiringAction G L]

omit [MulSemiringAction G L] in
private theorem sum_mul_left_reindex (f : G → L) (s : G) :
    ∑ t : G, f (s * t) = ∑ t : G, f t :=
  Fintype.sum_equiv (Equiv.mulLeft s) (fun t => f (s * t)) f (fun _ => rfl)

/-- The sum over a finite orbit is fixed by the action. -/
theorem smul_sum_orbit (α : L) (s : G) :
    s • (∑ t : G, t • α) = ∑ t : G, t • α := by
  simp only [Finset.smul_sum, ← mul_smul]
  exact sum_mul_left_reindex (fun t : G => t • α) s

omit [Fintype G] in
/-- Distinct automorphisms in a faithful field action are linearly independent as functions. -/
theorem linearIndependent_smul [FaithfulSMul G L] :
    LinearIndependent L (fun s : G => fun x : L => s • x) := by
  apply (linearIndependent_monoidHom L L).comp
    (fun s : G => (MulSemiringAction.toRingHom G L s).toMonoidHom)
  intro s t h
  exact eq_of_smul_eq_smul (fun x : L => DFunLike.congr_fun h x)

/-- A finite faithful field action has an element whose orbit sum is one. -/
theorem exists_sum_smul_eq_one [FaithfulSMul G L] :
    ∃ α : L, ∑ s : G, s • α = 1 := by
  classical
  have hex : ∃ β : L, ∑ s : G, s • β ≠ 0 := by
    by_contra h
    push Not at h
    have hz : (∑ s : G, (1 : L) • (fun x : L => s • x)) = 0 := by
      ext x
      simpa using h x
    have he := (linearIndependent_iff'.mp (linearIndependent_smul (G := G) (L := L)))
      Finset.univ (fun _ => (1 : L)) hz (1 : G) (Finset.mem_univ _)
    exact one_ne_zero he
  obtain ⟨β, hβ⟩ := hex
  refine ⟨β / (∑ s : G, s • β), ?_⟩
  have hf (s : G) : s • (β / (∑ t : G, t • β)) =
      (s • β) / (∑ t : G, t • β) := by
    change (MulSemiringAction.toRingHom G L s) (β / (∑ t : G, t • β)) = _
    rw [map_div₀]
    change (s • β) / (s • (∑ t : G, t • β)) = _
    rw [smul_sum_orbit]
  simp_rw [hf]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, mul_inv_cancel₀ hβ]

/-- The explicit trace-one solution of an additive one-cocycle equation. -/
noncomputable def oneCocycleSolution (α : L) (η : G → L) : L :=
  -∑ t : G, η t * (t • α)

theorem oneCocycleSolution_spec (α : L) (hα : ∑ t : G, t • α = 1)
    (η : G → L) (hη : ∀ s t, η (s * t) = η s + s • η t) (s : G) :
    s • oneCocycleSolution α η - oneCocycleSolution α η = η s := by
  have hη' (t : G) : s • η t = η (s * t) - η s := by
    rw [hη]
    ring
  have hs : ∑ t : G, (s * t) • α = 1 :=
    (sum_mul_left_reindex (fun t : G => t • α) s).trans hα
  have he : s • oneCocycleSolution α η = oneCocycleSolution α η + η s := by
    simp only [oneCocycleSolution, smul_neg, Finset.smul_sum, MulSemiringAction.smul_mul,
      ← mul_smul, hη', sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_one]
    rw [sum_mul_left_reindex (fun t : G => η t * (t • α)) s]
    ring
  rw [he]
  ring

/-- The trace-one finite sum that splits a fixed-valued additive two-cocycle. -/
noncomputable def twoCocycleSolution (α : L) (c : G → G → L) (s : G) : L :=
  ∑ u : G, c s u * ((s * u) • α)

theorem twoCocycleSolution_spec (α : L) (hα : ∑ u : G, u • α = 1)
    (c : G → G → L) (hcfix : ∀ s t u : G, s • c t u = c t u)
    (hc : ∀ s t u, c s t + c (s * t) u = c s (t * u) + c t u) (s t : G) :
    twoCocycleSolution α c s + s • twoCocycleSolution α c t -
      twoCocycleSolution α c (s * t) = c s t := by
  have hleft : twoCocycleSolution α c s =
      ∑ u : G, c s (t * u) * ((s * t * u) • α) := by
    simpa only [twoCocycleSolution, mul_assoc] using
      (sum_mul_left_reindex (fun u : G => c s u * ((s * u) • α)) t).symm
  have hact : s • twoCocycleSolution α c t =
      ∑ u : G, c t u * ((s * t * u) • α) := by
    simp only [twoCocycleSolution, Finset.smul_sum, MulSemiringAction.smul_mul,
      hcfix, ← mul_smul, mul_assoc]
  have hc' (u : G) : c s (t * u) + c t u - c (s * t) u = c s t := by
    rw [← hc]
    ring
  calc
    _ = ∑ u : G, (c s (t * u) + c t u - c (s * t) u) *
        ((s * t * u) • α) := by
      rw [hleft, hact, twoCocycleSolution]
      simp only [add_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = c s t * ∑ u : G, (s * t * u) • α := by
      simp only [hc', Finset.mul_sum]
    _ = c s t := by
      rw [sum_mul_left_reindex (fun u : G => u • α) (s * t), hα, mul_one]

@[simp]
theorem twoCocycleSolution_one (α : L) (c : G → G → L)
    (hc : ∀ u, c 1 u = 0) : twoCocycleSolution α c 1 = 0 := by
  simp [twoCocycleSolution, hc]

variable {p : ℕ} [Fact p.Prime] [CharP L p]

omit [Fintype G] in
/-- Applying the Artin–Schreier map to a split prime-valued two-cocycle gives a one-cocycle. -/
theorem pow_sub_isOneCocycle_of_twoCocycle (δ : G → L) (c : G → G → L)
    (hδ : ∀ s t, δ s + s • δ t - δ (s * t) = c s t)
    (hc : ∀ s t, c s t ^ p = c s t) (s t : G) :
    δ (s * t) ^ p - δ (s * t) =
      (δ s ^ p - δ s) + s • (δ t ^ p - δ t) := by
  have he : δ (s * t) = δ s + s • δ t - c s t := by
    linear_combination -(hδ s t)
  have hp : (s • δ t) ^ p = s • (δ t ^ p) :=
    (map_pow (MulSemiringAction.toRingHom G L s) (δ t) p).symm
  rw [he, sub_pow_char, add_pow_char, hp, hc]
  simp only [smul_sub]
  ring

omit [Fintype G] in
private theorem smul_zmod_cast (c : ZMod p) (s : G) :
    s • (ZMod.castHom (dvd_refl p) L c) = ZMod.castHom (dvd_refl p) L c := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective c
  simp only [map_natCast]
  exact map_natCast (MulSemiringAction.toRingHom G L s) n

omit [Fintype G] [MulSemiringAction G L] in
private theorem zmod_cast_pow (c : ZMod p) :
    (ZMod.castHom (dvd_refl p) L c) ^ p = ZMod.castHom (dvd_refl p) L c := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective c
  simp only [map_natCast]
  exact map_natCast (frobenius L p) n

omit [Fintype G] in
/-- Witt's two additive equations have explicit solutions for every prime-field cocycle.

The trace-one element used in the finite sums is proved to exist for the given faithful action;
neither a lift of the action nor a solution of either additive equation is assumed.
-/
theorem exists_witt_equations [Finite G] [FaithfulSMul G L] (c : G → G → ZMod p)
    (hc1 : ∀ t, c 1 t = 0)
    (hc : ∀ s t u, c s t + c (s * t) u = c s (t * u) + c t u) :
    ∃ (δ : G → L) (γ : L), δ 1 = 0 ∧
      (∀ s t, δ s + s • δ t - δ (s * t) = ZMod.castHom (dvd_refl p) L (c s t)) ∧
      ∀ s, s • γ - γ = δ s ^ p - δ s := by
  let := Fintype.ofFinite G
  obtain ⟨α, hα⟩ := exists_sum_smul_eq_one (G := G) (L := L)
  let cL : G → G → L := fun s t => ZMod.castHom (dvd_refl p) L (c s t)
  have hcL : ∀ s t u, cL s t + cL (s * t) u = cL s (t * u) + cL t u := by
    intro s t u
    simpa only [cL, map_add] using congrArg (ZMod.castHom (dvd_refl p) L) (hc s t u)
  let δ := twoCocycleSolution α cL
  have hδ (s t : G) : δ s + s • δ t - δ (s * t) = cL s t :=
    twoCocycleSolution_spec α hα cL (fun s t u => smul_zmod_cast (c t u) s)
      hcL s t
  let η : G → L := fun s => δ s ^ p - δ s
  have hη (s t : G) : η (s * t) = η s + s • η t :=
    pow_sub_isOneCocycle_of_twoCocycle δ cL hδ (fun s t => zmod_cast_pow (c s t)) s t
  refine ⟨δ, oneCocycleSolution α η, ?_, hδ, ?_⟩
  · exact twoCocycleSolution_one α cL (by intro t; simp [cL, hc1])
  · exact oneCocycleSolution_spec α hα η hη

end Camina1997.Witt
