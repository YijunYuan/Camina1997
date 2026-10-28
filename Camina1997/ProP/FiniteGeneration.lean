/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Topological finite generation and continuous homomorphisms

A finite set generating a dense subgroup determines every continuous
homomorphism to a Hausdorff group. Consequently there are only finitely many
continuous homomorphisms into each finite Hausdorff group.

Reference: Camina (1997), Theorem 5, p. 111; finite-quotient form of its
compactness argument.
-/

@[expose] public section

namespace Camina1997

/-- A group is topologically finitely generated when a finite set generates a dense subgroup. -/
def TopologicallyFG (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ s : Set G, s.Finite ∧ Dense (Subgroup.closure s : Set G)

variable {G A : Type*} [Group G] [TopologicalSpace G]
  [Group A] [TopologicalSpace A] [T2Space A]

/-- Agreement on generators of a dense subgroup determines a continuous homomorphism. -/
theorem continuousMonoidHom_ext_of_dense_closure {s : Set G}
    (hs : Dense (Subgroup.closure s : Set G))
    {f g : ContinuousMonoidHom G A} (h : Set.EqOn f g s) : f = g := by
  apply DFunLike.coe_injective
  apply Continuous.ext_on hs f.continuous g.continuous
  exact MonoidHom.eqOn_closure (f := f.toMonoidHom) (g := g.toMonoidHom) h

/-- Evaluation on a dense generating set embeds continuous homomorphisms into its function space. -/
theorem continuousMonoidHom_eval_injective {s : Set G}
    (hs : Dense (Subgroup.closure s : Set G)) :
    Function.Injective (fun f : ContinuousMonoidHom G A => fun x : s => f x) := by
  intro f g h
  apply continuousMonoidHom_ext_of_dense_closure hs
  intro x hx
  exact congrFun h ⟨x, hx⟩

/-- A finite dense generating set makes homomorphisms to a finite Hausdorff group finite. -/
theorem finite_continuousMonoidHom_of_dense_closure [Finite A] {s : Set G}
    (hfinite : s.Finite) (hs : Dense (Subgroup.closure s : Set G)) :
    Finite (ContinuousMonoidHom G A) := by
  let := hfinite.fintype
  exact Finite.of_injective _ (continuousMonoidHom_eval_injective (A := A) hs)

/-- The number of continuous homomorphisms is bounded by assignments on a finite generating set. -/
theorem card_continuousMonoidHom_le_of_dense_closure [Finite A] {s : Set G}
    (hfinite : s.Finite) (hs : Dense (Subgroup.closure s : Set G)) :
    Nat.card (ContinuousMonoidHom G A) ≤ Nat.card A ^ Nat.card s := by
  let := hfinite.fintype
  calc
    Nat.card (ContinuousMonoidHom G A) ≤ Nat.card (s → A) :=
      Nat.card_le_card_of_injective _ (continuousMonoidHom_eval_injective (A := A) hs)
    _ = Nat.card A ^ Nat.card s := Nat.card_fun

/-- A dense generating tuple of length r gives the bound `|A|^r`. -/
theorem card_continuousMonoidHom_le_of_dense_tuple [Finite A] {r : ℕ}
    (s : Fin r → G) (hs : Dense (Subgroup.closure (Set.range s) : Set G)) :
    Nat.card (ContinuousMonoidHom G A) ≤ Nat.card A ^ r := by
  have heval : Function.Injective
      (fun f : ContinuousMonoidHom G A => fun i : Fin r => f (s i)) := by
    intro f g h
    apply continuousMonoidHom_ext_of_dense_closure hs
    rintro _ ⟨i, rfl⟩
    exact congrFun h i
  calc
    Nat.card (ContinuousMonoidHom G A) ≤ Nat.card (Fin r → A) :=
      Nat.card_le_card_of_injective _ heval
    _ = Nat.card A ^ r := by rw [Nat.card_fun, Nat.card_fin]

namespace TopologicallyFG

/-- There are finitely many continuous homomorphisms to any finite Hausdorff group. -/
theorem finite_continuousMonoidHom [Finite A] (hG : TopologicallyFG G) :
    Finite (ContinuousMonoidHom G A) := by
  obtain ⟨s, hfinite, hs⟩ := hG
  exact finite_continuousMonoidHom_of_dense_closure hfinite hs

end TopologicallyFG

end Camina1997
