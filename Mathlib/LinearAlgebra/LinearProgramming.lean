/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! # Linear programming

Minimizing a linear function on a region defined by linear inequalities.

## Main definitions

 * `LinearProgram` defines a linear program in a form that generalizes "A x ≥ b".
 * `LinearProgram.feasibles` is the set of all admissible solutions to given linear program.
 * `LinearProgram.MinAt` defines an optimum solution of given linear program.

-/

/-- Linear program in the form of inequalities with general variables. -/
structure LinearProgram (K : Type*) {V : Type*} (P : Type*)
    [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P] where
  /-- Inequality constraints (given in the form "aᵀx - b ≥ 0") -/
  constraints : List (P →ᵃ[K] K)
  /-- The objective function (affine map) -/
  objective : P →ᵃ[K] K

variable {K V P : Type*} [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P]

/-- Constructs a linear program given a list of equalities, a list of inequalities,
    and an objective function. -/
def LinearProgram.mkOfEqs
    (equalities inequalities : List (P →ᵃ[K] K)) (objective : P →ᵃ[K] K) :
    LinearProgram K P :=
  { constraints := inequalities ++ equalities ++ equalities.map Neg.neg, objective }

/-- The set of all admissible solutions to given linear program. -/
def LinearProgram.feasibles (lp : LinearProgram K P) : Set P :=
  {x | ∀ ⦃a⦄, a ∈ lp.constraints → 0 ≤ a x}

@[simp] lemma LinearProgram.mem_feasibles {lp : LinearProgram K P} {x : P} :
    x ∈ lp.feasibles ↔ ∀ ⦃a⦄, a ∈ lp.constraints → 0 ≤ a x :=
  Iff.rfl

/-- Given linear program is minimized at given point. -/
def LinearProgram.MinAt (lp : LinearProgram K P) (x : P) : Prop :=
  IsLeast (lp.objective '' lp.feasibles) (lp.objective x)

lemma LinearProgram.feasibles_mkOfEqs
    (equalities inequalities : List (P →ᵃ[K] K)) (objective : P →ᵃ[K] K) :
    (mkOfEqs equalities inequalities objective).feasibles =
    { x : P | (∀ a ∈ equalities, a x = 0) ∧ (∀ a ∈ inequalities, 0 ≤ a x) } := by
  ext x
  rw [mem_feasibles]
  constructor
  · intro hyp
    simp only [LinearProgram.mkOfEqs, List.append_assoc, List.mem_append, List.mem_map,
      Function.Involutive.exists_mem_and_apply_eq_iff, neg_involutive] at hyp
    constructor
    · intro constr_eq mem_equalities
      refine le_antisymm ?neg (hyp (by simp [mem_equalities]))
      rw [← Left.nonneg_neg_iff, ← Pi.neg_apply, ← AffineMap.coe_neg]
      apply hyp
      simp [mem_equalities]
    · intro constr_le mem_inequalities
      exact hyp (by simp [mem_inequalities])
  · intro hyp
    rw [LinearProgram.mkOfEqs]
    intro constraint constraint_mem
    rw [List.mem_append, List.mem_append] at constraint_mem
    cases constraint_mem with
    | inl normal =>
      cases normal with
      | inl mem_les => exact hyp.2 constraint mem_les
      | inr mem_eqs => exact Eq.ge (hyp.1 constraint mem_eqs)
    | inr negated =>
      rw [List.mem_map] at negated
      rcases negated with ⟨orig, orig_mem, neg_orig⟩
      rw [← neg_orig]
      simp [hyp.1 orig orig_mem]

/-- Adding more constraints cannot enlarge the set of feasible solutions. -/
lemma LinearProgram.feasibles_superset_of_constraints_subset {lp₁ lp₂ : LinearProgram K P}
    (constrss : lp₁.constraints ⊆ lp₂.constraints) :
    lp₂.feasibles ⊆ lp₁.feasibles := by
  intro x hx
  rw [mem_feasibles] at hx ⊢
  intro a ha
  apply hx
  exact constrss ha

/-- Adding more constraints cannot decrease the minimum. -/
lemma LinearProgram.min_le_of_constraints_subset {lp₁ lp₂ : LinearProgram K P} {x₁ x₂ : P}
    (constrss : lp₁.constraints ⊆ lp₂.constraints)
    (hobj : lp₁.objective = lp₂.objective) (opt₁ : lp₁.MinAt x₁) (opt₂ : lp₂.MinAt x₂) :
    lp₁.objective x₁ ≤ lp₂.objective x₂ := by
  unfold LinearProgram.MinAt at opt₁ opt₂
  apply IsLeast.mono opt₂ opt₁
  rw [hobj]
  apply Set.image_subset
  exact feasibles_superset_of_constraints_subset constrss
