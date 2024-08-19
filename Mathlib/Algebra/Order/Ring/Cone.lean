/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Constructing an ordered ring from a ring with a specified positive cone.

-/


/-! ### Positive cones -/


variable {R : Type*} [Ring R]

namespace Ring

/-- `PositiveConeClass S R` says that `S` is a type of `PositiveCone`s in `R`. -/
class PositiveConeClass (S R : Type*) [Ring R] [SetLike S R]
    extends AddCommGroup.PositiveConeClass S R, SubsemiringClass S R : Prop

/-- A positive cone in a `Ring` is a `Subsemiring` that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of an `OrderedRing`. -/
structure PositiveCone (R : Type*) [Ring R] extends Subsemiring R where
  eq_zero_of_mem_of_neg_mem' : ∀ {a}, a ∈ carrier → -a ∈ carrier → a = 0

/-- A total positive cone in a nontrivial ring induces a linear order. -/
structure TotalPositiveCone (α : Type*) [Ring α] extends PositiveCone α,
  AddCommGroup.TotalPositiveCone α

theorem PositiveCone.one_pos (C : PositiveCone α) : C.pos 1 :=
  (C.pos_iff _).2 ⟨C.one_nonneg, fun h => one_ne_zero <| C.nonneg_antisymm C.one_nonneg h⟩

end Ring

open Ring

/-- Construct a `StrictOrderedRing` by designating a positive cone in an existing `Ring`. -/
def StrictOrderedRing.mkOfPositiveCone (C : PositiveCone α) : StrictOrderedRing α :=
  { ‹Ring α›, OrderedAddCommGroup.mkOfPositiveCone C.toPositiveCone with
    exists_pair_ne := ⟨0, 1, fun h => by simpa [← h, C.pos_iff] using C.one_pos⟩,
    zero_le_one := by
      change C.nonneg (1 - 0)
      convert C.one_nonneg
      simp,
    mul_pos := fun x y xp yp => by
      change C.pos (x * y - 0)
      -- Porting note: used to be convert, but it relied on unfolding definitions
      rw [sub_zero]
      exact C.mul_pos x y (by rwa [← sub_zero x]) (by rwa [← sub_zero y]) }

/-- Construct a `LinearOrderedRing` by
designating a positive cone in an existing `Ring`. -/
def LinearOrderedRing.mkOfPositiveCone (C : TotalPositiveCone α) : LinearOrderedRing α :=
  { LinearOrderedAddCommGroup.mkOfPositiveCone C.toTotalPositiveCone,
    StrictOrderedRing.mkOfPositiveCone C.toPositiveCone_1 with }
