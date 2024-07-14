/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

#align_import ring_theory.zmod from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"

/-!
# Ring theoretic facts about `ZMod n`

We collect a few facts about `ZMod n` that need some ring theory to be proved/stated.

## Main statements

* `ZMod.ker_intCastRingHom`:  the ring homomorphism `ℤ → ZMod n` has kernel generated by `n`.
* `ZMod.ringHom_eq_of_ker_eq`: two ring homomorphisms into `ZMod n` with equal kernels are equal.
* `isReduced_zmod`: `ZMod n` is reduced for all squarefree `n`.
-/

/-- The ring homomorphism `ℤ → ZMod n` has kernel generated by `n`. -/
theorem ZMod.ker_intCastRingHom (n : ℕ) :
    RingHom.ker (Int.castRingHom (ZMod n)) = Ideal.span ({(n : ℤ)} : Set ℤ) := by
  ext
  rw [Ideal.mem_span_singleton, RingHom.mem_ker, Int.coe_castRingHom,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
#align zmod.ker_int_cast_ring_hom ZMod.ker_intCastRingHom

/-- Two ring homomorphisms into `ZMod n` with equal kernels are equal. -/
theorem ZMod.ringHom_eq_of_ker_eq {n : ℕ} {R : Type*} [CommRing R] (f g : R →+* ZMod n)
    (h : RingHom.ker f = RingHom.ker g) : f = g := by
  have := f.liftOfRightInverse_comp _ (ZMod.ringHom_rightInverse f) ⟨g, le_of_eq h⟩
  rw [Subtype.coe_mk] at this
  rw [← this, RingHom.ext_zmod (f.liftOfRightInverse _ _ ⟨g, _⟩) _, RingHom.id_comp]
#align zmod.ring_hom_eq_of_ker_eq ZMod.ringHom_eq_of_ker_eq

/-- `ZMod n` is reduced iff `n` is square-free (or `n=0`). -/
@[simp]
theorem isReduced_zmod {n : ℕ} : IsReduced (ZMod n) ↔ Squarefree n ∨ n = 0 := by
  rw [← RingHom.ker_isRadical_iff_reduced_of_surjective
      (ZMod.ringHom_surjective <| Int.castRingHom <| ZMod n),
      ZMod.ker_intCastRingHom, ← isRadical_iff_span_singleton, isRadical_iff_squarefree_or_zero,
      Int.squarefree_natCast, Nat.cast_eq_zero]
#align is_reduced_zmod isReduced_zmod

instance {n : ℕ} [Fact <| Squarefree n] : IsReduced (ZMod n) :=
  isReduced_zmod.2 <| Or.inl <| Fact.out
