/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Invertible.GroupWithZero
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

#align_import algebra.invertible from "leanprover-community/mathlib"@"722b3b152ddd5e0cf21c0a29787c76596cb6b422"
/-!
# Theorems about invertible elements

-/

universe u

variable {α : Type u}

/-- An `Invertible` element is a unit. -/
@[simps]
def unitOfInvertible [Monoid α] (a : α) [Invertible a] : αˣ where
  val := a
  inv := ⅟ a
  val_inv := by simp
  inv_val := by simp
#align unit_of_invertible unitOfInvertible
#align coe_unit_of_invertible val_unitOfInvertible
#align coe_inv_unit_of_invertible val_inv_unitOfInvertible

lemma isUnit_of_invertible [Monoid α] (a : α) [Invertible a] : IsUnit a :=
  ⟨unitOfInvertible a, rfl⟩
#align is_unit_of_invertible isUnit_of_invertible

/-- Units are invertible in their associated monoid. -/
def Units.invertible [Monoid α] (u : αˣ) :
    Invertible (u : α) where
  invOf := ↑u⁻¹
  invOf_mul_self := u.inv_mul
  mul_invOf_self := u.mul_inv
#align units.invertible Units.invertible

@[simp]
lemma invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟ (u : α) = ↑u⁻¹ :=
  invOf_eq_right_inv u.mul_inv
#align inv_of_units invOf_units

lemma IsUnit.nonempty_invertible [Monoid α] {a : α} (h : IsUnit a) : Nonempty (Invertible a) :=
  let ⟨x, hx⟩ := h
  ⟨x.invertible.copy _ hx.symm⟩
#align is_unit.nonempty_invertible IsUnit.nonempty_invertible

/-- Convert `IsUnit` to `Invertible` using `Classical.choice`.

Prefer `casesI h.nonempty_invertible` over `letI := h.invertible` if you want to avoid choice. -/
noncomputable def IsUnit.invertible [Monoid α] {a : α} (h : IsUnit a) : Invertible a :=
  Classical.choice h.nonempty_invertible
#align is_unit.invertible IsUnit.invertible

@[simp]
lemma nonempty_invertible_iff_isUnit [Monoid α] (a : α) : Nonempty (Invertible a) ↔ IsUnit a :=
  ⟨Nonempty.rec <| @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩
#align nonempty_invertible_iff_is_unit nonempty_invertible_iff_isUnit

lemma Commute.invOf_right [Monoid α] {a b : α} [Invertible b] (h : Commute a b) :
    Commute a (⅟ b) :=
  calc
    a * ⅟ b = ⅟ b * (b * a * ⅟ b) := by simp [mul_assoc]
    _ = ⅟ b * (a * b * ⅟ b) := by rw [h.eq]
    _ = ⅟ b * a := by simp [mul_assoc]
#align commute.inv_of_right Commute.invOf_right

lemma Commute.invOf_left [Monoid α] {a b : α} [Invertible b] (h : Commute b a) :
    Commute (⅟ b) a :=
  calc
    ⅟ b * a = ⅟ b * (a * b * ⅟ b) := by simp [mul_assoc]
    _ = ⅟ b * (b * a * ⅟ b) := by rw [h.eq]
    _ = a * ⅟ b := by simp [mul_assoc]
#align commute.inv_of_left Commute.invOf_left

lemma commute_invOf {M : Type*} [One M] [Mul M] (m : M) [Invertible m] : Commute m (⅟ m) :=
  calc
    m * ⅟ m = 1 := mul_invOf_self m
    _ = ⅟ m * m := (invOf_mul_self m).symm
#align commute_inv_of commute_invOf

section Monoid

variable [Monoid α]

/-- This is the `Invertible` version of `Units.isUnit_units_mul` -/
abbrev invertibleOfInvertibleMul (a b : α) [Invertible a] [Invertible (a * b)] : Invertible b where
  invOf := ⅟ (a * b) * a
  invOf_mul_self := by rw [mul_assoc, invOf_mul_self]
  mul_invOf_self := by
    rw [← (isUnit_of_invertible a).mul_right_inj, ← mul_assoc, ← mul_assoc, mul_invOf_self, mul_one,
      one_mul]
#align invertible_of_invertible_mul invertibleOfInvertibleMul

/-- This is the `Invertible` version of `Units.isUnit_mul_units` -/
abbrev invertibleOfMulInvertible (a b : α) [Invertible (a * b)] [Invertible b] : Invertible a where
  invOf := b * ⅟ (a * b)
  invOf_mul_self := by
    rw [← (isUnit_of_invertible b).mul_left_inj, mul_assoc, mul_assoc, invOf_mul_self, mul_one,
      one_mul]
  mul_invOf_self := by rw [← mul_assoc, mul_invOf_self]
#align invertible_of_mul_invertible invertibleOfMulInvertible

/-- `invertibleOfInvertibleMul` and `invertibleMul` as an equivalence. -/
@[simps apply symm_apply]
def Invertible.mulLeft {a : α} (_ : Invertible a) (b : α) : Invertible b ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfInvertibleMul a _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible.mul_left Invertible.mulLeft
#align invertible.mul_left_apply Invertible.mulLeft_apply
#align invertible.mul_left_symm_apply Invertible.mulLeft_symm_apply

/-- `invertibleOfMulInvertible` and `invertibleMul` as an equivalence. -/
@[simps apply symm_apply]
def Invertible.mulRight (a : α) {b : α} (_ : Invertible b) : Invertible a ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfMulInvertible _ b
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible.mul_right Invertible.mulRight
#align invertible.mul_right_apply Invertible.mulRight_apply
#align invertible.mul_right_symm_apply Invertible.mulRight_symm_apply

instance invertiblePow (m : α) [Invertible m] (n : ℕ) : Invertible (m ^ n) where
  invOf := ⅟ m ^ n
  invOf_mul_self := by rw [← (commute_invOf m).symm.mul_pow, invOf_mul_self, one_pow]
  mul_invOf_self := by rw [← (commute_invOf m).mul_pow, mul_invOf_self, one_pow]
#align invertible_pow invertiblePow

lemma invOf_pow (m : α) [Invertible m] (n : ℕ) [Invertible (m ^ n)] : ⅟ (m ^ n) = ⅟ m ^ n :=
  @invertible_unique _ _ _ _ _ (invertiblePow m n) rfl
#align inv_of_pow invOf_pow

/-- If `x ^ n = 1` then `x` has an inverse, `x^(n - 1)`. -/
def invertibleOfPowEqOne (x : α) (n : ℕ) (hx : x ^ n = 1) (hn : n ≠ 0) : Invertible x :=
  (Units.ofPowEqOne x n hx hn).invertible
#align invertible_of_pow_eq_one invertibleOfPowEqOne

end Monoid

section MonoidWithZero

variable [MonoidWithZero α]

/-- A variant of `Ring.inverse_unit`. -/
@[simp]
theorem Ring.inverse_invertible (x : α) [Invertible x] : Ring.inverse x = ⅟ x :=
  Ring.inverse_unit (unitOfInvertible _)
#align ring.inverse_invertible Ring.inverse_invertible

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero α]

@[simp]
lemma div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a :=
  div_mul_cancel₀ a (nonzero_of_invertible b)
#align div_mul_cancel_of_invertible div_mul_cancel_of_invertible

@[simp]
lemma mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a :=
  mul_div_cancel_right₀ a (nonzero_of_invertible b)
#align mul_div_cancel_of_invertible mul_div_cancel_of_invertible

@[simp]
lemma div_self_of_invertible (a : α) [Invertible a] : a / a = 1 :=
  div_self (nonzero_of_invertible a)
#align div_self_of_invertible div_self_of_invertible

/-- `b / a` is the inverse of `a / b` -/
def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩
#align invertible_div invertibleDiv

-- Porting note (#10618): removed `simp` attribute as `simp` can prove it
lemma invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟ (a / b) = b / a :=
  invOf_eq_right_inv (by simp [← mul_div_assoc])
#align inv_of_div invOf_div

end GroupWithZero

/-- Monoid homs preserve invertibility. -/
def Invertible.map {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [MulOneClass S]
    [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] :
    Invertible (f r) where
  invOf := f (⅟ r)
  invOf_mul_self := by rw [← map_mul, invOf_mul_self, map_one]
  mul_invOf_self := by rw [← map_mul, mul_invOf_self, map_one]
#align invertible.map Invertible.map

/-- Note that the `Invertible (f r)` argument can be satisfied by using `letI := Invertible.map f r`
before applying this lemma. -/
theorem map_invOf {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [Monoid S]
    [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R)
    [Invertible r] [ifr : Invertible (f r)] :
    f (⅟ r) = ⅟ (f r) :=
  have h : ifr = Invertible.map f r := Subsingleton.elim _ _
  by subst h; rfl
#align map_inv_of map_invOf

/-- If a function `f : R → S` has a left-inverse that is a monoid hom,
  then `r : R` is invertible if `f r` is.

The inverse is computed as `g (⅟(f r))` -/
@[simps! (config := .lemmasOnly)]
def Invertible.ofLeftInverse {R : Type*} {S : Type*} {G : Type*} [MulOneClass R] [MulOneClass S]
    [FunLike G S R] [MonoidHomClass G S R] (f : R → S) (g : G) (r : R)
    (h : Function.LeftInverse g f) [Invertible (f r)] : Invertible r :=
  (Invertible.map g (f r)).copy _ (h r).symm
#align invertible.of_left_inverse Invertible.ofLeftInverse
#align invertible.of_left_inverse_inv_of Invertible.ofLeftInverse_invOf

/-- Invertibility on either side of a monoid hom with a left-inverse is equivalent. -/
@[simps]
def invertibleEquivOfLeftInverse {R : Type*} {S : Type*} {F G : Type*} [Monoid R] [Monoid S]
    [FunLike F R S] [MonoidHomClass F R S] [FunLike G S R] [MonoidHomClass G S R]
    (f : F) (g : G) (r : R) (h : Function.LeftInverse g f) :
    Invertible (f r) ≃
      Invertible r where
  toFun _ := Invertible.ofLeftInverse f _ _ h
  invFun _ := Invertible.map f _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible_equiv_of_left_inverse invertibleEquivOfLeftInverse
#align invertible_equiv_of_left_inverse_symm_apply invertibleEquivOfLeftInverse_symm_apply
#align invertible_equiv_of_left_inverse_apply invertibleEquivOfLeftInverse_apply
