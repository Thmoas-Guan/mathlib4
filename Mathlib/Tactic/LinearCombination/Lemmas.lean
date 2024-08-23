/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic

/-!
# Lemmas for the linear_combination tactic
-/

namespace Mathlib.Tactic.LinearCombination
open Lean

variable {α : Type*} {a a' a₁ a₂ b b' b₁ b₂ c : α}

/-! ### Addition -/

theorem add_eq_eq [Add α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl

theorem add_le_eq [Add α] [LE α] [CovariantClass α α (Function.swap (· + ·)) (· ≤ ·)]
    (p₁ : (a₁:α) ≤ b₁) (p₂ : a₂ = b₂) : a₁ + a₂ ≤ b₁ + b₂ :=
  p₂ ▸ add_le_add_right p₁ b₂

theorem add_eq_le [Add α] [LE α] [CovariantClass α α (· + ·) (· ≤ ·)]
    (p₁ : (a₁:α) = b₁) (p₂ : a₂ ≤ b₂) : a₁ + a₂ ≤ b₁ + b₂ :=
  p₁ ▸ add_le_add_left p₂ b₁

theorem add_lt_eq [Add α] [LT α] [CovariantClass α α (Function.swap (· + ·)) (· < ·)]
    (p₁ : (a₁:α) < b₁) (p₂ : a₂ = b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₂ ▸ add_lt_add_right p₁ b₂

theorem add_eq_lt [Add α] [LT α] [CovariantClass α α (· + ·) (· < ·)] {a₁ b₁ a₂ b₂ : α}
    (p₁ : a₁ = b₁) (p₂ : a₂ < b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₁ ▸ add_lt_add_left p₂ b₁

/-! ### Subtraction -/

theorem sub_eq_eq [Sub α] (p₁ : (a₁:α) = b₁) (p₂ : a₂ = b₂) : a₁ - a₂ = b₁ - b₂ := p₁ ▸ p₂ ▸ rfl

theorem sub_le_eq [AddGroup α] [LE α] [CovariantClass α α (Function.swap (· + ·)) (· ≤ ·)]
    (p₁ : (a₁:α) ≤ b₁) (p₂ : a₂ = b₂) : a₁ - a₂ ≤ b₁ - b₂ :=
  p₂ ▸ sub_le_sub_right p₁ b₂

theorem sub_lt_eq [AddGroup α] [LT α] [CovariantClass α α (Function.swap (· + ·)) (· < ·)]
    (p₁ : (a₁:α) < b₁) (p₂ : a₂ = b₂) : a₁ - a₂ < b₁ - b₂ :=
  p₂ ▸ sub_lt_sub_right p₁ b₂

/-! ### Negation -/

theorem neg_eq [Neg α] (p : (a:α) = b) : -a = -b := p ▸ rfl

/-! ### Multiplication -/

theorem mul_eq_const [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl

theorem mul_le_const [Mul α] [Zero α] [Preorder α] [MulPosMono α] (p : b ≤ c) (a : α)
    (ha : 0 ≤ a := by positivity) : b * a ≤ c * a :=
  mul_le_mul_of_nonneg_right p ha

theorem mul_lt_const [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α] (p : b < c) (a : α)
    (ha : 0 < a := by positivity) : b * a < c * a :=
  mul_lt_mul_of_pos_right p ha

-- FIXME allow for this variant
theorem mul_lt_const' [Mul α] [Zero α] [Preorder α] [MulPosMono α] (p : b < c) (a : α)
    (ha : 0 ≤ a := by positivity) : b * a ≤ c * a :=
  mul_le_mul_of_nonneg_right p.le ha

theorem mul_const_eq [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl

theorem mul_const_le [Mul α] [Zero α] [Preorder α] [PosMulMono α] (p : b ≤ c) (a : α)
    (ha : 0 ≤ a := by positivity) : a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left p ha

theorem mul_const_lt [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α] (p : b < c) (a : α)
    (ha : 0 < a := by positivity) : a * b < a * c :=
  mul_lt_mul_of_pos_left p ha

-- FIXME allow for this variant
theorem mul_const_lt' [Mul α] [Zero α] [Preorder α] [PosMulMono α] (p : b < c) (a : α)
    (ha : 0 ≤ a := by positivity) : a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left p.le ha

/-! ### Division -/

theorem div_eq_const [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl

theorem div_le_const [LinearOrderedSemifield α] (p : b ≤ c) (a : α)
    (ha : 0 ≤ a := by positivity) : b / a ≤ c / a :=
  div_le_div_of_nonneg_right p ha

theorem div_lt_const [LinearOrderedSemifield α] (p : b < c) (a : α)
    (ha : 0 < a := by positivity) : b / a < c / a :=
  div_lt_div_of_pos_right p ha

-- FIXME allow for this variant
theorem div_lt_const' [LinearOrderedSemifield α] (p : b < c) (a : α)
    (ha : 0 ≤ a := by positivity) : b / a ≤ c / a :=
  div_le_div_of_nonneg_right p.le ha

inductive RelType
  | Eq
  | Le
  | Lt
  deriving Repr, ToExpr

export RelType (Eq Le Lt)

def RelType.addRelRelData : RelType → RelType → RelType × Name
  | Eq, Eq => (Eq, ``add_eq_eq)
  | Eq, Le => (Le, ``add_eq_le)
  | Eq, Lt => (Lt, ``add_eq_lt)
  | Le, Eq => (Le, ``add_le_eq)
  | Le, Le => (Le, ``add_le_add)
  | Le, Lt => (Lt, ``add_lt_add_of_le_of_lt)
  | Lt, Eq => (Lt, ``add_lt_eq)
  | Lt, Le => (Lt, ``add_lt_add_of_lt_of_le)
  | Lt, Lt => (Lt, ``add_lt_add)

def RelType.subRelEqData : RelType → RelType × Name
  | Eq => (Eq, ``sub_eq_eq)
  | Le => (Le, ``sub_le_eq)
  | Lt => (Lt, ``sub_lt_eq)

def RelType.mulConstRelData : RelType → RelType × Name
  | Eq => (Eq, ``mul_const_eq)
  | Le => (Le, ``mul_const_le)
  | Lt => (Lt, ``mul_const_lt)

def RelType.mulRelConstData : RelType → RelType × Name
  | Eq => (Eq, ``mul_eq_const)
  | Le => (Le, ``mul_le_const)
  | Lt => (Lt, ``mul_lt_const)

def RelType.divRelConstData : RelType → RelType × Name
  | Eq => (Eq, ``div_eq_const)
  | Le => (Le, ``div_le_const)
  | Lt => (Lt, ``div_lt_const)

theorem eq_trans₃ (p : (a:α) = b) (p₁ : a = a') (p₂ : b = b') : a' = b' := p₁ ▸ p₂ ▸ p

theorem eq_of_eq [AddGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢
  rw [sub_eq_zero] at H
  exact H.trans p

theorem le_of_le [LinearOrderedAddCommGroup α] (p : (a:α) ≤ b) (H : (a' - b') - (a - b) ≤ 0) :
    a' ≤ b' := by
  rw [sub_nonpos] at H
  rw [← sub_nonpos] at p ⊢
  exact H.trans p

theorem le_of_eq [LinearOrderedAddCommGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) ≤ 0) :
    a' ≤ b' :=
  le_of_le p.le H

theorem le_of_lt [LinearOrderedAddCommGroup α] (p : (a:α) < b) (H : (a' - b') - (a - b) ≤ 0) :
    a' ≤ b' :=
  le_of_le p.le H

theorem lt_of_le [LinearOrderedAddCommGroup α] (p : (a:α) ≤ b) (H : (a' - b') - (a - b) < 0) :
    a' < b' := by
  rw [← sub_nonpos] at p
  rw [← sub_neg]
  rw [sub_neg] at H
  exact H.trans_le p

theorem lt_of_eq [LinearOrderedAddCommGroup α] (p : (a:α) = b) (H : (a' - b') - (a - b) < 0) :
    a' < b' :=
  lt_of_le p.le H

theorem lt_of_lt [LinearOrderedAddCommGroup α] (p : (a:α) < b) (H : (a' - b') - (a - b) ≤ 0) :
    a' < b' := by
  rw [sub_nonpos] at H
  rw [← sub_neg] at p ⊢
  exact lt_of_le_of_lt H p

def RelType.relImpRelData : RelType → RelType → Option Name
  | Eq, Eq => ``eq_of_eq
  | Eq, Le => ``le_of_eq
  | Eq, Lt => ``lt_of_eq
  | Le, Eq => none
  | Le, Le => ``le_of_le
  | Le, Lt => ``lt_of_le
  | Lt, Eq => none
  | Lt, Le => ``le_of_lt
  | Lt, Lt => ``lt_of_lt

theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : ℕ) (p : (a:α) = b)
    (H : (a' - b')^n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

end Mathlib.Tactic.LinearCombination
