/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-! # Tests for the module-normalization tactic -/

open Mathlib.Tactic.LinearCombination

variable {V : Type*} [AddCommGroup V] {K : Type} -- TODO generalize universes
  {t u v w x y : V} {a b c μ ν ρ : K}

/-! # Commutative ring -/

section
variable [CommRing K] [Module K V]

example : x + y = y + x := by module

example : x + 2 • x = 2 • x + x := by module

example : a • x + b • x = (a + b) • x := by module

example : a • x - b • x = (a - b) • x := by module

example : a • x - b • y = a • x + (-b) • y := by module

example : -x + x = 0 := by module

example : 2 • a • x = a • 2 • x := by module

-- from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/linear_combination.20for.20groups/near/437042918
example : (1 + a ^ 2) • (v + w) - a • (a • v - w) = v + (1 + a + a ^ 2) • w := by module

example (h : a = b) : a • x = b • x := by
  -- `linear_combination h • x`
  apply eq_of_add (congr($h • x):)
  module

example (h : a ^ 2 + b ^ 2 = 1) : a • (a • x - b • y) + (b • a • y + b • b • x) = x := by
  -- `linear_combination h • x`
  apply eq_of_add (congr($h • x):)
  module

-- from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/smul.20diamond/near/457163013
example : (4 : ℤ) • v = (4 : K) • v := by module
example : (4 : ℕ) • v = (4 : K) • v := by module

example : (μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by module

example : (μ - ν) • b • y = μ • (a • x + b • y) - (a • μ • x + b • ν • y) := by module

example (h1 : a • x + b • y = 0) (h2 : a • μ • x + b • ν • y = 0) :
    (μ - ν) • a • x = 0 := by
  -- `linear_combination h2 - ν • h1`
  apply eq_of_add (congr($h2 - ν • $h1):)
  module

example (h1 : 0 • z + a • x + b • y = 0) (h2 : 0 • ρ • z + a • μ • x + b • ν • y = 0) :
    (μ - ν) • a • x = 0 := by
  -- `linear_combination h2 - ν • h1`
  apply eq_of_add (congr($h2 - ν • $h1):)
  module

example (h1 : a • x + b • y = 0) (h2 : a • μ • x + b • ν • y = 0) :
    (μ - ν) • b • y = 0 := by
  -- `linear_combination μ • h1 + h2`
  apply eq_of_add (congr(μ • $h1 - $h2):)
  module

example
    (h1 : a • x + b • y + c • z = 0)
    (h2 : a • μ • x + b • ν • y + c • ρ • z = 0)
    (h3 : a • μ • μ • x + b • ν • ν • y + c • ρ • ρ • z = 0) :
    (μ - ν) • (μ - ρ) • a • x = 0 := by
  apply eq_of_add (congr($h3 - (ν + ρ) • $h2 + ν • ρ • $h1):)
  module

example
    (h1 : a • x + b • y + c • z = 0)
    (h2 : a • μ • x + b • ν • y + c • ρ • z = 0)
    (h3 : a • μ • μ • x + b • ν • ν • y + c • ρ • ρ • z = 0) :
    (μ - ν) • (ν - ρ) • b • y = 0 := by
  apply eq_of_add (congr(- $h3 + (μ + ρ) • $h2 - μ • ρ • $h1):)
  module

example
    (h1 : a • x + b • y + c • z = 0)
    (h2 : a • μ • x + b • ν • y + c • ρ • z = 0)
    (h3 : a • μ • μ • x + b • ν • ν • y + c • ρ • ρ • z = 0) :
    (μ - ρ) • (ν - ρ) • c • z = 0 := by
  apply eq_of_add (congr($h3 - (μ + ν) • $h2 + μ • ν • $h1):)
  module

/--
error: unsolved goals
V : Type u_1
inst✝² : AddCommGroup V
K : Type
t u v w x y : V
a b c μ ν ρ : K
inst✝¹ : CommRing K
inst✝ : Module K V
⊢ 2 * (a * 1) = 2
-/
#guard_msgs in
example : 2 • a • x = 2 • x := by module

end

/-! # Characteristic-zero field -/

example [Field K] [CharZero K] [Module K V] : (2:K)⁻¹ • x + (3:K)⁻¹ • x + (6:K)⁻¹ • x = x := by
  module

example [Field K] [CharZero K] [Module K V]
    (h₁ : t - u = -(v - w))
    (h₂ : t + u = v + w) :
    t = w := by
  -- `linear_combination 2⁻¹ • h₁ + 2⁻¹ • h₂`
  apply eq_of_add (congr((2:K)⁻¹ • $h₁ + (2:K)⁻¹ • $h₂):)
  module

/-! # Linearly ordered field -/

example [LinearOrderedField K] [Module K V]
    (h₁ : 1 = a ^ 2 + b ^ 2)
    (h₂ : 1 - a ≠ 0) :
    ((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ • (4:K) • ((2 / (1 - a)) • y)
    + ((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ • ((2 / (1 - a)) ^ 2 * b ^ 2 - 4) • x
    = a • x + y := by
  -- `linear_combination (h₁ * (b ^ 2 + (1 - a) ^ 2)⁻¹) • (y + (a - 1) • x)`
  apply eq_of_add (congr(($h₁ * (b ^ 2 + (1 - a) ^ 2)⁻¹) • (y + (a - 1) • x)):)
  match_coeffs
  · field_simp
    ring
  · field_simp
    ring

example [LinearOrderedField K] [Module K V]
    (h₁ : 1 = a ^ 2 + b ^ 2)
    (h₂ : 1 - a ≠ 0) :
    ((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ • (4:K) • ((2 / (1 - a)) • y)
    + ((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ • ((2 / (1 - a)) ^ 2 * b ^ 2 - 4) • x
    = a • x + y := by
  match_coeffs
  · linear_combination (norm := skip) h₁ / (b ^ 2 + (1 - a) ^ 2)
    field_simp
    ring
  · linear_combination (norm := skip) h₁ * (a - 1) / (b ^ 2 + (1 - a) ^ 2)
    field_simp
    ring
