import Mathlib

open Mathlib.Tactic.LinearCombination

macro "module" : tactic =>
  `(tactic | (try simp only [← mul_smul, smul_add, add_smul, smul_sub, sub_smul, mul_add, add_mul, sub_mul, mul_sub, smul_zero, zero_smul, one_smul]; ring_nf; abel))

variable {V : Type*} [AddCommGroup V] {K : Type*}
  {t u v w x y : V} {a b c μ ν ρ : K}

/-! # Commutative ring -/

section
variable [CommRing K] [Module K V]

example (h : a ^ 2 + b ^ 2 = 1) :
    a • (a • x - b • y) + (b • a • y + b • b • x) = x := by
  -- `linear_combination h • x`
  apply eq_of_add (congr($h • x):)
  module

-- from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/linear_combination.20for.20groups/near/437042918
example : (1 + a ^ 2) • (v + w) - a • (a • v - w) = v + (1 + a + a ^ 2) • w := by module

-- from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/smul.20diamond/near/457163013
example : (4 : ℤ) • v = (4 : K) • v := by sorry -- module
example : (4 : ℕ) • v = (4 : K) • v := by sorry -- module

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

end

/-! # Characteristic-zero field -/

example [Field K] [CharZero K] [Module K V]
    (h₁ : t - u = -(v - w))
    (h₂ : t + u = v + w) :
    t = w := by
  -- `linear_combination 2⁻¹ • h₁ + 2⁻¹ • h₂`
  apply eq_of_add (congr((2:K)⁻¹ • $h₁ + (2:K)⁻¹ • $h₂):)
  trans ((1:K) - 2⁻¹ - 2⁻¹) • t + (-(1:K) + 2⁻¹ + 2⁻¹) • w + ((2:K)⁻¹ - 2⁻¹) • v + ((2:K)⁻¹ - 2⁻¹) • u
  · simp only [sub_smul, add_smul, neg_smul, one_smul, smul_add, smul_sub, smul_neg]
    abel
  trans (0:K) • t + (0:K) • w + (0:K) • v + (0:K) • u
  · congrm ?_ • _ + ?_ • _ + ?_ • _ + ?_ • _ <;> ring
  · simp only [zero_smul]
    abel

/-! # Linearly ordered field -/

example [LinearOrderedField K] [Module K V]
    (h₁ : 1 = a ^ 2 + b ^ 2)
    (h₂ : 1 - a ≠ 0)
    (h₃ : 2 ^ 2 * b ^ 2 + 4 * (1 - a) ^ 2 ≠ 0) :
    ((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ • (4:K) • ((2 / (1 - a)) • y)
    + ((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ • ((2 / (1 - a)) ^ 2 * b ^ 2 - 4) • x
    = a • x + y := by
  -- `linear_combination (h₁ * (b ^ 2 + (1 - a) ^ 2)⁻¹) • (y + (a - 1) • x)`
  apply eq_of_add (congr(($h₁ * (b ^ 2 + (1 - a) ^ 2)⁻¹) • (y + (a - 1) • x)):)
  trans
        ((((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ * (4 * (2 / (1 - a)))) - 1
      + (a ^ 2 + b ^ 2 - 1) * (b ^ 2 + (1 - a) ^ 2)⁻¹) • y
      + ((((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ * ((2 / (1 - a)) ^ 2 * b ^ 2))
      - (((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ * 4)
      - a
      + ((a ^ 2 + b ^ 2 - 1) * (b ^ 2 + (1 - a) ^ 2)⁻¹ * (a - 1))) • x
  · simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_add, add_smul, smul_sub,
      sub_smul, ← mul_smul, one_smul, one_mul, mul_one]
    abel
  trans (0:K) • y + (0:K) • x
  · congrm ?_ • _ + ?_ • _
    · field_simp
      ring
    · field_simp
      ring
  · simp only [zero_smul]
    abel
