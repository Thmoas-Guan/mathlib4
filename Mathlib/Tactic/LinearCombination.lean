/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic

/-!
# linear_combination Tactic

In this file, the `linear_combination` tactic is created.  This tactic, which
works over `CommRing`s, attempts to simplify the target by creating a linear combination
of a list of equalities and subtracting it from the target.  There is also an option for
allowing the user to specify a normalization tactic (chosen as `ring` by default).

Over ordered algebraic objects (such as `LinearOrderedCommRing`), taking linear combinations of
inequalities is also supported.

## Implementation Notes

This tactic works by creating a weighted sum of the given equations with the
given coefficients.  Then, it subtracts the right side of the weighted sum
from the left side so that the right side equals 0, and it does the same with
the target.  Afterwards, it sets the goal to be the equality between the
lefthand side of the new goal and the lefthand side of the new weighted sum.
Lastly, calls a normalization tactic on this target.

## References

* <https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/Linear.20algebra.20tactic/near/213928196>

-/

@[inherit_doc Mathlib.Tactic.Ring.ring1] syntax (name := ring1Conv) "ring1" : conv

-- move this
open Lean Meta Elab Tactic Qq Mathlib.Tactic in
/-- Elaborator for `ring1` conv tactic. -/
@[tactic ring1Conv] def elabRing1Conv : Tactic := fun _ ↦ withMainContext do
  let e ← Conv.getLhs
  let α ← inferType e
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ← synthInstanceQ q(CommSemiring $α)
  let c ← Ring.mkCache sα
  let ⟨a, _, pa⟩ ← (Ring.eval sα c e).run .default
  Conv.updateLhs a pa

-- move to Mathlib.Lean.Expr.Basic
/-- `Lean.Expr.lt? e` takes `e : Expr` as input.
If `e` represents `a < b`, then it returns `some (t, a, b)`, where `t` is the Type of `a`,
otherwise, it returns `none`. -/
@[inline] def Lean.Expr.lt? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) ← p.app4? ``LT.lt
  return (type, lhs, rhs)

namespace Mathlib.Tactic.LinearCombination
open Lean hiding Rat
open Elab Meta Term

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

def _root_.Lean.Expr.relType (e : Expr) : Option (RelType × Expr) :=
  match e.eq? with
  | some (ty, _, _) => (Eq, ty)
  | none =>
  match e.le? with
  | some (ty, _, _) => (Le, ty)
  | none =>
  match e.lt? with
  | some (ty, _, _) => (Lt, ty)
  | none => none

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

/-- Result of `expandLinearCombo`, either an equality/inequality proof or a value. -/
inductive Expanded
  /-- A proof of `a = b`, `a ≤ b`, or `a < b` (according to the value of `RelType`). -/
  | proof (rel : RelType) (pf : Syntax.Term)
  /-- A value, equivalently a proof of `c = c`. -/
  | const (c : Syntax.Term)

/--
Performs macro expansion of a linear combination expression,
using `+`/`-`/`*`/`/` on equations and values.
* `.proof Eq p` means that `p` is a syntax corresponding to a proof of an equation.
  For example, if `h : a = b` then `expandLinearCombo (2 * h)` returns `.proof (c_add_pf 2 h)`
  which is a proof of `2 * a = 2 * b`.
  Similarly, `.proof Le p` means that `p` is a syntax corresponding to a proof of a non-strict
  inequality, and `.proof Lt p` means that `p` is a syntax corresponding to a proof of a strict
  inequality.
* `.const c` means that the input expression is not an equation but a value.
-/
partial def expandLinearCombo (ty : Expr) (stx : Syntax.Term) : TermElabM Expanded := withRef stx do
  match stx with
  | `(($e)) => expandLinearCombo ty e
  | `($e₁ + $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ + $c₂)
    | .proof rel₁ p₁, .proof rel₂ p₂ =>
      let (rel, n) := rel₁.addRelRelData rel₂
      let i := mkIdent n
      .proof rel <$> ``($i $p₁ $p₂)
    | _, _ => throwError "'linear_combination' is agnostic to the addition of constants"
  | `($e₁ - $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ - $c₂)
    | .proof _ _, .const _ =>
      throwError "'linear_combination' is agnostic to the subtraction of constants"
    | .const _, .proof _ _ =>
      throwError "'linear_combination' is agnostic to the addition of constants"
    | .proof rel₁ p₁, .proof Eq p₂ =>
      let (rel, n) := rel₁.subRelEqData
      let i := mkIdent n
      .proof rel <$> ``($i $p₁ $p₂)
    | .proof _ _, .proof _ _ =>
      throwError "coefficients of inequalities in 'linear_combination' must be nonnegative"
  | `(-$e) => do
      match ← expandLinearCombo ty e with
      | .const c => .const <$> `(-$c)
      | .proof Eq p => .proof Eq <$> ``(neg_eq $p)
      | .proof _ _ =>
        throwError "coefficients of inequalities in 'linear_combination' must be nonnegative"
  | `($e₁ * $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ * $c₂)
    | .proof rel₁ p₁, .const c₂ =>
      let (rel, n) := rel₁.mulRelConstData
      let i := mkIdent n
      .proof rel <$> ``($i $p₁ $c₂)
    | .const c₁, .proof rel₂ p₂ =>
      let (rel, n) := rel₂.mulConstRelData
      let i := mkIdent n
      .proof rel <$> ``($i $p₂ $c₁)
    | .proof _ _, .proof _ _ => throwError "'linear_combination' supports only linear operations"
  | `($e⁻¹) => do
    -- special-case inversion
    match ← expandLinearCombo ty e with
    | .const c => .const <$> `($c⁻¹)
    | _ => throwError "'linear_combination' supports only linear operations"
  | `($e₁ / $e₂) => do
    match ← expandLinearCombo ty e₁, ← expandLinearCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ / $c₂)
    | .proof rel₁ p₁, .const c₂ =>
      let (rel, n) := rel₁.divRelConstData
      let i := mkIdent n
      .proof rel <$> ``($i $p₁ $c₂)
    | _, .proof _ _ => throwError "'linear_combination' supports only linear operations"
  | e =>
    -- We have the expected type from the goal, so we can fully synthesize this leaf node.
    withSynthesize do
      -- It is OK to use `ty` as the expected type even if `e` is a proof.
      -- The expected type is just a hint.
      let c ← withSynthesizeLight <| Term.elabTerm e ty
      match (← whnfR (← inferType c)).relType with
      | some (rel, _) => .proof rel <$> c.toSyntax
      | none => .const <$> c.toSyntax

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

/-! ### Default discharger tactic for combination -/

theorem nonpos_intRawCast {α : Type*} [LinearOrderedRing α] {a : ℕ} :
    (Int.rawCast (Int.negOfNat a) : α) + 0 ≤ 0 := by
  simp

theorem nonpos_ratRawCast {α : Type*} [LinearOrderedField α] {a b : ℕ} :
    (Rat.rawCast (Int.negOfNat a) b : α) + 0 ≤ 0 := by
  simp [div_nonpos_iff]

theorem neg_intRawCast {α : Type*} [LinearOrderedRing α] {a : ℕ} :
    (Int.rawCast (Int.negOfNat a.succ) : α) + 0 < 0 := by
  simp [-Nat.succ_eq_add_one]

theorem neg_ratRawCast {α : Type*} [LinearOrderedField α] {a b : ℕ} :
    (Rat.rawCast (Int.negOfNat a.succ) b.succ : α) + 0 < 0 := by
  simp [div_neg_iff, -Nat.succ_eq_add_one]

-- TODO
-- make finishing-only tactic (note there is `Tactic.liftMetaFinishingTactic`)
-- make a `Tactic.Tactic` everywhere relevant, not a `Syntax.Tactic`
-- fail better with negative coefficients or with coefficients which just don't work

def lhsRelZero (int_lem rat_lem : Name) : Tactic.TacticM Unit :=
    Tactic.liftMetaTactic <| fun g ↦ do
  let e ← g.getType
  let whnfEType ← withReducible do whnf e
  let leftSummand := whnfEType.getAppArgs[2]!.getAppArgs[4]!
  let int? : Bool := leftSummand.isAppOfArity ``Int.rawCast 3
  let lem : Name := if int? then int_lem else rat_lem
  let pf ← mkConstWithFreshMVarLevels lem
  g.apply pf

elab "nonpos_rawcast" : tactic => lhsRelZero ``nonpos_intRawCast ``nonpos_ratRawCast
elab "neg_rawcast" : tactic => lhsRelZero ``neg_intRawCast ``neg_ratRawCast

/-- Implementation of `linear_combination`. -/
def elabLinearCombination (tk : Syntax)
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term) :
    Tactic.TacticM Unit := Tactic.withMainContext do
  let eType ← withReducible <| (← Tactic.getMainGoal).getType'
  let some (goalRel, ty) := eType.relType |
    throwError "'linear_combination' only proves equalities and inequalities"
  let (hypRel, p) ← match input with
  | none => Prod.mk Eq <$>  `(Eq.refl 0)
  | some e =>
    match ← expandLinearCombo ty e with
    | .const _ => throwError "To run 'linear_combination' without hypotheses, call it without input"
<<<<<<< HEAD
    | .proof p => pure p
  let norm := norm?.getD (Unhygienic.run <| withRef tk `(tactic| ring1))
=======
    | .proof hypRel p => pure (hypRel, p)
  let defaultTac : Unhygienic Syntax.Tactic :=
    match goalRel with
    | Eq => `(tactic | ring1)
      -- FIXME do I need parentheses around `(conv_lhs => ring1)`?
    | Le => `(tactic | ((conv_lhs => ring1); all_goals nonpos_rawcast))
    | Lt => `(tactic | ((conv_lhs => ring1); all_goals neg_rawcast))
  let norm := norm?.getD (Unhygienic.run <| withRef tk defaultTac)
>>>>>>> 6ca04b6e62 (wip)
  Term.withoutErrToSorry <| Tactic.evalTactic <| ← withFreshMacroScope <|
  let exp1 :=
    match hypRel.relImpRelData goalRel with
    | none => throwError "cannot prove an equality from inequality hypotheses"
    | some n =>
      let i := mkIdent n
      `(tactic| (refine $i $p ?a; case' a => $norm:tactic))
  match exp? with
  | some n =>
    if n.getNat = 1 then
      exp1
    else
      match hypRel with
      | Eq => `(tactic| (refine eq_of_add_pow $n $p ?a; case' a => $norm:tactic))
      | _ => throwError
        "linear combination tactic not implemented for exponentiation of inequality goals"
  | _ => exp1

/--
The `(norm := $tac)` syntax says to use `tac` as a normalization postprocessor for
`linear_combination`. The default normalizer is `ring1`, but you can override it with `ring_nf`
to get subgoals from `linear_combination` or with `skip` to disable normalization.
-/
syntax normStx := atomic(" (" &"norm" " := ") withoutPosition(tactic) ")"

/--
The `(exp := n)` syntax for `linear_combination` says to take the goal to the `n`th power before
subtracting the given combination of hypotheses.
-/
syntax expStx := atomic(" (" &"exp" " := ") withoutPosition(num) ")"

/--
`linear_combination` attempts to simplify the target by creating a linear combination
  of a list of equalities and subtracting it from the target.
  The tactic will create a linear
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `normalize` field of the
  configuration is set to false, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.

Note: The left and right sides of all the equalities should have the same
  type, and the coefficients should also have this type.  There must be
  instances of `Mul` and `AddGroup` for this type.

* The input `e` in `linear_combination e` is a linear combination of proofs of equalities,
  given as a sum/difference of coefficients multiplied by expressions.
  The coefficients may be arbitrary expressions.
  The expressions can be arbitrary proof terms proving equalities.
  Most commonly they are hypothesis names `h1, h2, ...`.
* `linear_combination (norm := tac) e` runs the "normalization tactic" `tac`
  on the subgoal(s) after constructing the linear combination.
  * The default normalization tactic is `ring1`, which closes the goal or fails.
  * To get a subgoal in the case that it is not immediately provable, use
    `ring_nf` as the normalization tactic.
  * To avoid normalization entirely, use `skip` as the normalization tactic.
* `linear_combination (exp := n) e` will take the goal to the `n`th power before subtracting the
  combination `e`. In other words, if the goal is `t1 = t2`, `linear_combination (exp := n) e`
  will change the goal to `(t1 - t2)^n = 0` before proceeding as above.

Example Usage:
```
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination (norm := ring_nf) -2*h2
  /- Goal: x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination (norm := skip) 2*h1
  simp

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination 3 * h a b + hqc
```
-/
syntax (name := linearCombination) "linear_combination"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| linear_combination%$tk $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>
    elabLinearCombination tk tac n e

end Mathlib.Tactic.LinearCombination
