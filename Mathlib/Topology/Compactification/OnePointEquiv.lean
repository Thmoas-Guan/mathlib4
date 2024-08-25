/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Compactification.OnePoint

/-!
# OnePoint Compactification and Projectivization

We construct a set-theoretic equivalence between
`OnePoint K` and the projectivization `ℙ K (Fin 2 → K)`
for an arbitrary field `K`.

(This equivalence can be extended to a homeomorphism
in the case `K = ℝ`, where `OnePoint ℝ` gets the topology of one-point compactification.
This result is to be added in a different file.)

## Main definitions

* `divOnePoint`: Division on `K` taking values in `OnePoint K`.
* `divSlope`: Lifting `divOnePoint` to a map `ℙ K (Fin 2 → K) → OnePoint K`.

## Main results

* `ℙ K (Fin 2 → K) ≃ OnePoint K`

## Tags

one-point extension, projectivization
-/


open scoped LinearAlgebra.Projectivization OnePoint
open Projectivization Classical

/-!
### Definition and basic properties

In this section we define `divOnePoint` and prove that it lifts to `divSlope`.
-/

/-- A modified division from a `DivisionRing` to its `OnePoint` extension,
so as to satisfy `1 ÷ 0 = ∞`. -/
noncomputable def divOnePoint {K : Type} [DivisionRing K] (a : K) (r : K): OnePoint K :=
  ite (r ≠ 0) (a / r) ∞

/-- Uncurried version of `divOnePoint`, with nonzeroness assumption. -/
noncomputable def divOnePoint' {K : Type} [DivisionRing K]
  (u : {v : Fin 2 → K // v ≠ 0}) : OnePoint K :=
  if u.1 1 ≠ 0 then some (u.1 0 / u.1 1) else ∞

/-- Notation `÷` showing that `div_onePoint` is distinct from
the ordinary division `/` of a `DivisionRing`. -/
infix:50 " ÷ " => divOnePoint

/-- `div_onePoint` can be lifted to the projective line (see `divSlope`.) -/
lemma divOnePoint_lifts {K : Type} [Field K] (a b : {v : Fin 2 → K // v ≠ 0})
    (h : ∃ c : Kˣ, (fun m : Kˣ ↦ m • b.1) c = a.1) :
    (fun u ↦ u.1 0 ÷ u.1 1) a = (fun u ↦ u.1 0 ÷ u.1 1) b := by
  obtain ⟨c,hc⟩ := h
  simp_all only
  rw [← hc]; unfold divOnePoint; simp only [ne_eq, Fin.isValue, Pi.smul_apply, ite_not]
  split_ifs with hbc hb hb
  · rfl
  · simp_all only [ne_eq, OnePoint.infty_ne_coe]
    apply hb;exact (Units.mul_right_eq_zero c).mp hbc
  · rw [hb] at hbc;simp at hbc
  · apply congrArg some
    field_simp
    show c * b.1 0 * b.1 1 = b.1 0 * (c * b.1 1)
    ring

/-- Equivalence between the projective line and the one-point extension. -/
noncomputable def divSlope {K : Type} [Field K] (p : ℙ K (Fin 2 → K)) : OnePoint K :=
  Quotient.lift (fun u => divOnePoint (u.1 0) (u.1 1)) divOnePoint_lifts p

/-! ### Equivalence
We establish the equivalence between `OnePoint K` and `ℙ K (Fin 2 → K)` for a field `K`.
-/

/-- In a nonzero pair, if one coordinate is 0 then the other is nonzero. -/
lemma not_both_zero {K : Type} [Zero K]
    (a : {v : Fin 2 → K // v ≠ 0}) (h : a.1 1 = 0) : a.1 0 ≠ 0 := by
  intro hc; apply a.2; ext s
  cases (Nat.le_one_iff_eq_zero_or_eq_one.mp (Fin.is_le s)) with
  |inl hl =>
    have : s = 0 := by apply Fin.eq_of_val_eq;tauto
    subst this;simp_all
  |inr hr =>
    have : s = 1 := by apply Fin.eq_of_val_eq;tauto
    subst this;simp_all

instance {K : Type} [DivisionRing K] : Setoid ({v : Fin 2 → K // v ≠ 0}) :=
  projectivizationSetoid K (Fin 2 → K)

/-- `divSlope` respects projective equivalence. -/
lemma divSlope_inj_lifted {K : Type} [Field K]
    (a b : {v : Fin 2 → K // v ≠ 0}) :
    divSlope ⟦a⟧ = divSlope ⟦b⟧ →
    (⟦a⟧ : Quotient (projectivizationSetoid K (Fin 2 → K))) = ⟦b⟧ := by
  unfold divSlope
  intro h
  repeat rw [Quotient.lift_mk] at h
  apply Quotient.sound
  unfold divOnePoint at h
  split_ifs at h with g₀ g₁ g₂
  · use Units.mk ((a.1 1) / (b.1 1)) ((b.1 1) / (a.1 1)) (by field_simp) (by field_simp)
    ext s
    cases (Nat.le_one_iff_eq_zero_or_eq_one.mp (Fin.is_le s)) with
    |inl hl =>
      have : s = 0 := Fin.eq_of_val_eq hl
      subst this; simp_all only [ne_eq, Fin.val_zero, Pi.smul_apply, Units.smul_mk_apply,
        smul_eq_mul];field_simp
      have h' : (a.1 0 / a.1 1) = (b.1 0 / b.1 1) := by
        apply Option.some_injective; tauto
      field_simp at h';rw [h',mul_comm]
    |inr hr =>
      have : s = 1 := Fin.eq_of_val_eq hr
      subst this; simp_all
  · simp at h
  · simp at h
  · simp_all only [ne_eq, Decidable.not_not]
    have h₀ : a.1 0 ≠ 0 := by apply not_both_zero;tauto
    have h₁ : b.1 0 ≠ 0 := by apply not_both_zero;tauto
    use Units.mk ((a.1 0) / (b.1 0)) ((b.1 0) / (a.1 0)) (by field_simp) (by field_simp)
    simp only [ne_eq, Fin.isValue, Units.smul_mk_apply]
    apply List.ofFn_inj.mp; simp only [Fin.isValue, List.ofFn_succ, Pi.smul_apply, smul_eq_mul,
      Fin.succ_zero_eq_one, List.ofFn_zero, List.cons.injEq, and_true]
    rw [g₀,g₂]; field_simp

/-- Over any field `K`, `divSlope` is injective. -/
lemma divSlope_injective {K : Type} [Field K] : Function.Injective (@divSlope K _) :=
  Quotient.ind (λ a ↦ Quotient.ind (divSlope_inj_lifted a))

/-- An inverse of `divSlope`. -/
def slope_inv {K : Type} [DivisionRing K] (p : OnePoint K) : ℙ K (Fin 2 → K) := match p with
|some t => mk' K ⟨![t, 1], by simp⟩
|∞      => mk' K ⟨![1, 0], by simp⟩


/-- `slope_inv` is an inverse of `divSlope`. -/
lemma divSlope_inv {K : Type} [Field K] : Function.LeftInverse (@divSlope K _) slope_inv := by
  intro a
  have g₀ :       divOnePoint' ⟨![(1:K), 0], by simp⟩ = ∞  := by unfold divOnePoint';simp
  have g₁ (t:K) : divOnePoint' ⟨![t, 1], by simp⟩ = some t := by unfold divOnePoint';simp
  cases a with
  |none => exact g₀
  |some t => exact g₁ t

/-- `divSlope` is surjective. -/
lemma divSlope_surjective {K : Type} [Field K]:
    Function.Surjective (@divSlope K _) :=
  λ r ↦ ⟨slope_inv r, divSlope_inv r⟩

/-- An equivalence between the one-point extension of a field `K`
and the projective line over `K`. -/
noncomputable instance divSlope_equiv {K : Type} [Field K] :
  OnePoint K ≃ ℙ K (Fin 2 → K) where
  toFun     := slope_inv
  invFun    := divSlope
  left_inv  := divSlope_inv
  right_inv := Function.rightInverse_of_injective_of_leftInverse
    divSlope_injective divSlope_inv
