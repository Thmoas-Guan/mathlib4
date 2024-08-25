import Qq
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Group.List

open Lean Qq

abbrev smulAndSum {R : Type*} {M : Type*} [SMul R M] [Add M] [Zero M] (l : List (R × M)) : M :=
  (l.map (fun (⟨r, x⟩ : R × M) ↦ r • x)).sum

abbrev smulRightFst {R S M : Type*} [SMul S R] [SMul S M] (l : List (R × M)) (s : S) :
    List (R × M) :=
  List.map (fun (⟨r, x⟩ : R × M) ↦ (s • r, x)) l

-- more typeclass assumptions needed
theorem bar {R S M : Type*} [Add M] [Zero M] [SMul S R] [SMul S M] [SMul R M] [IsScalarTower S R M]
    {x : M} {l : List (R × M)} (h : x = smulAndSum l) (s : S) :
    s • x = smulAndSum (smulRightFst l s) := by
  sorry

abbrev smulLeftFst {R S M : Type*} [SMul R S] [SMul S M] (l : List (R × M)) (s : S) :
    List (S × M) :=
  List.map (fun (⟨r, x⟩ : R × M) ↦ (r • s, x)) l

-- more typeclass assumptions needed
theorem foo {R S M : Type*} [Add M] [Zero M] [SMul R S] [SMul S M] [SMul R M] [IsScalarTower R S M]
    {x : M} {l : List (R × M)} (h : x = smulAndSum l) (s : S) :
    s • x = smulAndSum (smulLeftFst l s) := by
  sorry

partial def parse {v : Level} (M : Q(Type v)) (i : Q(AddMonoid $M)) (x : Q($M)) :
    MetaM (Σ R : Q(Type), Σ _ : Q(SMul $R $M), Σ e : Q(List ($R × $M)), Q($x = smulAndSum $e)) := do
  match x with
  | ~q($x₁ + $x₂) =>
    let ⟨R₁, i₁, l₁, pf₁⟩ ← parse M i x₁
    let ⟨R₂, i₂, l₂, pf₂⟩ ← parse M i x₂
    try
      let _i₁ ← synthInstanceQ q(Coe $R₁ $R₂)
      let l₁' : Q(List ($R₂ × $M)) := q(List.map (fun (⟨r, x⟩ : $R₁ × $M) ↦ ((r : $R₂), x)) $l₁)
      pure ⟨R₂, i₂, q($l₁' ++ $l₂), q(sorry)⟩
    catch _ =>
      let _i₁ ← synthInstanceQ q(Coe $R₂ $R₁)
      let l₂' : Q(List ($R₁ × $M)) := q(List.map (fun (⟨r, x⟩ : $R₂ × $M) ↦ ((r : $R₁), x)) $l₂)
      pure ⟨R₁, i₁, q($l₁ ++ $l₂'), q(sorry)⟩
  | ~q(@HSMul.hSMul _ _ _ (@instHSMul $S _ $iS) $s $y) =>
    let ⟨R, iR, l, pf⟩ ← parse M i y
    try
      let _i₃ ← synthInstanceQ q(SMul $S $R)
      let _i₄ ← synthInstanceQ q(IsScalarTower $S $R $M)
      let l' : Q(List ($R × $M)) := q(smulRightFst $l $s)
      let pf' : Q($s • $y = smulAndSum $l') := q(bar $pf $s)
      pure ⟨R, iR, l', pf'⟩
    catch _ =>
      let _i₃ ← synthInstanceQ q(SMul $R $S)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R $S $M)
      let _i₅ ← synthInstanceQ q(SMulCommClass $R $S $M)
      let l' : Q(List ($S × $M)) := q(smulLeftFst $l $s)
      let pf' : Q($s • $y = smulAndSum $l') := q(foo $pf $s)
      pure ⟨S, iS, l', pf'⟩
  | e => pure ⟨q(Nat), q(AddMonoid.toNatSMul), q([(1, $e)]), q(sorry)⟩
