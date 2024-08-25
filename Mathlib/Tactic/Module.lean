import Qq
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.GroupTheory.GroupAction.BigOperators
import Mathlib.Algebra.Algebra.Basic

open Lean Qq

abbrev smulAndSum {R : Type*} {M : Type*} [SMul R M] [Add M] [Zero M] (l : List (R × M)) : M :=
  (l.map (fun (⟨r, x⟩ : R × M) ↦ r • x)).sum

abbrev considerFstAs {S M : Type*} (R : Type*) [CommSemiring S] [Semiring R] [Algebra S R]
    (l : List (S × M)) : List (R × M) :=
  l.map (fun ⟨s, x⟩ ↦ (algebraMap S R s, x))

theorem considerFstAs_pf {S M : Type*} (R : Type*) [CommSemiring S] [Semiring R] [Algebra S R]
    [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower S R M]
    {x : M} {l : List (S × M)} (h : x = smulAndSum l) :
    x = smulAndSum (considerFstAs R l) := by
  simp only [h, smulAndSum, List.map_map]
  congr
  ext ⟨s, x⟩
  simp

theorem concat_pf {R : Type*} {M : Type*} [SMul R M] [AddMonoid M] {l₁ l₂ : List (R × M)}
    {x₁ x₂ : M} (h₁ : x₁ = smulAndSum l₁) (h₂ : x₂ = smulAndSum l₂) :
    x₁ + x₂ = smulAndSum (l₁ ++ l₂) := by
  simp [h₁, h₂, smulAndSum]

abbrev smulRightFst {R S M : Type*} [SMul S R] [SMul S M] (l : List (R × M)) (s : S) :
    List (R × M) :=
  List.map (fun (⟨r, x⟩ : R × M) ↦ (s • r, x)) l

theorem smulRightFst_pf {R S M : Type*} [AddMonoid M] [SMul S R] [DistribSMul S M] [SMul R M]
    [IsScalarTower S R M] {x : M} {l : List (R × M)} (h : x = smulAndSum l) (s : S) :
    s • x = smulAndSum (smulRightFst l s) := by
  simp only [h, smulAndSum, List.smul_sum, List.map_map]
  congr
  ext ⟨r, x⟩
  simp

abbrev smulLeftFst {R S M : Type*} [SMul R S] [SMul S M] (l : List (R × M)) (s : S) :
    List (S × M) :=
  List.map (fun (⟨r, x⟩ : R × M) ↦ (r • s, x)) l

theorem smulLeftFst_pf {R S M : Type*} [AddMonoid M] [SMul R S] [DistribSMul S M] [SMul R M]
    [SMulCommClass S R M] [IsScalarTower R S M]
    {x : M} {l : List (R × M)} (h : x = smulAndSum l) (s : S) :
    s • x = smulAndSum (smulLeftFst l s) := by
  simp only [h, smulAndSum, List.smul_sum, List.map_map]
  congr
  ext ⟨r, x⟩
  simp [smul_comm]

theorem one_pf {M : Type*} [AddMonoid M] (x : M) : x = smulAndSum [((1:ℕ), x)] := by
  simp [smulAndSum]

theorem zero_pf (M : Type*) [AddMonoid M] : (0:M) = smulAndSum (R := Nat) [] := by simp [smulAndSum]

partial def parse {v : Level} (M : Q(Type v)) (i : Q(AddCommMonoid $M)) (x : Q($M)) :
    MetaM (Σ R : Q(Type), Σ _ : Q(Semiring $R), Σ _ : Q(Module $R $M),
      Σ e : Q(List ($R × $M)), Q($x = smulAndSum $e)) := do
  match x with
  | ~q($x₁ + $x₂) =>
    let ⟨R₁, i₁, i₁', l₁, pf₁⟩ ← parse M i x₁
    let ⟨R₂, i₂, i₂', l₂, pf₂⟩ ← parse M i x₂
    match ← isDefEqQ R₁ R₂ with
    | .defEq (_ : $R₁ =Q $R₂) =>
      let l₂' : Q(List ($R₁ × $M)) := l₂
      let pf₂' : Q($x₂ = smulAndSum $l₂') := pf₂
      pure ⟨R₁, i₁, i₁', q($l₁ ++ $l₂), q(concat_pf $pf₁ $pf₂')⟩
    | _ =>
    try
      let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
      let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
      assumeInstancesCommute
      let l₁' : Q(List ($R₂ × $M)) := q(considerFstAs $R₂ $l₁)
      let pf₁' : Q($x₁ = smulAndSum (considerFstAs $R₂ $l₁)) := q(considerFstAs_pf $R₂ $pf₁)
      pure ⟨R₂, i₂, i₂', q($l₁' ++ $l₂), q(concat_pf $pf₁' $pf₂)⟩
    catch _ =>
      let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
      let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
      assumeInstancesCommute
      let l₂' : Q(List ($R₁ × $M)) := q(considerFstAs $R₁ $l₂)
      let pf₂' : Q($x₂ = smulAndSum (considerFstAs $R₁ $l₂)) := q(considerFstAs_pf $R₁ $pf₂)
      pure ⟨R₁, i₁, i₁', q($l₁ ++ $l₂'), q(concat_pf $pf₁ $pf₂')⟩
  | ~q(@HSMul.hSMul _ _ _ (@instHSMul $S _ $iS) $s $y) =>
    let ⟨R, iR, iR', l, pf⟩ ← parse M i y
    let i₁ ← synthInstanceQ q(Semiring $S)
    let i₂ ← synthInstanceQ q(Module $S $M)
    assumeInstancesCommute
    try
      let _i₃ ← synthInstanceQ q(SMul $S $R)
      let _i₄ ← synthInstanceQ q(IsScalarTower $S $R $M)
      let l' : Q(List ($R × $M)) := q(smulRightFst $l $s)
      let pf' : Q($s • $y = smulAndSum $l') := q(smulRightFst_pf $pf $s)
      pure ⟨R, iR, iR', l', pf'⟩
    catch _ =>
      let _i₃ ← synthInstanceQ q(SMul $R $S)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R $S $M)
      let _i₅ ← synthInstanceQ q(SMulCommClass $S $R $M)
      let l' : Q(List ($S × $M)) := q(smulLeftFst $l $s)
      let pf' : Q($s • $y = smulAndSum $l') := q(smulLeftFst_pf $pf $s)
      pure ⟨S, i₁, i₂, l', pf'⟩
  | ~q(0) => pure ⟨q(Nat), q(Nat.instSemiring), q(AddCommGroup.toNatModule), q([]), q(zero_pf $M)⟩
  | _ => pure ⟨q(Nat), q(Nat.instSemiring), q(AddCommGroup.toNatModule), q([(1, $x)]), q(one_pf $x)⟩
