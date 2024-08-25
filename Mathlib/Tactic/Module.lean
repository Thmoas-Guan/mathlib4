import Qq
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.GroupTheory.GroupAction.BigOperators

open Lean Qq

abbrev smulAndSum {R : Type*} {M : Type*} [SMul R M] [Add M] [Zero M] (l : List (R × M)) : M :=
  (l.map (fun (⟨r, x⟩ : R × M) ↦ r • x)).sum

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
      let _i₂ ← synthInstanceQ q(DistribSMul $S $M)
      assumeInstancesCommute
      let _i₃ ← synthInstanceQ q(SMul $S $R)
      let _i₄ ← synthInstanceQ q(IsScalarTower $S $R $M)
      let l' : Q(List ($R × $M)) := q(smulRightFst $l $s)
      let pf' : Q($s • $y = smulAndSum $l') := q(smulRightFst_pf $pf $s)
      pure ⟨R, iR, l', pf'⟩
    catch _ =>
      let _i₂ ← synthInstanceQ q(DistribSMul $S $M)
      assumeInstancesCommute
      let _i₃ ← synthInstanceQ q(SMul $R $S)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R $S $M)
      let _i₅ ← synthInstanceQ q(SMulCommClass $S $R $M)
      let l' : Q(List ($S × $M)) := q(smulLeftFst $l $s)
      let pf' : Q($s • $y = smulAndSum $l') := q(smulLeftFst_pf $pf $s)
      pure ⟨S, iS, l', pf'⟩
  | ~q(0) => pure ⟨q(Nat), q(AddMonoid.toNatSMul), q([]), q(zero_pf $M)⟩
  | _ => pure ⟨q(Nat), q(AddMonoid.toNatSMul), q([(1, $x)]), q(one_pf $x)⟩
