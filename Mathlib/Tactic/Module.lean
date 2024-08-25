import Qq
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Group.List

open Lean Qq

abbrev smulAndSum {R : Type*} {M : Type*} [SMul R M] [Add M] [Zero M] (l : List (R × M)) : M :=
  (l.map (fun (⟨r, x⟩ : R × M) ↦ r • x)).sum

partial def parse {v : Level} (M : Q(Type v)) (i : Q(AddMonoid $M)) (x : Q($M)) :
    MetaM (Σ R : Q(Type), Σ _ : Q(SMul $R $M), Σ e : Q(List ($R × $M)), Q(smulAndSum $e = $x)) := do
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
  | ~q(@HSMul.hSMul _ _ _ (@instHSMul $S _ $iS) $s $x) =>
    let ⟨R, iR, l, pf⟩ ← parse M i x
    try
      let _i₃ ← synthInstanceQ q(SMul $S $R)
      let _i₄ ← synthInstanceQ q(IsScalarTower $S $R $M)
      let l' : Q(List ($R × $M)) := q(List.map (fun (⟨r, x⟩ : $R × $M) ↦ ($s • r, x)) $l)
      pure ⟨R, iR, l', q(sorry)⟩
    catch _ =>
      let _i₃ ← synthInstanceQ q(SMul $R $S)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R $S $M)
      let _i₅ ← synthInstanceQ q(SMulCommClass $R $S $M)
      let l' : Q(List ($S × $M)) := q(List.map (fun (⟨r, x⟩ : $R × $M) ↦ (r • $s, x)) $l)
      pure ⟨S, iS, l', q(sorry)⟩
  | e => pure ⟨q(Nat), q(AddMonoid.toNatSMul), q([(1, $e)]), q(sorry)⟩
