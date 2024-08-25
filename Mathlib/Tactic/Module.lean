import Qq
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Group.List

open Lean Qq

abbrev ModuleExpr {u v : Level} (R : Q(Type u)) (M : Q(Type v)) : Type := Q(List ($R × $M))

abbrev ModuleExpr.sum {u v : Level} {R : Q(Type u)} {M : Q(Type v)} {_ : Q(SMul $R $M)}
    {_ : Q(Add $M)} {_ : Q(Zero $M)} (e : ModuleExpr R M) : Q($M) :=
  q(List.sum (List.map (fun (⟨r, x⟩ : $R × $M) ↦ r • x) $e))

partial def parse {v : Level} (M : Q(Type v)) (i : Q(Add $M)) (x : Q($M)) :
    MetaM (Σ R : Q(Type), ModuleExpr R M) := do
  match x with
  | ~q($x₁ + $x₂) =>
    let ⟨R₁, l₁⟩ ← parse M i x₁
    let ⟨R₂, l₂⟩ ← parse M i x₂
    try
      let _i₁ ← synthInstanceQ q(Coe $R₁ $R₂)
      let l₁' : Q(List ($R₂ × $M)) := q(List.map (fun (⟨r, x⟩ : $R₁ × $M) ↦ ((r : $R₂), x)) $l₁)
      pure ⟨R₂, q($l₁' ++ $l₂)⟩
    catch _ =>
      let _i₁ ← synthInstanceQ q(Coe $R₂ $R₁)
      let l₂' : Q(List ($R₁ × $M)) := q(List.map (fun (⟨r, x⟩ : $R₂ × $M) ↦ ((r : $R₁), x)) $l₂)
      pure ⟨R₁, q($l₁ ++ $l₂')⟩
  | ~q(@HSMul.hSMul $S _ _ (_) $s $x) =>
    have x : Q($M) := x
    let ⟨R, l⟩ ← parse M i x
    let _i₁ ← synthInstanceQ q(SMul $R $M)
    let _i₂ ← synthInstanceQ q(SMul $S $M)
    try
      let _i₃ ← synthInstanceQ q(SMul $S $R)
      let _i₄ ← synthInstanceQ q(IsScalarTower $S $R $M)
      let l' : Q(List ($R × $M)) := q(List.map (fun (⟨r, x⟩ : $R × $M) ↦ ($s • r, x)) $l)
      pure ⟨R, l'⟩
    catch _ =>
      let _i₃ ← synthInstanceQ q(SMul $R $S)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R $S $M)
      let _i₅ ← synthInstanceQ q(SMulCommClass $R $S $M)
      let l' : Q(List ($S × $M)) := q(List.map (fun (⟨r, x⟩ : $R × $M) ↦ (r • $s, x)) $l)
      pure ⟨S, l'⟩
  | e => pure ⟨q(Nat), q([(1, $e)])⟩
