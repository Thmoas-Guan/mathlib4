import Mathlib.Algebra.Algebra.Basic
import Mathlib.GroupTheory.GroupAction.BigOperators
import Mathlib.Util.AtomM

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic

abbrev smulAndSum {R : Type*} {M : Type*} [SMul R M] [Add M] [Zero M] (l : List (R × M)) : M :=
  (l.map (fun (⟨r, x⟩ : R × M) ↦ r • x)).sum

def List.onFst {α β γ : Type*} (l : List (α × β)) (f : α → γ) : List (γ × β) :=
  l.map (fun p ↦ ⟨f p.1, p.2⟩)

abbrev considerFstAs {S M : Type*} (R : Type*) [CommSemiring S] [Semiring R] [Algebra S R] :
    (S × M) → (R × M) :=
  fun ⟨s, x⟩ ↦ (algebraMap S R s, x)

def combine {α : Type*} (f : α → α → α) : List (α × ℕ) → List (α × ℕ) → List (α × ℕ)
  | [], l => l
  | l, [] => l
  | (a₁, k₁) :: t₁, (a₂, k₂) :: t₂ =>
    if k₁ < k₂ then
      (a₁, k₁) :: (a₂, k₂) :: combine f t₁ t₂
    else if k₁ = k₂ then
      (f a₁ a₂, k₁) :: combine f t₁ t₂
    else
      (a₂, k₂) :: (a₁, k₁) :: combine f t₁ t₂

def cob' {M : Type*} {R : Type} [Semiring R] (p₁ p₂ : R × M) : R × M :=
  let r₁ := Prod.fst p₁
  let r₂ := Prod.fst p₂
  let m₁ := Prod.snd p₁
  (r₁ + r₂, m₁)

def cob {v : Level} {M : Q(Type v)} {R : Q(Type)} (_i₂ : Q(Semiring $R)) (p₁ p₂ : Q($R × $M)) :
    Q($R × $M) :=
  q(cob' $p₁ $p₂)

abbrev smulRightFst {R S M : Type*} [SMul S R] [SMul S M] (s : S) : R × M → R × M :=
  fun ⟨r, x⟩ ↦ (s • r, x)

abbrev smulLeftFst {R S M : Type*} [SMul R S] [SMul S M] (s : S) : R × M → S × M :=
  fun ⟨r, x⟩ ↦ (r • s, x)

theorem one_pf {M : Type*} [AddMonoid M] (x : M) : x = smulAndSum [((1:ℕ), x)] := by
  simp [smulAndSum]

theorem zero_pf (M : Type*) [AddMonoid M] : (0:M) = smulAndSum (R := Nat) [] := by simp [smulAndSum]

def foo {v : Level} {α : Q(Type v)} : List (Q($α)) → Q(List $α)
  | [] => q([])
  | e :: t => q($e :: $(foo t))

partial def parse {v : Level} (M : Q(Type v)) (iM : Q(AddCommMonoid $M)) (x : Q($M)) :
    AtomM (Σ R : Q(Type), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ e : List (Q($R × $M) × ℕ), Q($x = smulAndSum $(foo (e.map Prod.fst)))) := do
  match x with
  | ~q($x₁ + $x₂) =>
    let ⟨R₁, i₁, i₁', l₁, pf₁⟩ ← parse M iM x₁
    let ⟨R₂, i₂, i₂', l₂, pf₂⟩ ← parse M iM x₂
    match ← isDefEqQ R₁ R₂ with
    | .defEq (_ : $R₁ =Q $R₂) =>
      let l₂' : List (Q($R₁ × $M) × ℕ) := l₂
      pure ⟨R₁, i₁, i₁', combine (cob i₁) l₁ l₂, q(sorry)⟩
    | _ =>
    try
      let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
      let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
      assumeInstancesCommute
      let l₁' : List (Q($R₂ × $M) × ℕ) := l₁.onFst (fun p ↦ q(considerFstAs $R₂ $p))
      pure ⟨R₂, i₂, i₂', combine (cob i₂) l₁' l₂, q(sorry)⟩
    catch _ =>
      let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
      let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
      assumeInstancesCommute
      let l₂' : List (Q($R₁ × $M) × ℕ) := l₂.onFst (fun p ↦ q(considerFstAs $R₁ $p))
      pure ⟨R₁, i₁, i₁', combine (cob i₁) l₁ l₂', q(sorry)⟩
  | ~q(@HSMul.hSMul _ _ _ (@instHSMul $S _ $iS) $s $y) =>
    trace[debug] "parsing scalar multiplication of {y} by {s}, scalar type is {S}"
    let ⟨R, iR, iR', l, pf⟩ ← parse M iM y
    let i₁ ← synthInstanceQ q(Semiring $S)
    let i₂ ← synthInstanceQ q(Module $S $M)
    trace[debug] "found semiring and module instances for {S}"
    assumeInstancesCommute
    try
      trace[debug] "trying first branch"
      let _i₃ ← synthInstanceQ q(SMul $S $R)
      let _i₄ ← synthInstanceQ q(IsScalarTower $S $R $M)
      trace[debug] "found that {S} is a valid scalar type for {R}"
      let l' : List (Q($R × $M) × ℕ) := l.onFst (fun p ↦ q(smulRightFst $s $p))
      trace[debug] "sending back the list {l'} now"
      pure ⟨R, iR, iR', l', q(sorry)⟩
    catch _ =>
      trace[debug] "trying second branch"
      let _i₃ ← synthInstanceQ q(SMul $R $S)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R $S $M)
      let _i₅ ← synthInstanceQ q(SMulCommClass $S $R $M)
      trace[debug] "found that {R} is a valid scalar type for {S}"
      let l' : List (Q($S × $M) × ℕ) := l.onFst (fun p ↦ q(smulLeftFst $s $p))
      trace[debug] "sending back the list {l'} now"
      pure ⟨S, i₁, i₂, l', q(sorry)⟩
  | ~q(0) => pure ⟨q(Nat), q(Nat.instSemiring), q(AddCommGroup.toNatModule), [], q(zero_pf $M)⟩
  | _ =>
    let k : ℕ ← AtomM.addAtom x
    pure ⟨q(Nat), q(Nat.instSemiring), q(AddCommGroup.toNatModule), [(q((1, $x)), k)], q(one_pf $x)⟩

def matchCoeffsAux (g : MVarId) : AtomM (List MVarId) := do
  let eqData := (← g.getType).consumeMData.eq?.get!
  let .sort u ← whnf (← inferType eqData.1) | unreachable!
  let some v := u.dec | throwError "goal cannot be an equality in Sort"
  let ((M : Q(Type v)), (lhs : Q($M)), (rhs :Q($M))) := eqData
  let iM ← synthInstanceQ q(AddCommMonoid.{v} $M)
  trace[debug] "parsing LHS, {lhs}"
  let e₁ ← parse M iM lhs
  have R₁ : Q(Type) := e₁.fst
  trace[debug] "got back some stuff over the semiring {R₁}"
  have iR₁ : Q(Semiring.{0} $R₁) := e₁.snd.fst
  let _i₁ ← synthInstanceQ q(SMul $R₁ $M) -- would be better to do the following, but doesn't work?
  -- have iMR₁ : Q(@Module.{0, v} $R₁ $M $iR₁ $iM) := e.snd.snd.fst
  assumeInstancesCommute
  have l₁ : List (Q($R₁ × $M) × ℕ) := e₁.snd.snd.snd.fst
  let ll₁ : Q(List ($R₁ × $M)) := foo (List.map Prod.fst l₁)
  let pf₁ : Q($lhs = smulAndSum $ll₁) := e₁.snd.snd.snd.snd
  trace[debug] "unpacked the LHS parse successfully"
  -- for now let's assume that LHS and RHS scalars have the same type
  trace[debug] "parsing RHS, {rhs}"
  let e₂ ← parse M iM rhs
  have l₂ : List (Q($R₁ × $M) × ℕ) := e₂.snd.snd.snd.fst
  let ll₂ : Q(List ($R₁ × $M)) := foo (List.map Prod.fst l₂)
  let pf₂ : Q($rhs = smulAndSum $ll₂) := e₂.snd.snd.snd.snd
  trace[debug] "unpacked the RHS parse successfully"
  -- start to rig up the collection of goals we will reduce to
  let mvar : Q(smulAndSum $ll₁ = smulAndSum $ll₂)
    ← mkFreshExprMVar q(smulAndSum $ll₁ = smulAndSum $ll₂)
  g.assign q(Eq.trans (Eq.trans $pf₁ $mvar) (Eq.symm $pf₂))
  pure [mvar.mvarId!]

def matchCoeffs (g : MVarId) : MetaM (List MVarId) := AtomM.run .default (matchCoeffsAux g)

elab "match_coeffs" : tactic => Tactic.liftMetaTactic matchCoeffs
