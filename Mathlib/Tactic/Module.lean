import Mathlib.Algebra.Algebra.Basic
import Mathlib.GroupTheory.GroupAction.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Util.AtomM

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic

abbrev smulAndSum {R : Type*} {M : Type*} [SMul R M] [Add M] [Zero M] (l : List (R × M)) : M :=
  (l.map (fun (⟨r, x⟩ : R × M) ↦ r • x)).sum

abbrev List.onFst {α β γ : Type*} (l : List (α × β)) (f : α → γ) : List (γ × β) :=
  l.map (fun p ↦ ⟨f p.1, p.2⟩)

abbrev considerFstAs {S M : Type*} (R : Type*) [CommSemiring S] [Semiring R] [Algebra S R] :
    (S × M) → (R × M) :=
  fun ⟨s, x⟩ ↦ (algebraMap S R s, x)

abbrev combine {α : Type*} (f : α → α → α) (fL : α → α) (fR : α → α) :
    List (α × ℕ) → List (α × ℕ) → List (α × ℕ)
  | [], l => l.onFst fR
  | l, [] => l.onFst fL
  | (a₁, k₁) :: t₁, (a₂, k₂) :: t₂ =>
    if k₁ < k₂ then
      (fL a₁, k₁) :: combine f fL fR t₁ ((a₂, k₂) :: t₂)
    else if k₁ = k₂ then
      (f a₁ a₂, k₁) :: combine f fL fR t₁ t₂
    else
      (fR a₂, k₂) :: combine f fL fR ((a₁, k₁) :: t₁) t₂

abbrev cob' {M : Type*} {R : Type} [Semiring R] (p₁ p₂ : R × M) : R × M :=
  let r₁ := Prod.fst p₁
  let r₂ := Prod.fst p₂
  let m₁ := Prod.snd p₁
  (r₁ + r₂, m₁)

abbrev cob {v : Level} {M : Q(Type v)} {R : Q(Type)} (_i₂ : Q(Semiring $R)) (p₁ p₂ : Q($R × $M)) :
    Q($R × $M) :=
  q(cob' $p₁ $p₂)

abbrev boc' {M : Type*} {R : Type} [Ring R] (p₁ p₂ : R × M) : R × M :=
  let r₁ := Prod.fst p₁
  let r₂ := Prod.fst p₂
  let m₁ := Prod.snd p₁
  (r₁ - r₂, m₁)

abbrev boc {v : Level} {M : Q(Type v)} {R : Q(Type)} (_i₂ : Q(Ring $R))
    (p₁ p₂ : Q($R × $M)) :
    Q($R × $M) :=
  q(boc' $p₁ $p₂)

abbrev bco' {M : Type*} {R : Type} [Ring R] (p : R × M) : R × M :=
  let r := Prod.fst p
  let m := Prod.snd p
  (- r, m)

abbrev bco {v : Level} {M : Q(Type v)} {R : Q(Type)} (_i₂ : Q(Ring $R))
    (p : Q($R × $M)) :
    Q($R × $M) :=
  q(bco' $p)

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

def matchRings {v : Level} (M : Q(Type v)) (iM : Q(AddCommMonoid $M)) (x₁ x₂ : Q($M))
    {R₁ : Q(Type)} {iR₁ : Q(Semiring $R₁)} (iMR₁ : Q(@Module $R₁ $M $iR₁ $iM))
    (l₁ : List (Q($R₁ × $M) × ℕ)) (pf₁ : Q($x₁ = smulAndSum $(foo (l₁.map Prod.fst))))
    {R₂ : Q(Type)} {iR₂ : Q(Semiring $R₂)} (iMR₂ : Q(@Module $R₂ $M $iR₂ $iM))
    (l₂ : List (Q($R₂ × $M) × ℕ)) (pf₂ : Q($x₂ = smulAndSum $(foo (l₂.map Prod.fst)))) :
    MetaM <| Σ R : Q(Type), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ l₁ l₂ : List (Q($R × $M) × ℕ),
      Q($x₁ = smulAndSum $(foo (l₁.map Prod.fst)))
        × Q($x₂ = smulAndSum $(foo (l₂.map Prod.fst))) := do
  match ← isDefEqQ R₁ R₂ with
  | .defEq (_ : $R₁ =Q $R₂) => pure ⟨R₁, iR₁, iMR₁, l₁, l₂, pf₁, pf₂⟩
  | _ =>
  try
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
    assumeInstancesCommute
    let l₁' : List (Q($R₂ × $M) × ℕ) := l₁.onFst (fun p ↦ q(considerFstAs $R₂ $p))
    pure ⟨R₂, iR₂, iMR₂, l₁', l₂, q(sorry), pf₂⟩
  catch _ =>
    let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
    assumeInstancesCommute
    let l₂' : List (Q($R₁ × $M) × ℕ) := l₂.onFst (fun p ↦ q(considerFstAs $R₁ $p))
    pure ⟨R₁, iR₁, iMR₁, l₁, l₂', pf₁, q(sorry)⟩

def liftRing {v : Level} (M : Q(Type v)) (iM : Q(AddCommMonoid $M)) (x₁ : Q($M))
    {R₁ : Q(Type)} {iR₁ : Q(Semiring $R₁)} (iMR₁ : Q(@Module $R₁ $M $iR₁ $iM))
    (l₁ : List (Q($R₁ × $M) × ℕ)) (pf₁ : Q($x₁ = smulAndSum $(foo (l₁.map Prod.fst))))
    (R₂ : Q(Type)) (iR₂ : Q(Semiring $R₂)) (iMR₂ : Q(@Module $R₂ $M $iR₂ $iM)) :
    MetaM <| Σ R : Q(Type), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ l₁ : List (Q($R × $M) × ℕ), Q($x₁ = smulAndSum $(foo (l₁.map Prod.fst))) := do
  try
    let _i₁ : Q(CommSemiring $R₂) ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
    pure ⟨R₁, iR₁, iMR₁, l₁, pf₁⟩
  catch _ =>
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
    assumeInstancesCommute
    let l₁' : List (Q($R₂ × $M) × ℕ) := l₁.onFst (fun p ↦ q(considerFstAs $R₂ $p))
    pure ⟨R₂, iR₂, iMR₂, l₁', q(sorry)⟩

partial def parse {v : Level} (M : Q(Type v)) (iM : Q(AddCommMonoid $M)) (x : Q($M)) :
    AtomM (Σ R : Q(Type), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ e : List (Q($R × $M) × ℕ), Q($x = smulAndSum $(foo (e.map Prod.fst)))) := do
  match x with
  | ~q($x₁ + $x₂) =>
    let ⟨R₁, iR₁, iMR₁, l₁, pf₁⟩ ← parse M iM x₁
    let ⟨R₂, iR₂, iMR₂, l₂, pf₂⟩ ← parse M iM x₂
    let ⟨R, iR, iMR, l₁', l₂', pf₁', pf₂'⟩ ← matchRings M iM x₁ x₂ iMR₁ l₁ pf₁ iMR₂ l₂ pf₂
    pure ⟨R, iR, iMR, combine (cob iR) id id l₁' l₂', q(sorry)⟩
  | ~q(@HSub.hSub _ _ _ (@instHSub _ $iM') $x₁ $x₂) =>
    let ⟨R₁, iR₁, iMR₁, l₁, pf₁⟩ ← parse M iM x₁
    let ⟨R₂, iR₂, iMR₂, l₂, pf₂⟩ ← parse M iM x₂
    let iZ ← synthInstanceQ q(Semiring ℤ)
    let iMZ ← synthInstanceQ q(Module ℤ $M)
    let ⟨R₁', iR₁', iMR₁', l₁', pf₁'⟩ ← liftRing M iM x₁ iMR₁ l₁ pf₁ q(ℤ) iZ iMZ
    let ⟨R₂', iR₂', iMR₂', l₂', pf₂'⟩ ← liftRing M iM x₂ iMR₂ l₂ pf₂ q(ℤ) iZ iMZ
    let ⟨R, iR, iMR, l₁'', l₂'', pf₁'', pf₂''⟩ ← matchRings M iM x₁ x₂ iMR₁' l₁' pf₁' iMR₂' l₂' pf₂'
    let iR' ← synthInstanceQ q(Ring $R)
    pure ⟨R, iR, iMR, combine (boc iR') id (bco iR') l₁'' l₂'', q(sorry)⟩
  | ~q(@Neg.neg _ $iM' $x) =>
    let ⟨R, iR, iMR, l, pf⟩ ← parse M iM x
    let iZ ← synthInstanceQ q(Semiring ℤ)
    let iMZ ← synthInstanceQ q(Module ℤ $M)
    let ⟨R', iR', iMR', l', pf'⟩ ← liftRing M iM x iMR l pf q(ℤ) iZ iMZ
    let iR'' ← synthInstanceQ q(Ring $R')
    let negL := l'.onFst fun (p : Q($R' × $M)) ↦ q((- Prod.fst $p, Prod.snd $p))
    pure ⟨R', iR', iMR', negL, q(sorry)⟩
  | ~q(@HSMul.hSMul _ _ _ (@instHSMul $S _ $iS) $s $y) =>
    let ⟨R, iR, iR', l, pf⟩ ← parse M iM y
    let i₁ ← synthInstanceQ q(Semiring $S)
    let i₂ ← synthInstanceQ q(Module $S $M)
    assumeInstancesCommute
    try
      let _i₃ ← synthInstanceQ q(SMul $S $R)
      let _i₄ ← synthInstanceQ q(IsScalarTower $S $R $M)
      let l' : List (Q($R × $M) × ℕ) := l.onFst (fun p ↦ q(smulRightFst $s $p))
      pure ⟨R, iR, iR', l', q(sorry)⟩
    catch _ =>
      let _i₃ ← synthInstanceQ q(SMul $R $S)
      let _i₄ ← synthInstanceQ q(IsScalarTower $R $S $M)
      let _i₅ ← synthInstanceQ q(SMulCommClass $S $R $M)
      let l' : List (Q($S × $M) × ℕ) := l.onFst (fun p ↦ q(smulLeftFst $s $p))
      pure ⟨S, i₁, i₂, l', q(sorry)⟩
  | ~q(0) => pure ⟨q(Nat), q(Nat.instSemiring), q(AddCommGroup.toNatModule), [], q(zero_pf $M)⟩
  | _ =>
    let k : ℕ ← AtomM.addAtom x
    pure ⟨q(Nat), q(Nat.instSemiring), q(AddCommGroup.toNatModule), [(q((1, $x)), k)], q(one_pf $x)⟩

theorem eq_cons_cons {R : Type*} {M : Type*} [AddMonoid M] [Zero R] [SMul R M] {r₁ r₂ : R} (m : M)
    {l₁ l₂ : List (R × M)} (h1 : r₁ = r₂) (h2 : smulAndSum l₁ = smulAndSum l₂) :
      smulAndSum ((r₁, m) :: l₁) = smulAndSum ((r₂, m) :: l₂) := by
  sorry

theorem eq_cons_const {R : Type*} {M : Type*} [AddMonoid M] [Zero R] [SMul R M] {r : R} (m : M)
    {n : M} {l : List (R × M)} (h1 : r = 0) (h2 : smulAndSum l = n) :
    smulAndSum ((r, m) :: l) = n := by
  sorry

theorem eq_const_cons {R : Type*} {M : Type*} [AddMonoid M] [Zero R] [SMul R M] {r : R} (m : M)
    {n : M} {l : List (R × M)} (h1 : 0 = r) (h2 : n = smulAndSum l) :
    n = smulAndSum ((r, m) :: l) := by
  sorry

partial def reduceCoefficientwise {v : Level} {R : Q(Type)} {M : Q(Type v)}
    (iM : Q(AddCommMonoid $M)) (iR : Q(Semiring $R)) (iRM : Q(Module $R $M))
    (l₁ l₂ : List (Q($R × $M) × ℕ)) (g : MVarId) :
    MetaM (List MVarId) := do
  trace[debug] "creating goals to compare {l₁} and {l₂}"
  let _i ← synthInstanceQ q(Zero $R)
  let ll₁ : Q(List ($R × $M)) := foo (List.map Prod.fst l₁)
  let ll₂ : Q(List ($R × $M)) := foo (List.map Prod.fst l₂)
  trace[debug] "current goal is {← g.getType}"
  let t : Q(Prop) := q(smulAndSum $ll₁ = smulAndSum $ll₂)
  trace[debug] "checking that this is the same as {t} ..."
  trace[debug] "we'll be inspecting {← isDefEq (← g.getType).consumeMData t}"
  guard (← isDefEq (← g.getType).consumeMData t)
  trace[debug] "... ok"
  match l₁, l₂ with
  | [], [] =>
    trace[debug] "we've reached the bottom; goal is {g}"
    let pf : Q(smulAndSum $ll₁ = smulAndSum $ll₁) := q(rfl)
    g.assign pf
    trace[debug] "successfully resolved bottom goal with rfl"
    pure []
  | [], (e, _) :: l =>
    let mvar₁ : Q((0:$R) = Prod.fst $e) ← mkFreshExprMVar q((0:$R) = Prod.fst $e)
    let ll : Q(List ($R × $M)) := foo (List.map Prod.fst l)
    let mvar₂ : Q((0:$M) = smulAndSum $ll) ← mkFreshExprMVar q((0:$M) = smulAndSum $ll)
    let mvars ← reduceCoefficientwise iM iR iRM [] l mvar₂.mvarId!
    g.assign q(eq_const_cons (Prod.snd $e) $mvar₁ $mvar₂)
    pure (mvar₁.mvarId! :: mvars)
  | (e, _) :: l, [] =>
    let mvar₁ : Q(Prod.fst $e = (0:$R)) ← mkFreshExprMVar q(Prod.fst $e = (0:$R))
    let ll : Q(List ($R × $M)) := foo (List.map Prod.fst l)
    let mvar₂ : Q(smulAndSum $ll = (0:$M)) ← mkFreshExprMVar q(smulAndSum $ll = (0:$M))
    let mvars ← reduceCoefficientwise iM iR iRM l [] mvar₂.mvarId!
    g.assign q(eq_cons_const (Prod.snd $e) $mvar₁ $mvar₂)
    pure (mvar₁.mvarId! :: mvars)
  | L₁@((e₁, k₁) :: l₁), L₂@((e₂, k₂) :: l₂) =>
    let ll₁ : Q(List ($R × $M)) := foo (l₁.map Prod.fst)
    let ll₂ : Q(List ($R × $M)) := foo (l₂.map Prod.fst)
    let LL₁ : Q(List ($R × $M)) := foo (L₁.map Prod.fst)
    let LL₂ : Q(List ($R × $M)) := foo (L₂.map Prod.fst)
    if k₁ < k₂ then
      let mvar₁ : Q(Prod.fst $e₁ = (0:$R)) ← mkFreshExprMVar q(Prod.fst $e₁ = (0:$R))
      let mvar₂ : Q(smulAndSum $ll₁ = smulAndSum $LL₂)
        ← mkFreshExprMVar q(smulAndSum $ll₁ = smulAndSum $LL₂)
      let mvars ← reduceCoefficientwise iM iR iRM l₁ L₂ mvar₂.mvarId!
      g.assign q(eq_cons_const (Prod.snd $e₁) $mvar₁ $mvar₂)
      pure (mvar₁.mvarId! :: mvars)
    else if k₁ = k₂ then
      let mvar₁ : Q(Prod.fst $e₁ = Prod.fst $e₂) ← mkFreshExprMVar q(Prod.fst $e₁ = Prod.fst $e₂)
      let mvar₂ : Q(smulAndSum $ll₁ = smulAndSum $ll₂)
        ← mkFreshExprMVar q(smulAndSum $ll₁ = smulAndSum $ll₂)
      let mvars ← reduceCoefficientwise iM iR iRM l₁ l₂ mvar₂.mvarId!
      g.assign q(eq_cons_cons (Prod.snd $e₁) $mvar₁ $mvar₂)
      pure (mvar₁.mvarId! :: mvars)
    else
      let mvar₁ : Q((0:$R) = Prod.fst $e₂) ← mkFreshExprMVar q((0:$R) = Prod.fst $e₂)
      let mvar₂ : Q(smulAndSum $LL₁ = smulAndSum $ll₂)
        ← mkFreshExprMVar q(smulAndSum $LL₁ = smulAndSum $ll₂)
      let mvars ← reduceCoefficientwise iM iRM iR L₁ l₂ mvar₂.mvarId!
      g.assign q(eq_const_cons (Prod.snd $e₂) $mvar₁ $mvar₂)
      pure (mvar₁.mvarId! :: mvars)

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
  have _iR₁ : Q(Semiring.{0} $R₁) := e₁.snd.fst
  let iMR₁ ← synthInstanceQ q(Module $R₁ $M)
  -- would be better to do the following, but doesn't work?
  -- have iMR₁ : Q(@Module.{0, v} $R₁ $M $iR₁ $iM) := e.snd.snd.fst
  assumeInstancesCommute
  have l₁ : List (Q($R₁ × $M) × ℕ) := e₁.snd.snd.snd.fst
  let ll₁ : Q(List ($R₁ × $M)) := foo (List.map Prod.fst l₁)
  let pf₁ : Q($lhs = smulAndSum $ll₁) := e₁.snd.snd.snd.snd
  trace[debug] "unpacked the LHS parse successfully"
  -- for now let's assume that LHS and RHS scalars have the same type
  trace[debug] "parsing RHS, {rhs}"
  let e₂ ← parse M iM rhs
  have R₂ : Q(Type) := e₂.fst
  have _iR₂ : Q(Semiring.{0} $R₂) := e₂.snd.fst
  let iMR₂ ← synthInstanceQ q(Module $R₂ $M)
  have l₂ : List (Q($R₁ × $M) × ℕ) := e₂.snd.snd.snd.fst
  let ll₂ : Q(List ($R₁ × $M)) := foo (List.map Prod.fst l₂)
  let pf₂ : Q($rhs = smulAndSum $ll₂) := e₂.snd.snd.snd.snd
  trace[debug] "unpacked the RHS parse successfully"
  -- lift LHS and RHS to same scalar ring
  let ⟨R, iR, iMR, l₁', l₂', pf₁', pf₂'⟩ ← matchRings M iM lhs rhs iMR₁ l₁ pf₁ iMR₂ l₂ pf₂
  -- start to rig up the collection of goals we will reduce to
  let ll₁' : Q(List ($R × $M)) := foo (List.map Prod.fst l₁')
  let ll₂' : Q(List ($R × $M)) := foo (List.map Prod.fst l₂')
  let mvar : Q(smulAndSum $ll₁' = smulAndSum $ll₂')
    ← mkFreshExprMVar q(smulAndSum $ll₁' = smulAndSum $ll₂')
  g.assign q(Eq.trans (Eq.trans $pf₁' $mvar) (Eq.symm $pf₂'))
  reduceCoefficientwise iM iR iMR l₁' l₂' mvar.mvarId!

def matchCoeffs (g : MVarId) : MetaM (List MVarId) := AtomM.run .default (matchCoeffsAux g)

elab "match_coeffs" : tactic => Tactic.liftMetaTactic matchCoeffs

elab "module" : tactic => do
  Tactic.liftMetaTactic matchCoeffs
  Tactic.allGoals <|
    Tactic.evalTactic <|
      ← `(tactic |
      (push_cast [eq_natCast, eq_intCast, eq_ratCast, smul_eq_mul, neg_smul, one_smul]; try ring1))
