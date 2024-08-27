/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.GroupTheory.GroupAction.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Util.AtomM

/-! # A tactic for normalization over modules
-/

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

def matchRings' {v : Level} (M : Q(Type v)) (iM : Q(AddCommMonoid $M)) (x : Q($M))
    {R₁ : Q(Type)} {iR₁ : Q(Semiring $R₁)} (iMR₁ : Q(@Module $R₁ $M $iR₁ $iM))
    (l : List (Q($R₁ × $M) × ℕ)) (pf : Q($x = smulAndSum $(foo (l.map Prod.fst))))
    {R₂ : Q(Type)} (iR₂ : Q(Semiring $R₂)) (iMR₂ : Q(@Module $R₂ $M $iR₂ $iM)) (r₂ : Q($R₂)) :
    MetaM <| Σ R : Q(Type), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ l : List (Q($R × $M) × ℕ),
      Q($x = smulAndSum $(foo (l.map Prod.fst)))
        × Σ r : Q($R), Q($r₂ • $x = $r • $x) := do
  match ← isDefEqQ R₁ R₂ with
  | .defEq (_ : $R₁ =Q $R₂) => pure ⟨R₁, iR₁, iMR₁, l, pf, r₂, q(sorry)⟩
  | _ =>
  try
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
    assumeInstancesCommute
    let l' : List (Q($R₂ × $M) × ℕ) := l.onFst (fun p ↦ q(considerFstAs $R₂ $p))
    let pf' : Q($r₂ • $x = $r₂ • $x) := q(rfl)
    pure ⟨R₂, iR₂, iMR₂, l', q(sorry), r₂, pf'⟩
  catch _ =>
    let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
    assumeInstancesCommute
    let r : Q($R₁) := q(algebraMap $R₂ $R₁ $r₂)
    let pf' : Q($r₂ • $x = $r • $x) := q(sorry)
    pure ⟨R₁, iR₁, iMR₁, l, pf, r, pf'⟩

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

theorem fasdasdfdf {M : Type*} [AddCommGroup M] {R : Type*} [Ring R] [Module R M]
    {l : List (R × M)} {x : M} (h : x = smulAndSum l) :
    - x = smulAndSum (l.onFst Neg.neg) := by
  unfold smulAndSum at h ⊢
  simp only [List.map_map, h, List.sum_neg]
  congr
  ext p
  simp

theorem fasddf {M : Type*} [AddCommMonoid M] {R : Type*} [Semiring R] [Module R M]
    {l : List (R × M)} {x : M} (h : x = smulAndSum l) (r : R) :
    r • x = smulAndSum (l.onFst (r * ·)) :=
  sorry

def asdfa {v : Level} {M : Q(Type v)} (iM : Q(AddCommMonoid $M)) {R : Q(Type)} (iR : Q(Semiring $R))
    (iMR : Q(@Module $R $M $iR $iM)) (f : Q($R × $M → $R × $M)) :
    ∀ (l : List (Q($R × $M) × ℕ)),
      MetaM Q(List.map $f $(foo (l.map Prod.fst))
        = $(foo ((l.map (fun ⟨p, k⟩ ↦ (q($f $p), k))).map Prod.fst)))
  | [] => pure q(rfl)
  | _ :: l => do pure q(congrArg _ $(← asdfa iM iR iMR f l))

/-- The main algorithm behind the `match_scalars` and `module` tactics: partially-normalizing an
expression in an additive commutative monoid `M` into the form c1 • x1 + c2 • x2 + ... c_k • x_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are scalars. The scalar type of the
expression is not pre-determined: instead it starts as `ℕ` (when each atom is initially given a
scalar `(1:ℕ)`) and gets bumped up into bigger semirings when such semirings are encountered.

It is assumed that there is a "linear order" on all the semirings which appear in the expression:
for any two semirings `R` and `S` which occur, we have either `Algebra R S` or `Algebra S R`). -/
partial def parse {v : Level} (M : Q(Type v)) (iM : Q(AddCommMonoid $M)) (x : Q($M)) :
    AtomM (Σ R : Q(Type), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ e : List (Q($R × $M) × ℕ), Q($x = smulAndSum $(foo (e.map Prod.fst)))) := do
  match x with
  -- parse an addition: `x₁ + x₁`
  | ~q($x₁ + $x₂) =>
    let ⟨R₁, iR₁, iMR₁, l₁, pf₁⟩ ← parse M iM x₁
    let ⟨R₂, iR₂, iMR₂, l₂, pf₂⟩ ← parse M iM x₂
    let ⟨R, iR, iMR, l₁', l₂', pf₁', pf₂'⟩ ← matchRings M iM x₁ x₂ iMR₁ l₁ pf₁ iMR₂ l₂ pf₂
    pure ⟨R, iR, iMR, combine (cob iR) id id l₁' l₂', q(sorry)⟩
  -- parse a subtraction: `x₁ - x₂`
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
  -- parse a negation: `-y`
  | ~q(@Neg.neg _ $iM' $y) =>
    let ⟨_, _, iMR₀, l₀, pf₀⟩ ← parse M iM y
    let iZ ← synthInstanceQ q(Semiring ℤ)
    let _i ← synthInstanceQ q(AddCommGroup $M)
    let iMZ ← synthInstanceQ q(Module ℤ $M)
    -- lift from original semiring of scalars (say `R₀`) to `R₀ ⊗ ℤ`
    let ⟨R, iR, iMR, l, pf⟩ ← liftRing M iM y iMR₀ l₀ pf₀ q(ℤ) iZ iMZ
    let _i' ← synthInstanceQ q(Ring $R)
    assumeInstancesCommute
    let qneg : Q($R × $M) → Q($R × $M) := fun (p : Q($R × $M)) ↦ q((- Prod.fst $p, Prod.snd $p))
    have pf_right :
        Q(List.onFst $(foo (l.map Prod.fst)) Neg.neg = $(foo ((l.onFst qneg).map Prod.fst))) :=
      ← asdfa iM iR iMR q(fun p ↦ (- p.1, p.2)) l
    have pf_left : Q(-$y = smulAndSum (R := $R) (List.onFst $(foo (l.map Prod.fst)) Neg.neg)) :=
      q(fasdasdfdf $pf)
    pure ⟨R, iR, iMR, l.onFst qneg, q(Eq.trans $pf_left (congrArg smulAndSum $pf_right))⟩
  -- parse a scalar multiplication: `(s₀ : S) • y`
  | ~q(@HSMul.hSMul _ _ _ (@instHSMul $S _ $iS) $s₀ $y) =>
    let ⟨_, _, iMR₀, l₀, pf₀⟩ ← parse M iM y
    let i₁ ← synthInstanceQ q(Semiring $S)
    let i₂ ← synthInstanceQ q(Module $S $M)
    assumeInstancesCommute
    -- lift from original semiring of scalars (say `R₀`) to `R₀ ⊗ S`
    let ⟨R, iR, iMR, l, (pf₂ : Q($y = smulAndSum $(foo (List.map Prod.fst l)))), s,
      (pf₁ : Q($s₀ • $y = $s • $y))⟩ ← matchRings' M iM y iMR₀ l₀ pf₀ i₁ i₂ s₀
    let sl : List (Q($R × $M) × ℕ) := l.onFst (fun p ↦ q(($s * Prod.fst $p, Prod.snd $p)))
    let pf₃ : Q((List.onFst $(foo (List.map Prod.fst l)) ($s * ·)) = $(foo (sl.map Prod.fst)))
      ← asdfa iM iR iMR q(fun p ↦ ($s * p.1, p.2)) l
    pure ⟨R, iR, iMR, sl, q(Eq.trans (Eq.trans $pf₁ (fasddf $pf₂ $s)) (congrArg _ $pf₃))⟩
  -- parse a `(0:M)`
  | ~q(0) => pure ⟨q(Nat), q(Nat.instSemiring), q(AddCommGroup.toNatModule), [], q(zero_pf $M)⟩
  -- anything else should be treated as an atom
  | _ =>
    let k : ℕ ← AtomM.addAtom x
    pure ⟨q(Nat), q(Nat.instSemiring), q(AddCommGroup.toNatModule), [(q((1, $x)), k)], q(one_pf $x)⟩

theorem eq_cons_cons {R : Type*} {M : Type*} [AddMonoid M] [Zero R] [SMul R M] {r₁ r₂ : R} (m : M)
    {l₁ l₂ : List (R × M)} (h1 : r₁ = r₂) (h2 : smulAndSum l₁ = smulAndSum l₂) :
      smulAndSum ((r₁, m) :: l₁) = smulAndSum ((r₂, m) :: l₂) := by
  simp only [smulAndSum] at *
  simp [h1, h2]

theorem eq_cons_const {R : Type*} {M : Type*} [AddCommMonoid M] [Semiring R] [Module R M] {r : R}
    (m : M) {n : M} {l : List (R × M)} (h1 : r = 0) (h2 : smulAndSum l = n) :
    smulAndSum ((r, m) :: l) = n := by
  simp only [smulAndSum] at *
  simp [h1, h2]

theorem eq_const_cons {R : Type*} {M : Type*} [AddCommMonoid M] [Semiring R] [Module R M] {r : R}
    (m : M) {n : M} {l : List (R × M)} (h1 : 0 = r) (h2 : n = smulAndSum l) :
    n = smulAndSum ((r, m) :: l) := by
  simp only [smulAndSum] at *
  simp [← h1, h2]

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
  assumeInstancesCommute
  match l₁, l₂ with
  | [], [] =>
    trace[debug] "we've reached the bottom; goal is {g}"
    let pf : Q(smulAndSum $ll₁ = smulAndSum $ll₁) := q(rfl)
    g.assign pf
    trace[debug] "successfully resolved bottom goal with rfl"
    pure []
  | [], (e, _) :: L =>
    let mvar₁ : Q((0:$R) = Prod.fst $e) ← mkFreshExprMVar q((0:$R) = Prod.fst $e)
    let LL : Q(List ($R × $M)) := foo (List.map Prod.fst L)
    let mvar₂ : Q((0:$M) = smulAndSum $LL) ← mkFreshExprMVar q((0:$M) = smulAndSum $LL)
    let mvars ← reduceCoefficientwise iM iR iRM [] L mvar₂.mvarId!
    g.assign q(eq_const_cons (Prod.snd $e) $mvar₁ $mvar₂)
    pure (mvar₁.mvarId! :: mvars)
  | (e, _) :: L, [] =>
    let mvar₁ : Q(Prod.fst $e = (0:$R)) ← mkFreshExprMVar q(Prod.fst $e = (0:$R))
    let LL : Q(List ($R × $M)) := foo (List.map Prod.fst L)
    let mvar₂ : Q(smulAndSum $LL = (0:$M)) ← mkFreshExprMVar q(smulAndSum $LL = (0:$M))
    let mvars ← reduceCoefficientwise iM iR iRM L [] mvar₂.mvarId!
    g.assign q(eq_cons_const (Prod.snd $e) $mvar₁ $mvar₂)
    pure (mvar₁.mvarId! :: mvars)
  | (e₁, k₁) :: L₁, (e₂, k₂) :: L₂ =>
    let LL₁ : Q(List ($R × $M)) := foo (L₁.map Prod.fst)
    let LL₂ : Q(List ($R × $M)) := foo (L₂.map Prod.fst)
    if k₁ < k₂ then
      let mvar₁ : Q(Prod.fst $e₁ = (0:$R)) ← mkFreshExprMVar q(Prod.fst $e₁ = (0:$R))
      let mvar₂ : Q(smulAndSum $LL₁ = smulAndSum $ll₂)
        ← mkFreshExprMVar q(smulAndSum $LL₁ = smulAndSum $ll₂)
      let mvars ← reduceCoefficientwise iM iR iRM L₁ l₂ mvar₂.mvarId!
      g.assign q(eq_cons_const (Prod.snd $e₁) $mvar₁ $mvar₂)
      pure (mvar₁.mvarId! :: mvars)
    else if k₁ = k₂ then
      let mvar₁ : Q(Prod.fst $e₁ = Prod.fst $e₂) ← mkFreshExprMVar q(Prod.fst $e₁ = Prod.fst $e₂)
      let mvar₂ : Q(smulAndSum $LL₁ = smulAndSum $LL₂)
        ← mkFreshExprMVar q(smulAndSum $LL₁ = smulAndSum $LL₂)
      let mvars ← reduceCoefficientwise iM iR iRM L₁ L₂ mvar₂.mvarId!
      g.assign q(eq_cons_cons (Prod.snd $e₁) $mvar₁ $mvar₂)
      pure (mvar₁.mvarId! :: mvars)
    else
      let mvar₁ : Q((0:$R) = Prod.fst $e₂) ← mkFreshExprMVar q((0:$R) = Prod.fst $e₂)
      let mvar₂ : Q(smulAndSum $ll₁ = smulAndSum $LL₂)
        ← mkFreshExprMVar q(smulAndSum $ll₁ = smulAndSum $LL₂)
      let mvars ← reduceCoefficientwise iM iRM iR l₁ L₂ mvar₂.mvarId!
      g.assign q(eq_const_cons (Prod.snd $e₂) $mvar₁ $mvar₂)
      pure (mvar₁.mvarId! :: mvars)

def matchScalarsAux (g : MVarId) : AtomM (List MVarId) := do
  let eqData ← do
    match (← g.getType').eq? with
    | some e => pure e
    | none => throwError "goal {← g.getType} is not an equality"
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
  -- have iMR₁ : Q(@Module.{0, v} $R₁ $M $_iR₁ $iM) := e.snd.snd.fst
  assumeInstancesCommute
  have l₁ : List (Q($R₁ × $M) × ℕ) := e₁.snd.snd.snd.fst
  let ll₁ : Q(List ($R₁ × $M)) := foo (List.map Prod.fst l₁)
  let pf₁ : Q($lhs = smulAndSum $ll₁) := e₁.snd.snd.snd.snd
  trace[debug] "unpacked the LHS parse successfully"
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

def matchScalars (g : MVarId) : MetaM (List MVarId) := AtomM.run .default (matchScalarsAux g)

/- Do we also want to import `Mathlib.Data.Complex.Module`, so that the `ℝ`-to-`ℂ` algebra map can
be added to the list of algebra-maps which get special-cased here?  (The lemma would be
`Complex.coe_algebraMap`.)-/

elab "match_scalars" : tactic => Tactic.withMainContext <| Tactic.focus do
  Tactic.liftMetaTactic matchScalars
  Tactic.allGoals <|
    Tactic.evalTactic <| ← `(tactic | push_cast [eq_natCast, eq_intCast, eq_ratCast])

elab "module" : tactic => Tactic.withMainContext <| Tactic.focus do
  Tactic.liftMetaTactic matchScalars
  Tactic.allGoals <| do
    Tactic.evalTactic <|
      ← `(tactic | (push_cast [eq_natCast, eq_intCast, eq_ratCast]; try ring1))
  Tactic.done
