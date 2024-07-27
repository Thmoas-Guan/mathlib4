import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Defs
import Mathlib.adomaniLeanUtils.inspect_syntax
import Batteries.Data.Array.Basic
import Mathlib.Tactic

namespace Lean.Syntax
/-!
# `Syntax` filters
-/

partial
def filterMapM {m : Type → Type} [Monad m] (stx : Syntax) (f : Syntax → m (Option Syntax)) :
    m (Array Syntax) := do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

def filterMap (stx : Syntax) (f : Syntax → Option Syntax) : Array Syntax :=
  stx.filterMapM (m := Id) f

def filter (stx : Syntax) (f : Syntax → Bool) : Array Syntax :=
  stx.filterMap (fun s => if f s then some s else none)

end Lean.Syntax

open Lean Elab Command

/-- the `SyntaxNodeKind`s of `intro` and `intros`. -/
abbrev introTacs := #[``Lean.Parser.Tactic.intros, ``Lean.Parser.Tactic.intro]

open Lean.Parser.Tactic in
/-- if the input is `have .. : ∀ ids : typs, ... := by intro(s)...`, then
it returns `(#[ids, typs], #[intro(s)])`, otherwise it returns `(#[], #[])`.
Note that `typs` could be `null`.
-/
def getVarsAndInfos : Syntax → (Array Syntax × Array Syntax)
  | .node _ ``Lean.Parser.Term.haveIdDecl #[
      _, -- have id
      _, -- new binders as in `have test {x : Nat}`
      ts?,
      _, -- `:=`
      intro? -- actual proof
    ] =>
      let vars := match ts? with
        | .node s1 k1 #[
            .node s2 ``Lean.Parser.Term.typeSpec #[
              colon,
              .node _ ``Lean.Parser.Term.forall #[
                _, -- `∀`
                ids, -- identifiers
                ts, -- `typeSpec`
                _, -- comma `,`
                body  -- body of `∀`
              ]
            ]
          ] =>
          --dbg_trace "{Syntax.node s1 k1 #[.node s2 ``Lean.Parser.Term.typeSpec #[colon, body]]}"
          --dbg_trace "{Syntax.node s1 k1 #[.node s2 ``Lean.Parser.Term.typeSpec #[colon, body]]}"
          #[ids, ts]
        | _ => #[]
      let intros? := match intro? with
        | .node _ _ #[_, -- `by`
            .node _ ``tacticSeq #[.node _ ``tacticSeq1Indented #[.node _ _ args]]] =>
          let firstTac := args[0]!
          if introTacs.contains firstTac.getKind then
            #[firstTac]
          else #[]
        | _ => #[]
      (vars, intros?)
  | _ => default
--#eval do ← `(tactic| have : $ := $)
inspect
example : True := by
  have (test : Nat) : test = test := by rfl
  trivial
#check Lean.Parser.Term.letIdBinder

def getIntroVars : Syntax → Option (Array Syntax)
  | `(by $first; $_*) =>
    if introTacs.contains first.raw.getKind then
      some (first.raw.filter (·.isOfKind `ident))
    else
      none
  | _ => none

inspect
example : ∀ a b c d : Nat, a + b = c + d := by
  skip
  intro a b
  intros c
  intro
  sorry

/-
|-node Lean.Parser.Tactic.intro, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'intro'
|   |-node null, none
|   |   |-ident original: ⟨⟩⟨ ⟩-- (a,a)
|   |   |-ident original: ⟨⟩⟨\n  ⟩-- (b,b)

|-node Lean.Parser.Tactic.intros, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'intros'
|   |-node null, none
|   |   |-ident original: ⟨⟩⟨\n  ⟩-- (c,c)
-/

def dropIntroVars : Syntax → Option Syntax
  | stx@(.node s1 k #[intr, .node s2 `null vars]) =>
    let varsDropFirst := vars.erase (vars.getD 0 .missing)
    let skipStx := none --some <| mkNode ``Lean.Parser.Tactic.skip #[mkAtom "skip"]
    let newIntro : Syntax :=  -- recreate `intro [one fewer variable]`, even if input is `intros`
      .node s1 ``Lean.Parser.Tactic.intro #[mkAtomFrom intr "intro", .node s2 `null varsDropFirst]
    match k, vars.size with
      | ``Lean.Parser.Tactic.intros, 0 =>
        stx -- `intros` stays `intros`
      | ``Lean.Parser.Tactic.intros, 1 =>
        skipStx -- `intros x` converts to `skip`
      | ``Lean.Parser.Tactic.intros, _ =>
        some newIntro -- `intros x ...` converts to `intro ...`
      | ``Lean.Parser.Tactic.intro, 0 | ``Lean.Parser.Tactic.intro, 1 =>
        skipStx -- `intro` and `intro x` convert to `skip`
      | ``Lean.Parser.Tactic.intro, _ =>
        some newIntro -- `intro x y ...` converts to `intro y ...`
      | _, _ => none
  | _ => none

elab "fin " cmd:command : command => do
  elabCommand cmd
  let haves := cmd.raw.filter fun s => (introTacs.contains (s.getKind))
  for h in haves do
    logInfo m!"'{h}': '{dropIntroVars h}'"

fin
--inspect
example : ∀ a b c d  e : Nat, a + b = c + d + e := by
  skip
  intro
  intro a b
  intros c
  intro
  intros
  sorry

def Term.dropOneIntro {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Option Syntax)
  | `(by $first; $ts*) => do
    if introTacs.contains first.raw.getKind then
      match dropIntroVars first with
        | some newIntro =>
          let newtacs : Syntax.TSepArray `tactic "" :=
            { ts with elemsAndSeps := #[newIntro, mkNullNode] ++ ts.elemsAndSeps }
          let tacSeq ← `(tacticSeq| $[$newtacs]*)
          --logInfo m!"shortened '{first}': '{← `(term| by $tacSeq)}'"
          return some (← `(term| by $tacSeq))
        | none =>
          --logInfo m!"shortened '{first}': '{← `(term| by $[$ts]*)}'"
          return some (← `(term| by $[$ts]*))
    else
      return none
  | _ => return default

/--
`recombineBinders ts1 ts2` takes as input two `TSyntaxArray`s and removes the first entry of the
second array and pushes it to the last array.
Implicitly, it forces an update of the `SyntaxNodeKinds` with no check on type correctness:
we leave this check to the elaboration of the produced syntax in a later step.

In the intended application of `recombineBinders`, the `SyntaxNodeKinds` are
* ``ks1 = `Lean.Parser.Term.letIdBinder``,
* ``ks2 = [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder]``.

The corresponding `TSyntaxArray`s are
* the identifiers `id₁ id₂ ...` appearing in a `have this id₁ id₂ ...` tactic, and
* the variables bound in a `∀` quantifiers.
-/
def recombineBinders {ks1 ks2 : SyntaxNodeKinds} (ts1 : TSyntaxArray ks1) (ts2 : TSyntaxArray ks2) :
    Option (TSyntaxArray ks1 × TSyntaxArray ks2) :=
  if h : 0 < ts2.size then
    let first := ts2[0]
    (ts1.push ⟨first.raw⟩, ts2.erase first)
  else
    none

def allStxCore (cmd : Syntax) : Syntax → CommandElabM (Option (Syntax × Syntax))
  | stx@`(tactic| have $id:haveId $bi1* : ∀ $bi2*, $body := $t) => do
    match recombineBinders bi1 bi2 with
      | none => return none  -- if we ran out of `∀`, then we are done
      | some (bi1', bi2') =>
        let newTerm? := ← Term.dropOneIntro t
        match newTerm? with
          | none => return none  -- if we ran out of `intro(s)`, then we are done
          | some t' =>
            let newHave := ←
              if bi2'.isEmpty then
                `(tactic| have $id:haveId $[$bi1']* : $body := $(⟨t'⟩))
              else
                `(tactic| have $id:haveId $[$bi1']* : ∀ $[$bi2']*, $body := $(⟨t'⟩))
            let newCmd ← cmd.replaceM fun s => do
              if s == stx then return some newHave else return none
            let s ← modifyGet fun st => (st, { st with messages := {} })
            elabCommandTopLevel newCmd
            let msgs ← modifyGet (·.messages, s)
            if msgs.hasErrors then
              let errs := msgs.unreported.filter (·.severity matches .error)
              logInfo m!"{← errs.toArray.mapM (·.toString)}"
              return none
            else
              return some (newCmd, newHave)
  | _ => return none

partial
def allStx (cmd stx : Syntax) : CommandElabM Syntax := do
  match ← allStxCore cmd stx with
    | none => return stx
    | some (cmd, stx) => allStx cmd stx

elab "fh " cmd:command : command => do
  elabCommand cmd
  let haves := cmd.raw.filter (·.isOfKind ``Lean.Parser.Tactic.tacticHave_)
  for stx in haves do
--  if let some stx := cmd.raw.find? (·.isOfKind ``Lean.Parser.Tactic.tacticHave_) then
    --dbg_trace "found have"
    let newHave ← allStx cmd stx
    --logInfo newHave
    let newCmd ← cmd.raw.replaceM fun s => do if s == stx then return some newHave else return none
    if cmd == newCmd then
      logInfo m!"No change needed"
    else
      logWarning m!"Please use\n---\n{newCmd}\n---"

-- and the test is successful!
/--
warning: declaration uses 'sorry'
---
warning: Please use
---
example : True :=
  by
  have (_ : Nat) x y : x + y = 0 := by
    refine ?_
    sorry
  trivial
---
-/
#guard_msgs in
fh
--inspect
example : True := by
  have (_ : Nat) : ∀ x y, x + y = 0 := by
    intros s t
    refine ?_
    sorry
  trivial

/--
warning: declaration uses 'sorry'
---
info: No change needed
-/
#guard_msgs in
fh
--inspect
example : True := by
  have (_ : Nat) : ∀ x y, x + y = 0 := by
    refine ?_
    sorry
  trivial

/--
warning: Please use
---
example : True := by
  have (n : Nat) : n = n := by rfl
  trivial
---
-/
#guard_msgs in
fh
--inspect
example : True := by
  have : ∀ (n : Nat), n = n := by
    intro s
    rfl
  trivial

/--
warning: declaration uses 'sorry'
---
warning: Please use
---
example : True :=
  by
  have (k : Nat) _ : ‹_› = k := by
    intros
    sorry
  trivial
---
-/
#guard_msgs in
fh
--inspect
example : True := by
  have :  ∀ (k : Nat), ∀ _, ‹_› = k := by
    intros
    sorry
  trivial

example : True :=
  by
--  have (k : Nat) _ : ‹_› = k := by
--    intros
--    sorry
  trivial

/- broken syntax
example : True := by
  have _ : ‹_› = 0 := by
    intros
    sorry
  trivial
-/

example {_n : Nat} : True :=
  by
--  have {_} : ‹_› = 0 := by
--    --intro x
--    sorry
  trivial

example : True :=
  by
--  have (_ : Nat) _ : ‹_› = 0 := by
--    intros
--    sorry
--    --rfl
  trivial


#exit
inspect
example : True := by
  have : ∀ (test : Nat), test = test := by intros b; rfl
  trivial







/-- returns true iff the input is of the form `have .. : ∀ ids : typs, ... := by intro(s)...`. -/
def findForall (stx : Syntax) : Bool :=
  let (a, b) := getVarsAndInfos stx
  !(a.isEmpty || b.isEmpty)
/-
|-node Lean.Parser.Term.byTactic, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'by'
|   |-node Lean.Parser.Tactic.tacticSeq, none
|   |   |-node Lean.Parser.Tactic.tacticSeq1Indented, none
|   |   |   |-node null, none
|   |   |   |   |-node Lean.Parser.Tactic.intros, none
|   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- 'intros'
|   |   |   |   |   |-node null, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ';'
|   |   |   |   |-node Lean.Parser.Tactic.exact, none
|   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- 'exact'
|   |   |   |   |   |-node num, none
|   |   |   |   |   |   |-atom original: ⟨⟩⟨\n  ⟩-- '0'

-/


/-
|-node Lean.Parser.Term.haveIdDecl, none
|   |-node Lean.Parser.Term.haveId, none
|   |   |-node hygieneInfo, none
|   |   |   |-ident original: ⟨⟩⟨⟩-- ([anonymous],)
|   |-node null, none
-- ts?
|   |-node null, none
|   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |-node Lean.Parser.Term.forall, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '∀'
|   |   |   |   |-node null, none
|   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (a,a)
|   |   |   |   |-node null, none
|   |   |   |   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |   |   |   |-ident original: ⟨⟩⟨⟩-- (Nat,Nat)
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ','
|   |   |   |   |-node «term_=_», none
|   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (a,a)
|   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '='
|   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (a,a)

|   |-atom original: ⟨⟩⟨ ⟩-- ':='
-- intro?
|   |-node Lean.Parser.Term.sorry, none
|   |   |-atom original: ⟨⟩⟨\n  ⟩-- 'sorry'
-/

/-
|-node Lean.Parser.Term.haveIdDecl, none
|   |-node Lean.Parser.Term.haveId, none
|   |   |-node hygieneInfo, none
|   |   |   |-ident original: ⟨⟩⟨⟩-- ([anonymous],)
|   |-node null, none
|   |-node null, none
|   |-atom original: ⟨⟩⟨ ⟩-- ':='
|   |-node num, none
|   |   |-atom original: ⟨⟩⟨\n  ⟩-- '0'
-/

/-- extracts blocks like `have .. : ∀ ids : typs, ... := by intro(s)...`. -/
def extractHaves (stx : Syntax) : Array Syntax :=
  let haves := stx.filter (·.isOfKind ``Lean.Parser.Term.haveIdDecl)
  haves.filter findForall --fun s => !(s.filter? findForall).isEmpty
  --(haves.map (·.filter? findForall)).flatten

inspect
example : True := by
  have : ∀ a : Nat, a = a := by intro; rfl
  trivial


elab "fh " cmd:command : command => do
  elabCommand cmd
  for h in extractHaves cmd do
    if let (#[vs, _ts], #[intros]) := getVarsAndInfos h then
      Meta.inspect _ts --vs[0]
      logWarningAt h m!"variables could merge with '{intros}' {← `(command| variable $(⟨vs[0]⟩))}"
      --logWarningAt intros m!"the '{intros}' here!"

/-
|-node Lean.Parser.Term.haveIdDecl, none
|   |-node Lean.Parser.Term.haveId, none
|   |   |-node hygieneInfo, none
|   |   |   |-ident original: ⟨⟩⟨⟩-- ([anonymous],)
|   |-node null, none
|   |-node null, none
|   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |-node Lean.Parser.Term.forall, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '∀'
|   |   |   |   |-node null, none
|   |   |   |   |   |-node Lean.Parser.Term.explicitBinder, none
|   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- '('
|   |   |   |   |   |   |-node null, none
|   |   |   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |   |   |   |   |   |-node null, none
|   |   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |   |   |   |   |-ident original: ⟨⟩⟨⟩-- (Nat,Nat)
|   |   |   |   |   |   |-node null, none
|   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- ')'
|   |   |   |   |-node null, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ','
|   |   |   |   |-node «term_=_», none
|   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '='
|   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |-atom original: ⟨⟩⟨ ⟩-- ':='

|-node Lean.Parser.Term.haveIdDecl, none
|   |-node Lean.Parser.Term.haveId, none
|   |   |-node hygieneInfo, none
|   |   |   |-ident original: ⟨⟩⟨⟩-- ([anonymous],)
|   |-node null, none
|   |   |-node Lean.Parser.Term.explicitBinder, none
|   |   |   |-atom original: ⟨⟩⟨⟩-- '('
|   |   |   |-node null, none
|   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |   |   |-node null, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |   |-ident original: ⟨⟩⟨⟩-- (Nat,Nat)
|   |   |   |-node null, none
|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ')'
|   |-node null, none
|   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |-node «term_=_», none
|   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '='
|   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (test,test)
|   |-atom original: ⟨⟩⟨ ⟩-- ':='

-/


set_option pp.rawOnError true

fh
inspect
example : True := by
  have : ∀ (test : Nat), test = test := by intros b; rfl
  trivial


inspect
example : True := by
  have (test : Nat) : test = test := by rfl
  trivial

fh
example : True := by
  have : ∀ test, (test : Nat) = test := by intros; rfl
  trivial


#check Lean.Parser.Command.declValSimple
fh
set_option linter.unusedVariables false in
--inspect
example : True := by
  have test (n : Nat) : ∀ test : Nat, test = test := by intros b; rfl
  have bad : ∃ d : Nat, ∀ bad b : Nat, ∀ c : Nat, bad = bad := by
    use 0
    intro a b c
    have good : ∀ {good : Nat}, good = good := by
      intro a
      exact rfl
    exact rfl
  have also_good : ∀ also_good another_good : Nat, also_good = also_good := by
    have also_bad : ∃ z : Nat, z = 0 := ⟨_, rfl⟩
    intro a _
    exact rfl
  have not : Nat := 0
  exact .intro
