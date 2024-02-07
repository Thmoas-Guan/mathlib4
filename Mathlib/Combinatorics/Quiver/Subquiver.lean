/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.Order.Notation
import Mathlib.Combinatorics.Quiver.Basic

#align_import combinatorics.quiver.subquiver from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
## Wide subquivers

A wide subquiver `H` of a quiver `H` consists of a subset of the edge set `a ⟶ b` for
every pair of vertices `a b : V`. We include 'wide' in the name to emphasize that these
subquivers by definition contain all vertices.
-/

universe v u

/-- A wide subquiver `H` of `G` picks out a set `H a b` of arrows from `a` to `b`
    for every pair of vertices `a b`.

    NB: this does not work for `Prop`-valued quivers. It requires `G : Quiver.{v+1} V`. -/
def WideSubquiver (V) [Quiver.{v + 1} V] :=
  ∀ a b : V, Set (a ⟶ b)
#align wide_subquiver WideSubquiver

namespace WideSubquiver

/-- A type synonym for `V`, when thought of as a quiver having only the arrows from
some `WideSubquiver`. -/
-- Porting note: no hasNonemptyInstance linter yet
@[nolint unusedArguments]
def toType (V) [Quiver V] (_ : WideSubquiver V) : Type u := V
#align wide_subquiver.to_Type WideSubquiver.toType

variable {V : Type u} [Quiver.{v + 1} V]

instance wideSubquiverHasCoeToSort : CoeSort (WideSubquiver V) (Type u) where
  coe H := WideSubquiver.toType V H

-- Boilerplate for wrapping/unwrapping the type synonym
/-- Wrap a vertex of `V` into a vertex of the wide subquiver `W`. -/
protected def mk (W : WideSubquiver V) (x : V) : W := x
/-- Unwrap of the wide subquiver `W` to a vertex of `V`. -/
@[inline, always_inline] def run {W : WideSubquiver V} (x : W) : V := x
@[simp] lemma run_mk (W : WideSubquiver V) (x : V) : run (W.mk x) = x := rfl
@[simp] lemma mk_run {W : WideSubquiver V} (x : W) : W.mk (run x) = x := rfl

/-- A wide subquiver viewed as a quiver on its own. -/
instance quiver (H : WideSubquiver V) : Quiver H where
  Hom a b := { f // f ∈ H a b }

/-- The canonical inclusion of a wide subquiver into the original quiver. -/
def inclusion (W : WideSubquiver V) : W ⥤q V where
  obj X := run X
  map f := f.val

end WideSubquiver

namespace Quiver

instance {V} [Quiver V] : Bot (WideSubquiver V) :=
  ⟨fun _ _ ↦ ∅⟩

instance {V} [Quiver V] : Top (WideSubquiver V) :=
  ⟨fun _ _ ↦ Set.univ⟩

noncomputable instance {V} [Quiver V] : Inhabited (WideSubquiver V) :=
  ⟨⊤⟩

-- TODO Unify with `CategoryTheory.Arrow`? (The fields have been named to match.)
/-- `Total V` is the type of _all_ arrows of `V`. -/
-- Porting note: no hasNonemptyInstance linter yet
@[ext]
structure Total (V : Type u) [Quiver.{v} V] : Sort max (u + 1) v where
  /-- the source vertex of an arrow -/
  left : V
  /-- the target vertex of an arrow -/
  right : V
  /-- an arrow -/
  hom : left ⟶ right
#align quiver.total Quiver.Total
#align quiver.total.ext Quiver.Total.ext
#align quiver.total.ext_iff Quiver.Total.ext_iff

/-- A wide subquiver of `G` can equivalently be viewed as a total set of arrows. -/
@[simps (config := .asFn) apply symm_apply]
def wideSubquiverEquivSetTotal {V} [Quiver V] :
    WideSubquiver V ≃
      Set (Total V) where
  toFun H := { e | e.hom ∈ H e.left e.right }
  invFun S a b := { e | Total.mk a b e ∈ S }
  left_inv _ := rfl
  right_inv _ := rfl
#align quiver.wide_subquiver_equiv_set_total Quiver.wideSubquiverEquivSetTotal

/-- An `L`-labelling of a quiver assigns to every arrow an element of `L`. -/
def Labelling (V : Type u) [Quiver V] (L : Sort*) :=
  ∀ ⦃a b : V⦄, (a ⟶ b) → L
#align quiver.labelling Quiver.Labelling

instance {V : Type u} [Quiver V] (L) [Inhabited L] : Inhabited (Labelling V L) :=
  ⟨fun _ _ _ ↦ default⟩

end Quiver
