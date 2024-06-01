/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Sheafify
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The sheafification functor for presheaves of modules

In this file, we construct a functor
`PresheafOfModules.sheafification α : PresheafOfModules R₀ ⥤ SheafOfModules R`
for a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a preasheaf of rings
and `R` a sheaf of rings.

-/

universe v v' u u'

open CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.val)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasWeakSheafify J AddCommGroupCat.{v}]
  [J.WEqualsLocallyBijective AddCommGroupCat.{v}]

namespace PresheafOfModules

/-- Given a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a preasheaf of rings
and `R` a sheaf of rings (i.e. `R` identifies to the sheafification of `R₀`), this is
the associated sheaf of modules functor `PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R`. -/
noncomputable def sheafification : PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R where
  obj M₀ := sheafify α (toSheafify J M₀.presheaf)
  map f :=
    { val :=
      { hom := (presheafToSheaf J AddCommGroupCat ⋙ sheafToPresheaf _ _).map f.hom
        map_smul := sorry } }

/-- The sheafification of presheaves of modules commutes with the functor which
forgets the module structures. -/
noncomputable def sheafificationCompForgetCompToPresheaf :
    sheafification.{v} α ⋙ SheafOfModules.forget _ ⋙ toPresheaf _ ≅
      toPresheaf _ ⋙ presheafToSheaf J AddCommGroupCat ⋙ sheafToPresheaf J AddCommGroupCat :=
  Iso.refl _

end PresheafOfModules
