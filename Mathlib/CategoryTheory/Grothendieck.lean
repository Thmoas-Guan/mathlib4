/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `Grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).obj f ⟶ f'`

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consists again of `β : b ⟶ b'` and `φ : f ⟶ (F.map (op β)).obj f'`.

## References

See also `CategoryTheory.Functor.Elements` for the category of elements of functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/


universe u

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]
variable (F : C ⥤ Cat)

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
-- Porting note(#5171): no such linter yet
-- @[nolint has_nonempty_instance]
structure Grothendieck where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F.obj base

namespace Grothendieck

variable {F}

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : Grothendieck F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : (F.map base).obj X.fiber ⟶ Y.fiber

@[ext (iff := false)]
theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  aesop_cat

/-- The identity morphism in the Grothendieck category.
-/
@[simps]
def id (X : Grothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by erw [CategoryTheory.Functor.map_id, Functor.id_obj X.fiber])

instance (X : Grothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the Grothendieck category.
-/
@[simps]
def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by erw [Functor.map_comp, Functor.comp_obj]) ≫ (F.map g.base).map f.fiber ≫ g.fiber

attribute [local simp] eqToHom_map

instance : Category (Grothendieck F) where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp := @fun X Y Z f g => Grothendieck.comp f g
  comp_id := @fun X Y f => by
    dsimp; ext
    · simp
    · dsimp
      rw [← NatIso.naturality_2 (eqToIso (F.map_id Y.base)) f.fiber]
      simp
  id_comp := @fun X Y f => by dsimp; ext <;> simp
  assoc := @fun W X Y Z f g h => by
    dsimp; ext
    · simp
    · dsimp
      rw [← NatIso.naturality_2 (eqToIso (F.map_comp _ _)) f.fiber]
      simp

@[simp]
theorem id_fiber' (X : Grothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by erw [CategoryTheory.Functor.map_id, Functor.id_obj X.fiber]) :=
  id_fiber X

theorem congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

section

variable (F)

/-- The forgetful functor from `Grothendieck F` to the source category. -/
@[simps!]
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map := @fun X Y f => f.1

end

universe w

variable (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps!]
def grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements where
  obj X := ⟨X.1, X.2.as⟩
  map := @fun X Y f => ⟨f.1, f.2.1.1⟩

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
-- Porting note:
-- `simps` is incorrectly producing Prop-valued projections here,
-- so we manually specify which ones to produce.
-- See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/!4.233204.20simps.20bug.20.28Grothendieck.20construction.29
@[simps! obj_base obj_fiber_as map_base]
def grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) where
  obj X := ⟨X.1, ⟨X.2⟩⟩
  map f := ⟨f.1, ⟨⟨f.2⟩⟩⟩

/-- The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
-- See porting note on grothendieckTypeToCatInverse.
-- We just want to turn off grothendieckTypeToCat_inverse_map_fiber_down_down,
-- so have to list the complement here for `@[simps]`.
@[simps! functor_obj_fst functor_obj_snd functor_map_coe inverse_obj_base inverse_obj_fiber_as
  inverse_map_base unitIso_hom_app_base unitIso_hom_app_fiber unitIso_inv_app_base
  unitIso_inv_app_fiber counitIso_hom_app_coe counitIso_inv_app_coe]
def grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where
  functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact Iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        simp
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact Iso.refl _)
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        dsimp at *
        simp
        rfl)
  functor_unitIso_comp := by
    rintro ⟨_, ⟨⟩⟩
    dsimp
    simp
    rfl

end Grothendieck

end CategoryTheory
