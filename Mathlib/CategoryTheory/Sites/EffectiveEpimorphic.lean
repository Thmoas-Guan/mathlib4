/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.EffectiveEpi.Basic
/-!

# Effective epimorphic sieves

We define the notion of effective epimorphic (pre)sieves and provide some API for relating the
notion with the notions of effective epimorphism and effective epimorphic family.

More precisely, if `f` is a morphism, then `f` is an effective epi if and only if the sieve
it generates is effective epimorphic; see `CategoryTheory.Sieve.effectiveEpimorphic_singleton`.
The analogous statement for a family of morphisms is in the theorem
`CategoryTheory.Sieve.effectiveEpimorphic_family`.

-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

/-- A sieve is effective epimorphic if the associated cocone is a colimit cocone. -/
def Sieve.EffectiveEpimorphic {X : C} (S : Sieve X) : Prop :=
  Nonempty (IsColimit (S : Presieve X).cocone)

/-- A presieve is effective epimorphic if the cocone associated to the sieve it generates
is a colimit cocone. -/
abbrev Presieve.EffectiveEpimorphic {X : C} (S : Presieve X) : Prop :=
  (Sieve.generate S).EffectiveEpimorphic

/--
The sieve of morphisms which factor through a given morphism `f`.
This is equal to `Sieve.generate (Presieve.singleton f)`, but has
more convenient definitional properties.
-/
def Sieve.generateSingleton {X Y : C} (f : Y ⟶ X) : Sieve X where
  arrows Z := { g | ∃ (e : Z ⟶ Y), e ≫ f = g }
  downward_closed := by
    rintro W Z g ⟨e,rfl⟩ q
    exact ⟨q ≫ e, by simp⟩

lemma Sieve.generateSingleton_eq {X Y : C} (f : Y ⟶ X) :
    Sieve.generate (Presieve.singleton f) = Sieve.generateSingleton f := by
  ext Z g
  constructor
  · rintro ⟨W,i,p,⟨⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨g,h⟩
    exact ⟨Y,g,f,⟨⟩,h⟩

/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a single arrow is effective epimorphic if and only if
the arrow is an effective epi.
-/
def isColimitOfEffectiveEpiStruct {X Y : C} (f : Y ⟶ X) (Hf : EffectiveEpiStruct f) :
    IsColimit (Sieve.generateSingleton f : Presieve X).cocone :=
  letI D := FullSubcategory fun T : Over X => Sieve.generateSingleton f T.hom
  letI F : D ⥤ _ := (Sieve.generateSingleton f).arrows.diagram
  { desc := fun S => Hf.desc (S.ι.app ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩) <| by
      intro Z g₁ g₂ h
      let Y' : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ f), g₁, rfl⟩
      let g₁' : Z' ⟶ Y' := Over.homMk g₁
      let g₂' : Z' ⟶ Y' := Over.homMk g₂ (by simp [h])
      change F.map g₁' ≫ _ = F.map g₂' ≫ _
      simp only [S.w]
    fac := by
      rintro S ⟨T,g,hT⟩
      dsimp
      nth_rewrite 1 [← hT, Category.assoc, Hf.fac]
      let y : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let x : D := ⟨Over.mk T.hom, g, hT⟩
      let g' : x ⟶ y := Over.homMk g
      change F.map g' ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm
      dsimp
      generalize_proofs h1 h2
      apply Hf.uniq _ h2
      exact hm ⟨Over.mk f, 𝟙 _, by simp⟩ }

/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a single arrow is effective epimorphic if and only if
the arrow is an effective epi.
-/
noncomputable
def effectiveEpiStructOfIsColimit {X Y : C} (f : Y ⟶ X)
    (Hf : IsColimit (Sieve.generateSingleton f : Presieve X).cocone) :
    EffectiveEpiStruct f :=
  let aux {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    Cocone (Sieve.generateSingleton f).arrows.diagram :=
    { pt := W
      ι := {
        app := fun ⟨T,hT⟩ => hT.choose ≫ e
        naturality := by
          rintro ⟨A,hA⟩ ⟨B,hB⟩ (q : A ⟶ B)
          dsimp; simp only [← Category.assoc, Category.comp_id]
          apply h
          rw [Category.assoc, hB.choose_spec, hA.choose_spec, Over.w] } }
  { desc := fun {W} e h => Hf.desc (aux e h)
    fac := by
      intro W e h
      dsimp
      have := Hf.fac (aux e h) ⟨Over.mk f, 𝟙 _, by simp⟩
      dsimp at this; rw [this]; clear this
      nth_rewrite 2 [← Category.id_comp e]
      apply h
      generalize_proofs hh
      rw [hh.choose_spec, Category.id_comp]
    uniq := by
      intro W e h m hm
      dsimp
      apply Hf.uniq (aux e h)
      rintro ⟨A,g,hA⟩
      dsimp
      nth_rewrite 1 [← hA, Category.assoc, hm]
      apply h
      generalize_proofs hh
      rwa [hh.choose_spec] }

lemma Sieve.effectiveEpimorphic_singleton {X Y : C} (f : Y ⟶ X) :
    (Presieve.singleton f).EffectiveEpimorphic ↔ (EffectiveEpi f) := by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateSingleton_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiStructOfIsColimit _) h
  · rintro ⟨h⟩
    show Nonempty _
    rw [Sieve.generateSingleton_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiStruct _) h

/--
The sieve of morphisms which factor through a morphism in a given family.
This is equal to `Sieve.generate (Presieve.ofArrows X π)`, but has
more convenient definitional properties.
-/
def Sieve.generateFamily {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    Sieve B where
  arrows Y := { f | ∃ (a : α) (g : Y ⟶ X a), g ≫ π a = f }
  downward_closed := by
    rintro Y₁ Y₂ g₁ ⟨a,q,rfl⟩ e
    exact ⟨a, e ≫ q, by simp⟩

lemma Sieve.generateFamily_eq {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    Sieve.generate (Presieve.ofArrows X π) = Sieve.generateFamily X π := by
  ext Y g
  constructor
  · rintro ⟨W, g, f, ⟨a⟩, rfl⟩
    exact ⟨a, g, rfl⟩
  · rintro ⟨a, g, rfl⟩
    exact ⟨_, g, π a, ⟨a⟩, rfl⟩

/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a family of arrows is effective epimorphic if and only if
the family is an effective epi.
-/
def isColimitOfEffectiveEpiFamilyStruct {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) (H : EffectiveEpiFamilyStruct X π) :
    IsColimit (Sieve.generateFamily X π : Presieve B).cocone :=
  letI D := FullSubcategory fun T : Over B => Sieve.generateFamily X π T.hom
  letI F : D ⥤ _ := (Sieve.generateFamily X π).arrows.diagram
  { desc := fun S => H.desc (fun a => S.ι.app ⟨Over.mk (π a), ⟨a,𝟙 _, by simp⟩⟩) <| by
      intro Z a₁ a₂ g₁ g₂ h
      dsimp
      let A₁ : D := ⟨Over.mk (π a₁), a₁, 𝟙 _, by simp⟩
      let A₂ : D := ⟨Over.mk (π a₂), a₂, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ π a₁), a₁, g₁, rfl⟩
      let i₁ : Z' ⟶ A₁ := Over.homMk g₁
      let i₂ : Z' ⟶ A₂ := Over.homMk g₂
      change F.map i₁ ≫ _ = F.map i₂ ≫ _
      simp only [S.w]
    fac := by
      intro S ⟨T, a, (g : T.left ⟶ X a), hT⟩
      dsimp
      nth_rewrite 1 [← hT, Category.assoc, H.fac]
      let A : D := ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      let B : D := ⟨Over.mk T.hom, a, g, hT⟩
      let i : B ⟶ A := Over.homMk g
      change F.map i ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm; dsimp
      apply H.uniq
      intro a
      exact hm ⟨Over.mk (π a), a, 𝟙 _, by simp⟩ }

/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a family of arrows is effective epimorphic if and only if
the family is an effective epi.
-/
noncomputable
def effectiveEpiFamilyStructOfIsColimit {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B))
    (H : IsColimit (Sieve.generateFamily X π : Presieve B).cocone) :
    EffectiveEpiFamilyStruct X π :=
  let aux {W : C} (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) :
    Cocone (Sieve.generateFamily X π).arrows.diagram := {
      pt := W
      ι := {
        app := fun ⟨T,hT⟩ => hT.choose_spec.choose ≫ e hT.choose
        naturality := by
          intro ⟨A,a,(g₁ : A.left ⟶ _),ha⟩ ⟨B,b,(g₂ : B.left ⟶ _),hb⟩ (q : A ⟶ B)
          dsimp; rw [Category.comp_id, ← Category.assoc]
          apply h; rw [Category.assoc]
          generalize_proofs h1 h2 h3 h4
          rw [h2.choose_spec, h4.choose_spec, Over.w] } }
  { desc := fun {W} e h => H.desc (aux e h)
    fac := by
      intro W e h a
      dsimp
      have := H.fac (aux e h) ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      dsimp at this; rw [this]; clear this
      conv_rhs => rw [← Category.id_comp (e a)]
      apply h
      generalize_proofs h1 h2
      rw [h2.choose_spec, Category.id_comp]
    uniq := by
      intro W e h m hm
      apply H.uniq (aux e h)
      rintro ⟨T, a, (g : T.left ⟶ _), ha⟩
      dsimp
      nth_rewrite 1 [← ha, Category.assoc, hm]
      apply h
      generalize_proofs h1 h2
      rwa [h2.choose_spec] }

lemma Sieve.effectiveEpimorphic_family {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    (Presieve.ofArrows X π).EffectiveEpimorphic ↔ EffectiveEpiFamily X π := by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateFamily_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiFamilyStructOfIsColimit _ _) h
  · rintro ⟨h⟩
    show Nonempty _
    rw [Sieve.generateFamily_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiFamilyStruct _ _) h

end CategoryTheory
