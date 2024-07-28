import Mathlib.CategoryTheory.Triangulated.Filtered.Basic

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

namespace Triangulated

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C (ℤ × ℤ)]
  [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hP : FilteredTriangulated C]

namespace FilteredTriangulated

lemma triangle_map_ext' (a b : ℤ) (hab : a < b) {T T' : Triangle C} (f₁ f₂ : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (h₀ : hP.IsGE T.obj₁ b) (h₁ : hP.IsLE T'.obj₃ a)
    (H : f₁.hom₂ = f₂.hom₂) : f₁ = f₂ := by
  suffices ∀ (f : T ⟶ T') (_ : f.hom₂ = 0), f = (0 : T ⟶ T') by
    rw [← sub_eq_zero]
    apply this
    dsimp
    rw [H, sub_self]
  intro f hf
  ext
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT') f.hom₁ (by
      have eq := f.comm₁
      dsimp at eq ⊢
      rw [← eq, hf, comp_zero])
    have hg' : g = 0 := hP.zero_of_isGE_of_isLE g a b hab h₀
      (hP.shift_isLE_of_isLE T'.obj₃ a (-1))
    simp [hg, hg']
  · simp [hf]
  · obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT f.hom₃ (by rw [f.comm₂, hf, zero_comp])
    have hg' : g = 0 := hP.zero_of_isGE_of_isLE g a b hab
      (hP.shift_isGE_of_isGE T.obj₁ b 1) h₁
    simp [hg, hg']

lemma triangle_map_exists (n₀ n₁ : ℤ) (h : n₀ < n₁) (T T' : Triangle C)
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (φ : T.obj₂ ⟶ T'.obj₂)
    (h₀ : hP.IsGE T.obj₁ n₁)
    (h₁ : hP.IsLE T'.obj₃ n₀) :
    ∃ (f : T ⟶ T'), f.hom₂ = φ := by
  obtain ⟨a, comm₁⟩ := T'.coyoneda_exact₂ hT' (T.mor₁ ≫ φ) (hP.zero _ n₀ n₁ h)
  obtain ⟨c, ⟨comm₂, comm₃⟩⟩ := complete_distinguished_triangle_morphism _ _ hT hT' a φ comm₁
  exact ⟨
    { hom₁ := a
      hom₂ := φ
      hom₃ := c
      comm₁ := comm₁
      comm₂ := comm₂
      comm₃ := comm₃ }, rfl⟩

lemma triangle_iso_exists (n₀ n₁ : ℤ) (h : n₀ < n₁) (T T' : Triangle C)
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (e : T.obj₂ ≅ T'.obj₂)
    (h₀ : hP.IsGE T.obj₁ n₁) (h₁ : hP.IsLE T.obj₃ n₀)
    (h₀' : hP.IsGE T'.obj₁ n₁) (h₁' : hP.IsLE T'.obj₃ n₀) :
    ∃ (e' : T ≅ T'), e'.hom.hom₂ = e.hom := by
  obtain ⟨hom, hhom⟩ := triangle_map_exists _ _ h _ _ hT hT' e.hom h₀ h₁'
  obtain ⟨inv, hinv⟩ := triangle_map_exists _ _ h _ _ hT' hT e.inv h₀' h₁
  refine ⟨
    { hom := hom
      inv := inv
      hom_inv_id := triangle_map_ext' n₀ n₁ (by linarith) _ _ hT hT h₀ h₁
        (by simp only [comp_hom₂, id_hom₂, hhom, hinv, e.hom_inv_id])
      inv_hom_id := triangle_map_ext' n₀ n₁ (by linarith) _ _ hT' hT' h₀' h₁'
        (by simp only [comp_hom₂, id_hom₂, hhom, hinv, e.inv_hom_id]) }, hhom⟩

namespace TruncAux

variable (n : ℤ) (A : C)

noncomputable def triangle : Triangle C :=
  Triangle.mk
    (hP.exists_triangle A (n-1) n
      (by linarith)).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (hP.exists_triangle A (n-1) n
      (by linarith)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (hP.exists_triangle A (n-1) n
      (by linarith)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

lemma triangle_distinguished :
    triangle n A ∈ distTriang C :=
  (hP.exists_triangle A (n-1) n (by linarith)
    ).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

instance triangle_obj₁_isGE (n : ℤ) :
    hP.IsGE (triangle n A).obj₁ n := by
  exact ⟨(hP.exists_triangle A (n-1) n (by linarith)).choose_spec.choose_spec.choose⟩

@[simp]
lemma triangle_obj₂ :
    (triangle n A).obj₂ = A := by rfl

instance triangle_obj₃_isLE :
    hP.IsLE (triangle n A).obj₃ (n-1) :=
  ⟨(hP.exists_triangle A (n-1) n (by linarith)).choose_spec.choose_spec.choose_spec.choose⟩

variable {A}
variable {B : C} (φ : A ⟶ B)

lemma triangle_map_ext (f₁ f₂ : triangle n A ⟶ triangle n B)
    (H : f₁.hom₂ = f₂.hom₂) : f₁ = f₂ :=
  triangle_map_ext' (n-1) n (by linarith) _ _
    (triangle_distinguished n A) (triangle_distinguished n B)
    inferInstance inferInstance H

noncomputable def triangleMap : triangle n A ⟶ triangle n B :=
  have H := triangle_map_exists (n-1) n (by linarith) _ _ (triangle_distinguished n A)
    (triangle_distinguished n B) φ inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := φ
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

noncomputable def triangleFunctor : C ⥤ Triangle C where
  obj := triangle n
  map φ := triangleMap n φ
  map_id _ := triangle_map_ext n _ _ rfl
  map_comp _ _ := triangle_map_ext n _ _ rfl

variable (A)

lemma triangleFunctor_obj_distinguished :
  (triangleFunctor n).obj A ∈ distTriang C :=
    triangle_distinguished n A

@[simp]
lemma triangleFunctor_obj_obj₂ : ((triangleFunctor n).obj A).obj₂ = A := rfl

@[simp]
lemma triangleFunctor_map_hom₂ : ((triangleFunctor n).map φ).hom₂ = φ := rfl

instance isGE_triangleFunctor_obj_obj₁ :
    hP.IsGE ((triangleFunctor n).obj A).obj₁ n := by
  dsimp [triangleFunctor]
  infer_instance

instance isLE_triangleFunctor_obj_obj₃ :
    hP.IsLE ((triangleFunctor n).obj A).obj₃ (n-1) := by
  dsimp [triangleFunctor]
  infer_instance

noncomputable def triangleMapOfGE (a b : ℤ) (h : b ≤ a) : triangle a A ⟶ triangle b A :=
  have H := triangle_map_exists (b-1) a (by linarith) _ _ (triangle_distinguished a A)
    (triangle_distinguished b A) (𝟙 _) inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := 𝟙 _
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

noncomputable def triangleFunctorNatTransOfGE (a b : ℤ) (h : b ≤ a) :
    triangleFunctor a ⟶ triangleFunctor (hP := hP) b where
  app X := triangleMapOfGE X a b h
  naturality {X₁ X₂} φ := by
    refine triangle_map_ext' (b-1) a (by linarith) _ _
      (triangleFunctor_obj_distinguished a X₁) (triangleFunctor_obj_distinguished b X₂)
      inferInstance inferInstance ?_
    dsimp [triangleMapOfGE]
    rw [id_comp, comp_id]

@[simp]
lemma triangleFunctorNatTransOfGE_app_hom₂ (a b : ℤ) (h : b ≤ a) (X : C) :
    ((triangleFunctorNatTransOfGE a b h).app X).hom₂ = 𝟙 X := rfl

lemma triangleFunctorNatTransOfGE_trans (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    triangleFunctorNatTransOfGE a b hab ≫ triangleFunctorNatTransOfGE b c hbc =
      triangleFunctorNatTransOfGE a c (hbc.trans hab) (hP := hP) := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext' (c-1) a (by linarith) _ _
    (triangleFunctor_obj_distinguished a X) (triangleFunctor_obj_distinguished c X)
    inferInstance inferInstance (by aesop_cat)

lemma triangleFunctorNatTransOfGE_refl (a : ℤ) :
    triangleFunctorNatTransOfGE (hP := hP) a a (by rfl) = 𝟙 _ := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext' (a-1) a (by linarith) _ _
    (triangleFunctor_obj_distinguished a X) (triangleFunctor_obj_distinguished a X)
    inferInstance inferInstance (by aesop_cat)

instance : (triangleFunctor (hP := hP) n).Additive where
  map_add := triangle_map_ext n  _ _ rfl

noncomputable def triangleFunctorIsoShift_exists (a : ℤ) :=
  triangle_iso_exists (n - 1) n (by linarith) _ _
      (triangleFunctor_obj_distinguished n (A⟦a⟧))
      (Triangle.shift_distinguished _ (triangleFunctor_obj_distinguished n A) a) (Iso.refl _)
      inferInstance inferInstance (shift_isGE_of_isGE _ n a ) (shift_isLE_of_isLE _ (n - 1) a)

set_option maxHeartbeats 500000 in
noncomputable instance : (triangleFunctor (hP := hP) n).CommShift ℤ where
  iso a := by
    refine NatIso.ofComponents (fun A ↦ Classical.choose (triangleFunctorIsoShift_exists n A a)) ?_
    intro A B f
    refine triangle_map_ext' (n - 1) n (by linarith) _ _ ?_ ?_ ?_ ?_ ?_
    · simp only [Functor.comp_obj]
      exact triangleFunctor_obj_distinguished _ _
    · simp only [Functor.comp_obj]
      exact Triangle.shift_distinguished _ (triangleFunctor_obj_distinguished _ _) _
    · simp only [Functor.comp_obj]
      exact inferInstance
    · simp only [Triangle.shiftFunctor_eq, Functor.comp_obj, Triangle.shiftFunctor_obj,
      triangleFunctor_obj_obj₂, Triangle.mk_obj₃]
      exact shift_isLE_of_isLE _ (n - 1) a
    · simp only [Functor.comp_obj, triangleFunctor_obj_obj₂, Triangle.shiftFunctor_eq,
      Triangle.shiftFunctor_obj, Triangle.mk_obj₂, Functor.comp_map, Iso.refl_hom, id_eq,
      triangleCategory_comp, TriangleMorphism.comp_hom₂, triangleFunctor_map_hom₂,
      Triangle.shiftFunctor_map_hom₂]
      rw [Classical.choose_spec (triangleFunctorIsoShift_exists n A a),
        Classical.choose_spec (triangleFunctorIsoShift_exists n B a)]
      simp only [triangleFunctor_obj_obj₂, Triangle.shiftFunctor_eq, Triangle.shiftFunctor_obj,
        Functor.comp_obj, Triangle.mk_obj₂, Iso.refl_hom, comp_id, id_comp]
  zero := by
    apply Iso.ext
    apply NatTrans.ext
    ext1 A
    refine triangle_map_ext' (n - 1) n (by linarith) _ _ ?_ ?_ ?_ ?_ ?_
    . exact triangleFunctor_obj_distinguished _ _
    · exact Triangle.shift_distinguished _ (triangleFunctor_obj_distinguished _ _) _
    · simp only [Functor.comp_obj]
      exact inferInstance
    · simp only [Triangle.shiftFunctor_eq, Functor.comp_obj, Triangle.shiftFunctor_obj,
      triangleFunctor_obj_obj₂, Int.negOnePow_zero, one_smul, Triangle.mk_obj₃]
      exact shift_isLE_of_isLE _ (n - 1) 0
    · simp only [Functor.comp_obj, triangleFunctor_obj_obj₂, Triangle.shiftFunctor_eq,
      Triangle.shiftFunctor_obj, Int.negOnePow_zero, Triangle.mk_obj₂, Iso.refl_hom,
      NatIso.ofComponents_hom_app, Functor.CommShift.isoZero_hom_app, Triangle.shiftFunctorZero_eq,
      triangleCategory_comp, TriangleMorphism.comp_hom₂, triangleFunctor_map_hom₂,
      Triangle.shiftFunctorZero_inv_app_hom₂, Iso.hom_inv_id_app]
      rw [Classical.choose_spec (triangleFunctorIsoShift_exists n A 0)]
      simp only [triangleFunctor_obj_obj₂, Triangle.shiftFunctor_eq, Triangle.shiftFunctor_obj,
        Int.negOnePow_zero, Functor.comp_obj, Triangle.mk_obj₂, Iso.refl_hom]
  add a b := by
    apply Iso.ext
    apply NatTrans.ext
    ext1 A
    refine triangle_map_ext' (n - 1) n (by linarith) _ _ ?_ ?_ ?_ ?_ ?_
    · simp only [Functor.comp_obj]
      exact triangleFunctor_obj_distinguished _ _
    · simp only [Functor.comp_obj]
      exact Triangle.shift_distinguished _ (triangleFunctor_obj_distinguished _ _) _
    · simp only [Functor.comp_obj]
      exact inferInstance
    · simp only [Triangle.shiftFunctor_eq, Functor.comp_obj, Triangle.shiftFunctor_obj,
      triangleFunctor_obj_obj₂, Triangle.mk_obj₃]
      exact shift_isLE_of_isLE _ (n - 1) _
    · simp only [NatIso.ofComponents_hom_app, Functor.CommShift.isoAdd_hom_app]
      rw [Classical.choose_spec (triangleFunctorIsoShift_exists n A (a + b)), Iso.refl_hom]
      simp only [comp_hom₂]
      conv_rhs => congr; rfl; congr
                  rw [Classical.choose_spec (triangleFunctorIsoShift_exists n _ b), Iso.refl_hom]
                  rfl; congr
                  erw [Triangle.shiftFunctor_map_hom₂]
                  rw [Classical.choose_spec (triangleFunctorIsoShift_exists n A a), Iso.refl_hom,
                    Functor.map_id]
      erw [id_comp, id_comp]
      simp only [Functor.comp_obj, triangleFunctor_obj_obj₂, Triangle.shiftFunctor_eq,
        Triangle.shiftFunctor_obj, Triangle.mk_obj₂, triangleFunctor_map_hom₂, Triangle.mk_obj₁,
        Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
        Triangle.shiftFunctorAdd_eq, Triangle.shiftFunctorAdd'_inv_app_hom₂]
      rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
      simp only [Iso.hom_inv_id_app]

#synth (triangleFunctor n).CommShift ℤ (C := C)

end TruncAux

noncomputable def truncLT (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor n ⋙ Triangle.π₃

instance (n : ℤ) : (truncLT (hP := hP) n).Additive where
  map_add {_ _ f g} := by
    dsimp only [truncLT, Functor.comp_map]
    rw [Functor.map_add]
    rfl

noncomputable instance (n : ℤ) : (truncLT (hP := hP) n).CommShift ℤ := Functor.CommShift.comp _ _

noncomputable def truncLTπ (n : ℤ) : 𝟭 _ ⟶ truncLT (hP := hP) n:=
  whiskerLeft (TruncAux.triangleFunctor n) Triangle.π₂Toπ₃

noncomputable def truncGE (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor n ⋙ Triangle.π₁

instance (n : ℤ) : (truncGE (hP := hP) n).Additive where
  map_add {_ _ f g} := by
    dsimp only [truncGE, Functor.comp_map]
    rw [Functor.map_add]
    rfl

noncomputable instance (n : ℤ) : (truncGE (hP := hP) n).CommShift ℤ := Functor.CommShift.comp _ _

noncomputable def truncGEι (n : ℤ) : truncGE (hP := hP) n ⟶ 𝟭 _ :=
  whiskerLeft (TruncAux.triangleFunctor n) Triangle.π₁Toπ₂

instance (X : C) (n : ℤ) : hP.IsLE ((truncLT n).obj X) (n-1) := by
  dsimp [truncLT]
  infer_instance

instance (X : C) (n : ℤ) : hP.IsGE ((truncGE n).obj X) n := by
  dsimp [truncGE]
  infer_instance

noncomputable def truncLTδGE (n : ℤ) :
  truncLT n ⟶ truncGE n ⋙ shiftFunctor C (1 : ℤ) :=
    whiskerLeft (TruncAux.triangleFunctor n) Triangle.π₃Toπ₁

@[simps!]
noncomputable def triangleGELT (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (truncGEι n) (truncLTπ n) (truncLTδGE n)

lemma triangleGELT_distinguished (n : ℤ) (X : C) :
    (triangleGELT n).obj X ∈ distTriang C :=
  TruncAux.triangleFunctor_obj_distinguished n X

@[reassoc (attr := simp)]
lemma truncGEι_comp_truncLEπ_app (n : ℤ) (X : C) :
    (truncGEι n).app X ≫ (truncLTπ n).app X = 0 :=
  comp_distTriang_mor_zero₁₂ _ ((triangleGELT_distinguished n X))

@[reassoc (attr := simp)]
lemma truncLTπ_comp_truncLTδGE_app (n : ℤ) (X : C) :
    (truncLTπ n).app X ≫ (truncLTδGE n).app X = 0 :=
  comp_distTriang_mor_zero₂₃ _ ((triangleGELT_distinguished n X))

@[reassoc (attr := simp)]
lemma truncLTδGE_comp_truncGEι_app (n : ℤ) (X : C) :
    (truncLTδGE n).app X ≫ ((truncGEι n).app X)⟦(1 : ℤ)⟧' = 0 :=
  comp_distTriang_mor_zero₃₁ _ ((triangleGELT_distinguished n X))

@[reassoc (attr := simp)]
lemma truncGEι_comp_truncLTπ (n : ℤ) :
    truncGEι (hP := hP) n ≫ truncLTπ n = 0 := by aesop_cat

@[reassoc (attr := simp)]
lemma truncLTπ_comp_truncLTδGE (n : ℤ) :
    truncLTπ (hP := hP) n ≫ truncLTδGE n = 0 := by aesop_cat

@[reassoc (attr := simp)]
lemma truncLTδGE_comp_truncGEι (n : ℤ) :
    truncLTδGE n ≫ whiskerRight (truncGEι n) (shiftFunctor C (1 : ℤ)) = 0 := by aesop_cat

noncomputable def natTransTruncLTOfGE (a b : ℤ) (h : b ≤ a) :
    truncLT a ⟶ truncLT (hP := hP) b :=
  whiskerRight (TruncAux.triangleFunctorNatTransOfGE a b h) Triangle.π₃

noncomputable def natTransTruncGEOfGE (a b : ℤ) (h : b ≤ a) :
    truncGE a ⟶ truncGE (hP := hP) b :=
  whiskerRight (TruncAux.triangleFunctorNatTransOfGE a b h) Triangle.π₁

@[reassoc (attr := simp)]
lemma natTransTruncLTOfGE_π_app (a b : ℤ) (h : b ≤ a) (X : C):
    (truncLTπ a).app X ≫ (natTransTruncLTOfGE a b h).app X = (truncLTπ b).app X := by
  simpa only [TruncAux.triangleFunctorNatTransOfGE_app_hom₂,
    TruncAux.triangleFunctor_obj_obj₂, id_comp]
    using ((TruncAux.triangleFunctorNatTransOfGE a b h).app X).comm₂

@[reassoc (attr := simp)]
lemma natTransTruncLTOfGE_π (a b : ℤ) (h : b ≤ a) :
    truncLTπ a  ≫ natTransTruncLTOfGE a b h = truncLTπ (hP := hP) b := by aesop_cat

@[reassoc (attr := simp)]
lemma ι_natTransTruncGEOfGE_app (a b : ℤ) (h : b ≤ a) (X : C) :
    (natTransTruncGEOfGE a b h).app X ≫ (truncGEι b).app X = (truncGEι a).app X := by
  simpa only [TruncAux.triangleFunctorNatTransOfGE_app_hom₂,
    TruncAux.triangleFunctor_obj_obj₂, comp_id]
    using ((TruncAux.triangleFunctorNatTransOfGE a b h).app X).comm₁.symm

@[reassoc (attr := simp)]
lemma ι_natTransTruncGEOfGE (a b : ℤ) (h : b ≤ a) :
    natTransTruncGEOfGE (hP := hP) a b h ≫ truncGEι b = truncGEι a := by aesop_cat

@[reassoc]
lemma truncLTδGE_comp_natTransTruncGEOfGE_app (a b : ℤ) (h : b ≤ a) (X : C) :
  (truncLTδGE a).app X ≫ ((natTransTruncGEOfGE a b h).app X)⟦(1 :ℤ)⟧' =
    (natTransTruncLTOfGE a b h).app X ≫ (truncLTδGE b).app X :=
  ((TruncAux.triangleFunctorNatTransOfGE a b h).app X).comm₃

@[reassoc]
lemma truncLTδGE_comp_whiskerRight_natTransTruncGEOfGE (a b : ℤ) (h : b ≤ a) :
  truncLTδGE a ≫ whiskerRight (natTransTruncGEOfGE a b h) (shiftFunctor C (1 : ℤ)) =
    natTransTruncLTOfGE a b h ≫ truncLTδGE b := by
  ext X
  exact truncLTδGE_comp_natTransTruncGEOfGE_app a b h X

noncomputable def natTransTriangleGELTOfGE (a b : ℤ) (h : b ≤ a) :
    triangleGELT a ⟶ triangleGELT b (hP := hP) := by
  refine Triangle.functorHomMk' (natTransTruncGEOfGE a b h) (𝟙 _)
    ((natTransTruncLTOfGE a b h)) ?_ ?_ ?_
  · dsimp
    simp
  · dsimp
    simp
  · exact truncLTδGE_comp_whiskerRight_natTransTruncGEOfGE a b h

@[simp]
lemma natTransTriangleGELTOfGE_refl (a : ℤ) :
    natTransTriangleGELTOfGE (hP := hP) a a (by rfl) = 𝟙 _ :=
  TruncAux.triangleFunctorNatTransOfGE_refl a

set_option maxHeartbeats 400000 in
lemma natTransTriangleGELTOfGE_trans (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b):
    natTransTriangleGELTOfGE a b hab ≫ natTransTriangleGELTOfGE b c hbc =
      natTransTriangleGELTOfGE (hP := hP) a c (hbc.trans hab) :=
  TruncAux.triangleFunctorNatTransOfGE_trans a b c hab hbc

@[simp]
lemma natTransTruncLTOfGE_refl (a : ℤ) :
    natTransTruncLTOfGE (hP := hP) a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x => whiskerRight x (Triangle.π₃)) (natTransTriangleGELTOfGE_refl a)

set_option maxHeartbeats 400000 in
@[simp]
lemma natTransTruncLTOfGE_trans (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    natTransTruncLTOfGE a b hab ≫ natTransTruncLTOfGE b c hbc =
      natTransTruncLTOfGE (hP := hP) a c (hbc.trans hab) :=
  congr_arg (fun x => whiskerRight x Triangle.π₃)
    (natTransTriangleGELTOfGE_trans a b c hab hbc)

lemma natTransTruncLTOfGE_refl_app (a : ℤ) (X : C) :
    (natTransTruncLTOfGE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (natTransTruncLTOfGE_refl a) X

lemma natTransTruncLTOfGE_trans_app (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) (X : C) :
    (natTransTruncLTOfGE a b hab).app X ≫ (natTransTruncLTOfGE b c hbc).app X =
      (natTransTruncLTOfGE a c (hbc.trans hab)).app X :=
  congr_app (natTransTruncLTOfGE_trans a b c hab hbc) X

@[simp]
lemma natTransTruncGEOfGE_refl (a : ℤ) :
    natTransTruncGEOfGE (hP := hP) a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x => whiskerRight x (Triangle.π₁)) (natTransTriangleGELTOfGE_refl a)

set_option maxHeartbeats 400000 in
@[simp]
lemma natTransTruncGEOfGE_trans (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    natTransTruncGEOfGE a b hab ≫ natTransTruncGEOfGE b c hbc =
      natTransTruncGEOfGE (hP := hP) a c (hbc.trans hab) :=
  congr_arg (fun x => whiskerRight x Triangle.π₁)
    (natTransTriangleGELTOfGE_trans a b c hab hbc)

lemma natTransTruncGEOfGE_refl_app (a : ℤ) (X : C) :
    (natTransTruncGEOfGE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (natTransTruncGEOfGE_refl a) X

lemma natTransTruncGEOfGE_trans_app (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) (X : C) :
    (natTransTruncGEOfGE a b hab).app X ≫ (natTransTruncGEOfGE b c hbc).app X =
      (natTransTruncGEOfGE a c (hbc.trans hab)).app X :=
  congr_app (natTransTruncGEOfGE_trans a b c hab hbc) X

attribute [irreducible] truncLT truncGE truncLTπ truncGEι truncLTδGE
  natTransTruncLTOfGE natTransTruncGEOfGE

noncomputable def truncLE (n : ℤ) : C ⥤ C := truncLT (n+1)

instance (n : ℤ) : (truncLE (hP := hP) n).Additive := by
  dsimp only [truncLE]
  infer_instance

noncomputable instance (n : ℤ) : (truncLE (hP := hP) n).CommShift ℤ := by
  dsimp only [truncLE]
  infer_instance

instance (n : ℤ) (X : C) : hP.IsLE ((truncLE n).obj X) n := by
  have : hP.IsLE ((truncLE n).obj X) (n+1-1) := by
    dsimp [truncLE]
    infer_instance
  exact hP.isLE_of_LE _ (n+1-1) n (by linarith)

noncomputable def truncGT (n : ℤ) : C ⥤ C := truncGE (n+1)

instance (n : ℤ) : (truncGT (hP := hP) n).Additive := by
  dsimp only [truncGT]
  infer_instance

noncomputable instance (n : ℤ) : (truncGT (hP := hP) n).CommShift ℤ := by
  dsimp only [truncGT]
  infer_instance

instance (n : ℤ) (X : C) : hP.IsGE ((truncGT n).obj X) (n+1) := by
  dsimp [truncGT]
  infer_instance

instance (n : ℤ) (X : C) : hP.IsGE ((truncGT (n-1)).obj X) n :=
  hP.isGE_of_GE _ n (n-1+1) (by linarith)

noncomputable def truncLEIsoTruncLT (a b : ℤ) (h : a + 1 = b) : hP.truncLE a ≅ truncLT b :=
  eqToIso (congr_arg truncLT h)

noncomputable def truncGTIsoTruncGE (a b : ℤ) (h : a + 1 = b) : hP.truncGT a ≅ truncGE b :=
  eqToIso (congr_arg truncGE h)

noncomputable def truncLEπ (n : ℤ) : 𝟭 C ⟶ truncLE n:= truncLTπ (n + 1)

@[reassoc (attr := simp)]
lemma π_truncLEIsoTruncLT_hom (a b : ℤ) (h : a + 1 = b) :
    truncLEπ a ≫ (hP.truncLEIsoTruncLT a b h).hom = truncLTπ b := by
  subst h
  dsimp [truncLEIsoTruncLT, truncLEπ]
  rw [comp_id]

@[reassoc (attr := simp)]
lemma π_truncLEIsoTruncLT_hom_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (truncLEπ a).app X ≫ (truncLEIsoTruncLT a b h).hom.app X = (truncLTπ b).app X :=
  congr_app (π_truncLEIsoTruncLT_hom a b h) X

@[reassoc (attr := simp)]
lemma π_truncLEIsoTruncLT_inv (a b : ℤ) (h : a + 1 = b) :
    truncLTπ b ≫ (hP.truncLEIsoTruncLT a b h).inv = truncLEπ a := by
  subst h
  dsimp [truncLEIsoTruncLT, truncLEπ, truncLE]
  rw [comp_id]

@[reassoc (attr := simp)]
lemma π_truncLEIsoTruncLT_inv_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (truncLTπ b).app X ≫ (truncLEIsoTruncLT a b h).inv.app X = (truncLEπ a).app X :=
  congr_app (π_truncLEIsoTruncLT_inv a b h) X

noncomputable def truncGTι (n : ℤ) : truncGT n ⟶ 𝟭 C := truncGEι (n + 1)

@[reassoc (attr := simp)]
lemma truncGTIsoTruncGE_hom_ι (a b : ℤ) (h : a + 1 = b) :
    (hP.truncGTIsoTruncGE a b h).hom ≫ truncGEι b = truncGTι a := by
  subst h
  dsimp [truncGTIsoTruncGE, truncGTι]
  rw [id_comp]

@[reassoc (attr := simp)]
lemma truncGTIsoTruncGE_hom_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (truncGTIsoTruncGE a b h).hom.app X ≫ (truncGEι b).app X = (truncGTι a).app X :=
  congr_app (truncGTIsoTruncGE_hom_ι a b h) X

@[reassoc (attr := simp)]
lemma truncGTIsoTruncGE_inv_ι (a b : ℤ) (h : a + 1 = b) :
    (hP.truncGTIsoTruncGE a b h).inv ≫ truncGTι a = truncGEι b := by
  subst h
  dsimp [truncGTIsoTruncGE, truncGTι, truncGT]
  rw [id_comp]

@[reassoc (attr := simp)]
lemma truncGTIsoTruncGE_inv_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (truncGTIsoTruncGE a b h).inv.app X ≫ (truncGTι a).app X = (truncGEι b).app X :=
  congr_app (truncGTIsoTruncGE_inv_ι a b h) X

noncomputable def truncLEδGE (a b : ℤ) (h : a + 1 = b) :
    truncLE a ⟶ truncGE b ⋙ shiftFunctor C (1 : ℤ) :=
  (truncLEIsoTruncLT a b h).hom ≫ truncLTδGE b

@[simps!]
noncomputable def triangleGELE (a b : ℤ) (h : a + 1 = b) : C ⥤ Triangle C :=
  Triangle.functorMk (truncGEι b) (truncLEπ a) (truncLEδGE a b h)

noncomputable def triangleGELEIsoTriangleGELT (a b : ℤ) (h : a + 1 = b) :
    hP.triangleGELE a b h ≅ triangleGELT b := by
  refine Triangle.functorIsoMk _ _ (Iso.refl _) (Iso.refl _) (truncLEIsoTruncLT a b h) ?_ ?_ ?_
  · aesop_cat
  · aesop_cat
  · ext
    dsimp [truncLEδGE]
    simp only [assoc, id_comp, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, comp_id]

lemma triangleGELE_distinguished (a b : ℤ) (h : a + 1 = b) (X : C) :
    (triangleGELE a b h).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (triangleGELT_distinguished b X) _
    ((triangleGELEIsoTriangleGELT a b h).app X)

noncomputable def truncLEδGT (n : ℤ) :
    truncLE n ⟶ truncGT n ⋙ shiftFunctor C (1 : ℤ) :=
  truncLEδGE n (n+1) (by linarith) ≫ whiskerRight (truncGTIsoTruncGE n (n+1) rfl).inv
  (shiftFunctor C 1)

@[simps!]
noncomputable def triangleGTLE (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (truncGTι n) (truncLEπ n) (truncLEδGT n)

noncomputable def triangleGTLEIsoTriangleGELE (a b : ℤ) (h : a + 1 = b) :
    hP.triangleGTLE a ≅ triangleGELE a b h := by
  refine Triangle.functorIsoMk _ _ (truncGTIsoTruncGE a b h) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · aesop_cat
  · aesop_cat
  · ext
    dsimp [truncLEδGT]
    subst h
    simp only [assoc, id_comp, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, comp_id]

lemma triangleGTLE_distinguished (n : ℤ) (X : C) :
    (triangleGTLE n).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (triangleGELE_distinguished n (n+1) rfl X) _
    ((triangleGTLEIsoTriangleGELE n (n+1) rfl).app X)

variable (n : ℤ)
#synth (truncLE n).CommShift ℤ (C := C)

@[simp]
lemma truncLECommShift.comm (X : C) (n a : ℤ) :
    ((hP.truncLEπ n).app X)⟦a⟧' = (truncLEπ n).app (X⟦a⟧) ≫
    ((truncLE n).commShiftIso a).hom.app X := by
  set ex := TruncAux.triangleFunctorIsoShift_exists n X a
  set e := ex.choose
  set e' := e.inv.hom₃
  simp only [Triangle.shiftFunctor_eq, Triangle.shiftFunctor_obj, TruncAux.triangleFunctor_obj_obj₂,
    Functor.comp_obj, Triangle.mk_obj₃] at e'
  have : ((truncLE n).commShiftIso a).hom.app X = e' := sorry

-- TODO: similar lemmas for LT, GE, GT

lemma to_truncGE_obj_ext (n : ℤ) (X : C) {Y : C}
    (f₁ f₂ : X ⟶ (hP.truncGE n).obj Y) (h : f₁ ≫ (hP.truncGEι n).app Y =
    f₂ ≫ (hP.truncGEι n).app Y) [hP.IsGE X n] :
    f₁ = f₂ := by
  suffices ∀ (f : X ⟶ (hP.truncGE n).obj Y) (_ : f ≫ (hP.truncGEι n).app Y = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by rw [sub_comp, sub_eq_zero, h])]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _
    (hP.triangleGELT_distinguished n Y)) f hf
  have hg' := zero_of_isGE_of_isLE g (n-1) n (by linarith) inferInstance
    (by simp only [Triangle.invRotate_obj₁, Int.reduceNeg, triangleGELT_obj_obj₃]
        exact shift_isLE_of_isLE _ _ _)
  rw [hg, hg', zero_comp]

lemma to_truncGT_obj_ext (n : ℤ) (X : C) {Y : C}
    (f₁ f₂ : X ⟶ (hP.truncGT n).obj Y) (h : f₁ ≫ (hP.truncGTι n).app Y =
    f₂ ≫ (hP.truncGTι n).app Y) [hP.IsGE X (n+1)] :
    f₁ = f₂ := by
  rw [← cancel_mono ((hP.truncGTIsoTruncGE n (n+1) (by linarith)).hom.app Y)]
  apply to_truncGE_obj_ext
  simpa only [Functor.id_obj, assoc, truncGTIsoTruncGE_hom_ι_app] using h

lemma from_truncLE_obj_ext (n : ℤ) (Y : C) {X : C}
    (f₁ f₂ : (hP.truncLE n).obj X ⟶ Y) (h : (hP.truncLEπ n).app X ≫ f₁ =
    (hP.truncLEπ n).app X ≫ f₂) [hP.IsLE Y n] :
    f₁ = f₂ := by
  suffices ∀ (f : (hP.truncLE n).obj X ⟶ Y) (_ : (hP.truncLEπ n).app X ≫ f = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by rw [comp_sub, sub_eq_zero, h])]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (hP.triangleGTLE_distinguished n X) f hf
  have hg' := hP.zero_of_isGE_of_isLE g n (n+1) (by linarith)
    (by simp only [triangleGTLE_obj_obj₁]; exact shift_isGE_of_isGE _ _ _) inferInstance
  rw [hg, hg', comp_zero]

lemma from_truncLT_obj_ext (n : ℤ) (Y : C) {X : C}
    (f₁ f₂ : (hP.truncLT n).obj X ⟶ Y) (h : (hP.truncLTπ n).app X ≫ f₁ =
    (hP.truncLTπ n).app X ≫ f₂) [hP.IsLE Y (n-1)] :
    f₁ = f₂ := by
  rw [← cancel_epi ((hP.truncLEIsoTruncLT (n-1) n (by linarith)).hom.app X)]
  apply from_truncLE_obj_ext
  simpa only [Functor.id_obj, π_truncLEIsoTruncLT_hom_app_assoc] using h

lemma liftTruncGE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsGE X n] :
    ∃ (f' : X ⟶ (hP.truncGE n).obj Y), f = f' ≫ (hP.truncGEι n).app Y :=
  Triangle.coyoneda_exact₂ _ (hP.triangleGELT_distinguished n Y) f
    (hP.zero_of_isGE_of_isLE  _ (n - 1) n (by linarith)
    inferInstance (by dsimp; infer_instance))

noncomputable def liftTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsGE X n] :
    X ⟶ (hP.truncGE n).obj Y := (hP.liftTruncGE' f n).choose

@[reassoc (attr := simp)]
lemma liftTruncGE_ι {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsGE X n] :
    hP.liftTruncGE f n ≫ (hP.truncGEι n).app Y = f :=
  (hP.liftTruncGE' f n).choose_spec.symm

noncomputable def liftTruncGT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₁ + 1 = n₀) [hP.IsGE X n₀] :
    X ⟶ (hP.truncGT n₁).obj Y :=
  hP.liftTruncGE f n₀ ≫ (hP.truncGTIsoTruncGE _ _ h).inv.app Y

@[reassoc (attr := simp)]
lemma liftTruncGT_ι {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₁ + 1 = n₀) [hP.IsGE X n₀] :
    hP.liftTruncGT f n₀ n₁ h ≫ (hP.truncGTι n₁).app Y = f := by
  dsimp only [liftTruncGT]
  simp only [Functor.id_obj, assoc, truncGTIsoTruncGE_inv_ι_app, liftTruncGE_ι]

lemma descTruncLE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsLE Y n] :
  ∃ (f' : (hP.truncLE n).obj X ⟶ Y), f = (hP.truncLEπ n).app X ≫ f' :=
  Triangle.yoneda_exact₂ _ (hP.triangleGTLE_distinguished n X) f
    (hP.zero_of_isGE_of_isLE _ n (n + 1) (by linarith) (by dsimp; infer_instance) inferInstance)

noncomputable def descTruncLE {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsLE Y n] :
    (hP.truncLE n).obj X ⟶ Y := (hP.descTruncLE' f n).choose

@[reassoc (attr := simp)]
lemma π_descTruncLE {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsLE Y n] :
    (hP.truncLEπ n).app X ≫ hP.descTruncLE f n  = f :=
  (hP.descTruncLE' f n).choose_spec.symm

noncomputable def descTruncLT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [hP.IsLE Y n₀] :
    (hP.truncLT n₁).obj X ⟶ Y := (hP.truncLEIsoTruncLT _ _ h).inv.app X ≫ hP.descTruncLE f n₀

@[reassoc (attr := simp)]
lemma π_descTruncLT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [hP.IsLE Y n₀] :
    (hP.truncLTπ n₁).app X ≫ hP.descTruncLT f n₀ n₁ h  = f := by
  dsimp only [descTruncLT]
  simp only [Functor.id_obj, π_truncLEIsoTruncLT_inv_app_assoc, π_descTruncLE]

variable [IsTriangulated C]

noncomputable instance (n : ℤ) : (hP.truncLE n).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨Z₁, Z₃, f, g, h, v₁, w₁, u₃, v₃, w₃, hZ, hGT, hLE, comm₁₂, comm₂₃, _, comm₃₁₂,
      _⟩ := NineGrid' (hP.triangleGTLE_distinguished n T.obj₁) (hP.triangleGTLE_distinguished n
      T.obj₂) ((hP.truncGT n).map T.mor₁) T.mor₁ (by simp only [triangleGTLE_obj_obj₁,
      triangleGTLE_obj_obj₂, triangleGTLE_obj_mor₁, NatTrans.naturality, Functor.id_obj,
      Functor.id_map]) T.mor₂ T.mor₃ hT
    have ex := triangle_iso_exists n (n + 1) (by linarith) _ _ hZ
      (hP.triangleGTLE_distinguished n T.obj₃) (Iso.refl _)
      (by simp only [Triangle.mk_obj₁]
          refine hP.isGE₃ _ hGT ?_ ?_ (n := n + 1)
          simp only [triangleGTLE_obj_obj₁, Triangle.mk_obj₁]; infer_instance
          simp only [triangleGTLE_obj_obj₁, Triangle.mk_obj₂]; infer_instance)
      (by simp only [Triangle.mk_obj₃]
          refine hP.isLE₃ _ hLE ?_ ?_ (n := n)
          simp only [triangleGTLE_obj_obj₃, Triangle.mk_obj₁]; infer_instance
          simp only [triangleGTLE_obj_obj₃, Triangle.mk_obj₂]; infer_instance)
      (by simp only [triangleGTLE_obj_obj₁]; infer_instance)
      (by simp only [triangleGTLE_obj_obj₃]; infer_instance)
    set eZ := ex.choose
    set e : Triangle.mk u₃ v₃ w₃ ≅ (truncLE n).mapTriangle.obj T := by
      refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Triangle.π₃.mapIso eZ) ?_ ?_ ?_
      · simp only [triangleGTLE_obj_obj₃, Triangle.mk_obj₁, Functor.mapTriangle_obj,
        Triangle.mk_obj₂, Triangle.mk_mor₁, Iso.refl_hom, comp_id, id_comp]
        have : IsLE ((triangleGTLE n).obj T.obj₂).obj₃ n := by
          simp only [triangleGTLE_obj_obj₃]; infer_instance
        refine from_truncLE_obj_ext n _ _ _ ?_
        simp only [Functor.id_obj, triangleGTLE_obj_obj₃]
        have := comm₁₂.2.1
        simp only [triangleGTLE_obj_obj₂, triangleGTLE_obj_obj₃, triangleGTLE_obj_mor₂] at this
        rw [this]
        exact (truncLEπ n).naturality T.mor₁
      · simp only [triangleGTLE_obj_obj₃, Triangle.mk_obj₂, Functor.mapTriangle_obj,
        Triangle.mk_obj₃, Triangle.mk_mor₂, Functor.mapIso_hom, Triangle.π₃_map, Iso.refl_hom,
        id_comp]
        refine from_truncLE_obj_ext n _ _ _ ?_
        have := comm₂₃.2.1
        simp only [triangleGTLE_obj_obj₂, Triangle.mk_obj₃, triangleGTLE_obj_obj₃,
        triangleGTLE_obj_mor₂, Triangle.mk_obj₂, Triangle.mk_mor₂] at this
        rw [← assoc, this]
        have := eZ.hom.comm₂
        simp only [Triangle.mk_obj₂, triangleGTLE_obj_obj₃, Triangle.mk_obj₃, Triangle.mk_mor₂,
        triangleGTLE_obj_obj₂, triangleGTLE_obj_mor₂] at this
        rw [assoc, this]
        have := (truncLEπ n).naturality T.mor₂
        simp only [Functor.id_obj, Functor.id_map] at this
        rw [← this, ex.choose_spec]
        simp only [Functor.id_obj, Triangle.mk_obj₂, triangleGTLE_obj_obj₂, Iso.refl_hom, id_comp]
      · simp only [triangleGTLE_obj_obj₃, Triangle.mk_obj₃, Functor.mapTriangle_obj,
        Triangle.mk_obj₁, Triangle.mk_mor₃, Iso.refl_hom, Functor.map_id, comp_id, Functor.mapIso_hom,
        Triangle.π₃_map]
        rw [← cancel_epi eZ.inv.hom₃]
        have : IsLE ((((triangleGTLE n).obj T.obj₁).obj₃)⟦(1 : ℤ)⟧) n := by
          simp only [triangleGTLE_obj_obj₃]
          exact shift_isLE_of_isLE _ _ _
        refine from_truncLE_obj_ext n _ _ _ ?_
        have := eZ.inv.comm₂
        simp only [triangleGTLE_obj_obj₂, Triangle.mk_obj₃, triangleGTLE_obj_obj₃,
        triangleGTLE_obj_mor₂, Triangle.mk_obj₂, Triangle.mk_mor₂] at this
        rw [← assoc, this]
        rw [← cancel_epi eZ.hom.hom₂]
        conv_rhs => rw [ex.choose_spec]
        simp only [Triangle.mk_obj₂, triangleGTLE_obj_obj₃, triangleGTLE_obj_obj₂, Functor.id_obj,
        Triangle.mk_obj₃, assoc, Iso.hom_inv_id_triangle_hom₂_assoc, Iso.refl_hom,
        Iso.inv_hom_id_triangle_hom₃_assoc, id_comp]
        have := (truncLEπ n).naturality T.mor₃
        simp only [Functor.id_obj, Functor.id_map] at this
        rw [← assoc, ← this, ← comm₃₁₂]
        simp only [triangleGTLE_obj_obj₂, triangleGTLE_obj_obj₃, triangleGTLE_obj_mor₂, assoc]
        rw [truncLECommShift.comm]
    exact isomorphic_distinguished _ hLE _ e.symm

#exit

namespace TruncLTt

noncomputable def obj : ℤt → C ⥤ C
  | some none => 0
  | some (some a) => t.truncLT a
  | none => 𝟭 C

noncomputable def map : ∀ {x y : ℤt}, (x ⟶ y) → (obj t x ⟶ obj t y)
  | some none, some none => fun _ => 𝟙 _
  | some none, some (some b) => fun _ => 0
  | some none, none => fun _ => 0
  | some (some a), some none  => fun _ => 0
  | some (some a), some (some b) =>
      fun hab => t.natTransTruncLTOfLE a b (by simpa using (leOfHom hab))
  | some (some a), none => fun _ => t.truncLTι a
  | none, some none  => fun _ => 0
  | none, some (some b) => fun _ => 0
  | none, none => fun _ => 𝟙 _

end TruncLTt

noncomputable def truncLTt : ℤt ⥤ C ⥤ C where
  obj := TruncLTt.obj t
  map φ := TruncLTt.map t φ
  map_id := by
    rintro (_|_|_)
    · rfl
    · rfl
    · dsimp [TruncLTt.map]
      rw [t.natTransTruncLTOfLE_refl]
      rfl
  map_comp {a b c} hab hbc := by
    replace hab := leOfHom hab
    replace hbc := leOfHom hbc
    obtain (_|_|_) := a <;> obtain (_|_|_) := b <;> obtain (_|_|_) := c
    all_goals simp (config := {failIfUnchanged := false}) at hbc hab <;>
      dsimp [TruncLTt.map] <;> simp

@[simp]
lemma truncLTt_obj_top : t.truncLTt.obj ⊤ = 𝟭 _ := rfl

@[simp]
lemma truncLTt_obj_bot : t.truncLTt.obj ⊥ = 0 := rfl

@[simp]
lemma truncLTt_obj_mk (n : ℤ) : t.truncLTt.obj (ℤt.mk n) = t.truncLT n := rfl

@[simp]
lemma truncLTt_map_eq_truncLTι (n : ℤ) :
    t.truncLTt.map (homOfLE (show ℤt.mk n ≤ ⊤ by simp)) = t.truncLTι n := rfl

namespace TruncGEt

noncomputable def obj : ℤt → C ⥤ C
  | some none => 𝟭 C
  | some (some a) => t.truncGE a
  | none => 0

noncomputable def map : ∀ {x y : ℤt}, (x ⟶ y) → (obj t x ⟶ obj t y)
  | some none, some none => fun _ => 𝟙 _
  | some none, some (some b) => fun _ => t.truncGEπ b
  | some none, none => fun _ => 0
  | some (some a), some none  => fun _ => 0
  | some (some a), some (some b) =>
      fun hab => t.natTransTruncGEOfLE a b (by simpa using (leOfHom hab))
  | some (some a), none => fun _ => 0
  | none, some none  => fun _ => 0
  | none, some (some b) => fun _ => 0
  | none, none => fun _ => 𝟙 _

end TruncGEt

noncomputable def truncGEt : ℤt ⥤ C ⥤ C where
  obj := TruncGEt.obj t
  map φ := TruncGEt.map t φ
  map_id := by
    rintro (_|a|_)
    · rfl
    · rfl
    · dsimp [TruncGEt.map]
      rw [natTransTruncGEOfLE_refl]
      rfl
  map_comp {a b c} hab hbc := by
    replace hab := leOfHom hab
    replace hbc := leOfHom hbc
    obtain (_|_|_) := a <;> obtain (_|_|_) := b <;> obtain (_|_|_) := c
    all_goals simp (config := {failIfUnchanged := false}) at hbc hab <;>
      dsimp [TruncGEt.map] <;> simp

@[simp]
lemma truncGEt_obj_bot :
    t.truncGEt.obj ⊥ = 𝟭 _ := rfl

@[simp]
lemma truncGEt_obj_top :
    t.truncGEt.obj ⊤ = 0 := rfl

@[simp]
lemma truncGEt_obj_mk (n : ℤ) : t.truncGEt.obj (ℤt.mk n) = t.truncGE n := rfl

namespace TruncGEtδLTt

noncomputable def app : ∀ (a : ℤt), t.truncGEt.obj a ⟶ t.truncLTt.obj a ⋙ shiftFunctor C (1 : ℤ)
  | some none => 0
  | some (some a) => t.truncGEδLT a
  | none => 0

end TruncGEtδLTt

noncomputable def truncGEtδLTt :
    t.truncGEt ⟶ t.truncLTt ⋙ ((whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ))) where
  app a := TruncGEtδLTt.app t a
  naturality {a b} hab := by
    replace hab := leOfHom hab
    obtain (_|_|a) := a
    · apply IsZero.eq_of_src
      exact isZero_zero _
    all_goals obtain (_|_|b) := b <;> simp (config := {failIfUnchanged := false}) at hab <;>
      dsimp [TruncGEtδLTt.app, truncGEt, truncLTt, TruncGEt.map, TruncLTt.map] <;>
      simp [t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE]

@[simp]
lemma truncGEtδLTt_mk (n : ℤ) :
    t.truncGEtδLTt.app (ℤt.mk n) = t.truncGEδLT n := rfl

@[simps]
noncomputable def abstractSpectralObject : SpectralObject.AbstractSpectralObject C ℤt where
  truncLT := t.truncLTt
  truncGE := t.truncGEt
  truncLTObjTopIso' := Iso.refl _
  truncGEObjBotIso' := Iso.refl _
  truncGEδLT := t.truncGEtδLTt


namespace AbstractSpectralObject

open SpectralObject

@[simp]
lemma truncGELT_eq (g : Arrow ℤt) :
  (abstractSpectralObject t).truncGELT.obj g =
    t.truncLTt.obj g.right ⋙ t.truncGEt.obj g.left := rfl

noncomputable def isZero_truncGE_obj_top_obj (X : C) :
    IsZero ((t.abstractSpectralObject.truncGE.obj ⊤).obj X) :=
  IsZero.obj (isZero_zero _) _

noncomputable def isZero_truncLT_obj_bot_obj (X : C) :
    IsZero ((t.abstractSpectralObject.truncLT.obj ⊥).obj X) :=
  IsZero.obj (isZero_zero _) _

@[simp]
lemma truncLEι_mk (n : ℤ) :
    t.abstractSpectralObject.truncLTι (ℤt.mk n) = t.truncLTι n :=
  comp_id _

@[simp]
lemma truncGEπ_mk (n : ℤ) :
    t.abstractSpectralObject.truncGEπ (ℤt.mk n) = t.truncGEπ n :=
  id_comp _

@[simp]
lemma truncGEδLT_mk (n : ℤ) :
    t.abstractSpectralObject.truncGEδLT.app (ℤt.mk n) =
      t.truncGEδLT n := rfl

noncomputable def triangleLTGEIso (n : ℤ) (X : C) :
    (t.abstractSpectralObject.triangleLTGE.obj (ℤt.mk n)).obj X ≅
      (t.triangleLTGE n).obj X := by
  refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _ _
  all_goals aesop_cat

@[simp]
lemma truncLTObjTopIso : t.abstractSpectralObject.truncLTObjTopIso = Iso.refl _ := rfl

@[simp]
lemma truncGEObjBotIso : t.abstractSpectralObject.truncGEObjBotIso = Iso.refl _ := rfl

@[simp]
lemma truncLTι_top_app (X : C) :
    (t.abstractSpectralObject.truncLTι ⊤).app X = 𝟙 X := by
  dsimp [AbstractSpectralObject.truncLTι]
  erw [Functor.map_id]
  simp only [truncLTt_obj_top, NatTrans.id_app, Functor.id_obj, comp_id]

@[simp]
lemma truncGEπ_bot_app (X : C) :
    (t.abstractSpectralObject.truncGEπ ⊥).app X = 𝟙 X := by
  dsimp [AbstractSpectralObject.truncGEπ]
  erw [Functor.map_id]
  simp only [truncGEt_obj_bot, NatTrans.id_app, Functor.id_obj, comp_id]

noncomputable def triangleLTGETopIso (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj ⊤).obj X ≅
    Pretriangulated.contractibleTriangle X := by
  refine' Triangle.isoMk _ _ (((abstractSpectralObject t).truncLTObjTopIso).app X)
    (Iso.refl _) (isZero_truncLT_obj_bot_obj t X).isoZero _ _ _
  · dsimp
    rw [truncLTι_top_app]
  · exact IsZero.eq_of_tgt (isZero_zero _) _ _
  · refine' IsZero.eq_of_src _ _ _
    exact IsZero.obj (isZero_zero _) _

noncomputable def triangleLTGEBotIso (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj ⊥).obj X ≅
    (Pretriangulated.contractibleTriangle X).invRotate := by
  refine' Triangle.isoMk _ _ ((isZero_truncLT_obj_bot_obj t X).isoZero ≪≫
    (shiftFunctor C (-1 : ℤ)).mapZeroObject.symm)
    (((abstractSpectralObject t).truncLTObjTopIso).app X) (Iso.refl _) _ _ _
  · apply IsZero.eq_of_src
    apply isZero_truncLT_obj_bot_obj
  · dsimp
    rw [truncGEπ_bot_app]
  · apply IsZero.eq_of_tgt _
    dsimp
    rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← Functor.map_id, id_zero,
      Functor.map_zero, Functor.map_zero]

lemma distinguished (n : ℤt) (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj n).obj X ∈ distTriang C := by
  obtain (_|_|n) := n
  · exact isomorphic_distinguished _ (contractible_distinguished X) _
      (triangleLTGETopIso t X)
  · exact isomorphic_distinguished _
      (inv_rot_of_distTriang _ (contractible_distinguished X)) _
      (triangleLTGEBotIso t X)
  · exact isomorphic_distinguished _ (t.triangleLTGE_distinguished n X) _
      (triangleLTGEIso t n X)

end AbstractSpectralObject

lemma isZero_truncLE_obj_zero (n : ℤ) : IsZero ((t.truncLE n).obj 0) := by
  let δ := (t.truncGEδLE n (n+1) rfl).app 0
  have : IsIso δ := by
    have h := (t.triangleLEGE_distinguished n (n+1) rfl 0)
    exact (Triangle.isZero₂_iff_isIso₃ _ h).1
      ((Triangle.isZero₂_iff _ (t.triangleLEGE_distinguished n (n+1) rfl 0)).2
        ⟨(isZero_zero C).eq_of_tgt _ _, (isZero_zero C).eq_of_src _ _⟩)
  have : t.IsLE ((t.truncLE n ⋙ shiftFunctor C (1 : ℤ)).obj 0) (n-1) :=
    t.isLE_shift _ n 1 (n-1) (by linarith)
  have hδ := t.zero_of_isLE_of_isGE δ (n-1) (n+1) (by linarith)
    (t.isLE_of_iso (asIso δ).symm _) (t.isGE_of_iso (asIso δ) _)
  rw [IsZero.iff_id_eq_zero]
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [Functor.map_id, Functor.map_zero, ← cancel_epi δ, comp_zero, hδ, zero_comp]

lemma isZero_truncGE_obj_zero (n : ℤ) : IsZero ((t.truncGE n).obj 0) := by
  apply (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLEGE_distinguished (n-1) n (by linarith) 0)).2
  exact ⟨⟨0, (isZero_truncLE_obj_zero t (n-1)).eq_of_src _ _, (isZero_zero _).eq_of_src _ _⟩⟩

instance (n : ℤ) : t.IsLE (0 : C) n := t.isLE_of_iso (t.isZero_truncLE_obj_zero n).isoZero n
instance (n : ℤ) : t.IsGE (0 : C) n := t.isGE_of_iso (t.isZero_truncGE_obj_zero n).isoZero n

lemma isLE_of_isZero (X : C) (hX : IsZero X) (n : ℤ) : t.IsLE X n :=
  t.isLE_of_iso hX.isoZero.symm n

lemma isGE_of_isZero (X : C) (hX : IsZero X) (n : ℤ) : t.IsGE X n :=
  t.isGE_of_iso hX.isoZero.symm n

lemma isLE_iff_isIso_truncLEι_app (n : ℤ) (X : C) :
    t.IsLE X n ↔ IsIso ((t.truncLEι n).app X) := by
  constructor
  · intro
    obtain ⟨e, he⟩ := t.triangle_iso_exists n (n+1) (by linarith) _ _
      (contractible_distinguished X) (t.triangleLEGT_distinguished n X)
      (Iso.refl X) (by dsimp ; infer_instance)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    dsimp at he
    have : (truncLEι t n).app X = e.inv.hom₁ := by
      have he' : e.inv.hom₂ = 𝟙 X := by
        rw [← cancel_mono e.hom.hom₂, ← comp_hom₂, e.inv_hom_id, he]
        dsimp
        rw [id_comp]
      simpa [he'] using e.inv.comm₁
    rw [this]
    infer_instance
  · intro
    exact t.isLE_of_iso (asIso ((truncLEι t n).app X)) n

lemma isLE_iff_isIso_truncLTι_app (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsIso (((t.truncLTι n₁)).app X) := by
  rw [isLE_iff_isIso_truncLEι_app]
  subst hn₁
  rfl

lemma isGE_iff_isIso_truncGEπ_app (n : ℤ) (X : C) :
    t.IsGE X n ↔ IsIso ((t.truncGEπ n).app X) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := t.triangle_iso_exists (n-1) n (by linarith) _ _
      (inv_rot_of_distTriang _ (contractible_distinguished X))
      (t.triangleLTGE_distinguished n X) (Iso.refl X)
      (t.isLE_of_iso (shiftFunctor C (-1 : ℤ)).mapZeroObject.symm _)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    dsimp at he
    have : (truncGEπ t n).app X = e.hom.hom₃ := by
      have eq := e.hom.comm₂
      dsimp at eq
      rw [← cancel_epi e.hom.hom₂, ← eq, he]
    rw [this]
    infer_instance
  · intro
    exact t.isGE_of_iso (asIso ((truncGEπ t n).app X)).symm n

instance (X : C) (n : ℤ) [t.IsLE X n] : IsIso ((t.truncLEι n).app X) := by
  rw [← isLE_iff_isIso_truncLEι_app ]
  infer_instance

instance (X : C) (n : ℤ) [t.IsGE X n] : IsIso ((t.truncGEπ n).app X) := by
  rw [← isGE_iff_isIso_truncGEπ_app ]
  infer_instance

lemma isLE_iff_isZero_truncGT_obj (n : ℤ) (X : C) :
    t.IsLE X n ↔ IsZero ((t.truncGT n).obj X) := by
  rw [t.isLE_iff_isIso_truncLEι_app n X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLEGT_distinguished n X)).symm

lemma isGE_iff_isZero_truncLT_obj (n : ℤ) (X : C) :
    t.IsGE X n ↔ IsZero ((t.truncLT n).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (t.triangleLTGE_distinguished n X)).symm

lemma isLE_iff_isZero_truncGE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsZero ((t.truncGE n₁).obj X) := by
  rw [t.isLE_iff_isIso_truncLEι_app n₀ X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLEGE_distinguished n₀ n₁ h X)).symm

lemma isGE_iff_isZero_truncLE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ IsZero ((t.truncLE n₀).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n₁ X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (t.triangleLEGE_distinguished n₀ n₁ h X)).symm

lemma isZero_truncGE_obj_of_isLE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) [t.IsLE X n₀] :
    IsZero ((t.truncGE n₁).obj X) := by
  rw [← t.isLE_iff_isZero_truncGE_obj _ _ h X]
  infer_instance

lemma isZero_truncLE_obj_of_isGE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) [t.IsGE X n₁] :
    IsZero ((t.truncLE n₀).obj X) := by
  rw [← t.isGE_iff_isZero_truncLE_obj _ _ h X]
  infer_instance

lemma from_truncGE_obj_ext (n : ℤ) (X : C) {Y : C}
    (f₁ f₂ : (t.truncGE n).obj X ⟶ Y) (h : (t.truncGEπ n).app X ≫ f₁ = (t.truncGEπ n).app X ≫ f₂)
    [t.IsGE Y n] :
    f₁ = f₂ := by
  suffices ∀ (f : (t.truncGE n).obj X ⟶ Y) (_ : (t.truncGEπ n).app X ≫ f = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by rw [comp_sub, sub_eq_zero, h])]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _
    (t.triangleLTGE_distinguished n X) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n-2) n (by linarith)
    (by dsimp ; exact t.isLE_shift _ (n-1) 1 (n-2) (by linarith)) (by infer_instance)
  rw [hg, hg', comp_zero]

lemma to_truncLE_obj_ext (n : ℤ) (Y : C) {X : C}
    (f₁ f₂ : Y ⟶ (t.truncLE n).obj X) (h : f₁ ≫ (t.truncLEι n).app X = f₂ ≫ (t.truncLEι n).app X)
    [t.IsLE Y n] :
    f₁ = f₂ := by
  suffices ∀ (f : Y ⟶ (t.truncLE n).obj X) (_ : f ≫ (t.truncLEι n).app X = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by rw [sub_comp, sub_eq_zero, h])]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _
    (t.triangleLEGT_distinguished n X)) f hf
  have hg' := t.zero_of_isLE_of_isGE g n (n+2) (by linarith) (by infer_instance)
    (by dsimp ; apply (t.isGE_shift _ (n+1) (-1) (n+2) (by linarith)))
  rw [hg, hg', zero_comp]

lemma to_truncLT_obj_ext (n : ℤ) (Y : C) {X : C}
    (f₁ f₂ : Y ⟶ (t.truncLT n).obj X) (h : f₁ ≫ (t.truncLTι n).app X = f₂ ≫ (t.truncLTι n).app X)
    [t.IsLE Y (n-1)] :
    f₁ = f₂ := by
  rw [← cancel_mono ((t.truncLEIsoTruncLT (n-1) n (by linarith)).inv.app X)]
  apply to_truncLE_obj_ext
  simpa only [Functor.id_obj, assoc, truncLEIsoTruncLT_inv_ι_app] using h

lemma liftTruncLE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    ∃ (f' : X ⟶ (t.truncLE n).obj Y), f = f' ≫ (t.truncLEι n).app Y :=
  Triangle.coyoneda_exact₂ _ (t.triangleLEGT_distinguished n Y) f
    (t.zero_of_isLE_of_isGE  _ n (n+1) (by linarith) inferInstance (by dsimp ; infer_instance))

noncomputable def liftTruncLE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    X ⟶ (t.truncLE n).obj Y := (t.liftTruncLE' f n).choose

@[reassoc (attr := simp)]
lemma liftTruncLE_ι {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    t.liftTruncLE f n ≫ (t.truncLEι n).app Y = f :=
  (t.liftTruncLE' f n).choose_spec.symm

noncomputable def liftTruncLT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsLE X n₀] :
    X ⟶ (t.truncLT n₁).obj Y :=
  t.liftTruncLE f n₀ ≫ (t.truncLEIsoTruncLT _ _ h).hom.app Y

@[reassoc (attr := simp)]
lemma liftTruncLT_ι {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsLE X n₀] :
    t.liftTruncLT f n₀ n₁ h ≫ (t.truncLTι n₁).app Y = f := by
  dsimp only [liftTruncLT]
  simp only [Functor.id_obj, assoc, truncLEIsoTruncLT_hom_ι_app, liftTruncLE_ι]

lemma descTruncGE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
  ∃ (f' : (t.truncGE n).obj X ⟶ Y), f = (t.truncGEπ n).app X ≫ f' :=
  Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished n X) f
    (t.zero_of_isLE_of_isGE _ (n-1)  n (by linarith) (by dsimp ; infer_instance) inferInstance)

noncomputable def descTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
    (t.truncGE n).obj X ⟶ Y := (t.descTruncGE' f n).choose

@[reassoc (attr := simp)]
lemma π_descTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
    (t.truncGEπ n).app X ≫ t.descTruncGE f n  = f :=
  (t.descTruncGE' f n).choose_spec.symm

lemma isLE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ ∀ (Y : C) (f : X ⟶ Y) (_ : t.IsGE Y n₁), f = 0 := by
  constructor
  · intro _ Y f _
    exact t.zero f n₀ n₁ (by linarith)
  · intro hX
    rw [isLE_iff_isZero_truncGE_obj t n₀ n₁ h, IsZero.iff_id_eq_zero]
    apply t.from_truncGE_obj_ext n₁
    rw [comp_zero, comp_id]
    exact hX _ _ inferInstance

lemma isGE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ ∀ (Y : C) (f : Y ⟶ X) (_ : t.IsLE Y n₀), f = 0 := by
  constructor
  · intro _ Y f _
    exact t.zero f n₀ n₁ (by linarith)
  · intro hX
    rw [isGE_iff_isZero_truncLE_obj t n₀ n₁ h, IsZero.iff_id_eq_zero]
    apply t.to_truncLE_obj_ext n₀
    rw [zero_comp, id_comp]
    exact hX _ _ inferInstance

lemma isLE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : t.IsLE T.obj₁ n)
    (h₃ : t.IsLE T.obj₃ n) : t.IsLE T.obj₂ n := by
  rw [t.isLE_iff_orthogonal n (n+1) rfl]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.yoneda_exact₂ _ hT f
    (t.zero _ n (n+1) (by linarith) )
  rw [hf', t.zero f' n (n+1) (by linarith), comp_zero]

lemma isGE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : t.IsGE T.obj₁ n)
    (h₃ : t.IsGE T.obj₃ n) : t.IsGE T.obj₂ n := by
  rw [t.isGE_iff_orthogonal (n-1) n (by linarith)]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.coyoneda_exact₂ _ hT f (t.zero _ (n-1) n (by linarith))
  rw [hf', t.zero f' (n-1) n (by linarith), zero_comp]

def minus : Triangulated.Subcategory C := Triangulated.Subcategory.mk'
  (fun X => ∃ (n : ℤ), t.IsLE X n)
  ⟨0, inferInstance⟩
  (fun X n => by
    rintro ⟨i, hX⟩
    exact ⟨i - n, t.isLE_shift _ i n (i - n) (by linarith)⟩)
  (fun T hT => by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨max i₁ i₃, t.isLE₂ T hT _ (t.isLE_of_LE _ _ _ (le_max_left i₁ i₃))
      (t.isLE_of_LE _ _ _ (le_max_right i₁ i₃))⟩)

instance : ClosedUnderIsomorphisms t.minus.P := by
  dsimp only [minus]
  infer_instance

def plus : Triangulated.Subcategory C := Triangulated.Subcategory.mk'
  (fun X => ∃ (n : ℤ), t.IsGE X n)
  ⟨0, inferInstance⟩
  (fun X n => by
    rintro ⟨i, hX⟩
    exact ⟨i - n, t.isGE_shift _ i n (i - n) (by linarith)⟩)
  (fun T hT => by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨min i₁ i₃, t.isGE₂ T hT _ (t.isGE_of_GE _ _ _ (min_le_left i₁ i₃))
      (t.isGE_of_GE _ _ _ (min_le_right i₁ i₃))⟩)

instance : ClosedUnderIsomorphisms t.plus.P := by
  dsimp only [plus]
  infer_instance

def bounded : Triangulated.Subcategory C := t.plus.inter t.minus

instance : ClosedUnderIsomorphisms t.bounded.P := by
  dsimp [bounded]
  infer_instance

noncomputable def natTransTruncLEOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncLE a ⟶ t.truncLE b :=
  t.natTransTruncLTOfLE (a+1) (b+1) (by linarith)

@[reassoc (attr := simp)]
lemma natTransTruncLEOfLE_ι_app (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) (X : C) :
    (t.natTransTruncLEOfLE n₀ n₁ h).app X ≫ (t.truncLEι n₁).app X =
      (t.truncLEι n₀).app X :=
  t.natTransTruncLTOfLE_ι_app _ _ _ _

@[reassoc (attr := simp)]
lemma natTransTruncLEOfLE_ι (a b : ℤ) (h : a ≤ b) :
    t.natTransTruncLEOfLE a b h ≫ t.truncLEι b = t.truncLEι a := by aesop_cat

@[simp]
lemma natTransTruncLEOfLE_refl (a : ℤ) :
    t.natTransTruncLEOfLE a a (by rfl) = 𝟙 _ :=
  t.natTransTruncLTOfLE_refl _

@[simp]
lemma natTransTruncLEOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTruncLEOfLE a b hab ≫ t.natTransTruncLEOfLE b c hbc =
      t.natTransTruncLEOfLE a c (hab.trans hbc) :=
  t.natTransTruncLTOfLE_trans _ _ _ _ _

@[simp]
lemma natTransTruncLEOfLE_refl_app (a : ℤ) (X : C) :
    (t.natTransTruncLEOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncLEOfLE_refl a) X

@[reassoc (attr := simp)]
lemma natTransTruncLEOfLE_trans_app (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) (X : C) :
    (t.natTransTruncLEOfLE a b hab).app X ≫ (t.natTransTruncLEOfLE b c hbc).app X =
      (t.natTransTruncLEOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncLEOfLE_trans a b c hab hbc) X

lemma isIso_truncLTmap_iff {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    IsIso ((t.truncLT n).map f) ↔
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ ((t.truncLT n).obj X)⟦1⟧)
        (_ : Triangle.mk ((t.truncLTι n).app X ≫ f) g h ∈ distTriang _), t.IsGE Z n := by
  constructor
  · intro hf
    refine' ⟨(t.truncGE n).obj Y, (t.truncGEπ n).app Y,
      (t.truncGEδLT n).app Y ≫ (inv ((t.truncLT n).map f))⟦1⟧',
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n Y) _ _, inferInstance⟩
    refine' Triangle.isoMk _ _ (asIso ((t.truncLT n).map f)) (Iso.refl _) (Iso.refl _) _ _ _
    all_goals aesop_cat
  · rintro ⟨Z, g, h, mem, _⟩
    obtain ⟨e, he⟩ := t.triangle_iso_exists (n-1) n (by linarith)  _ _ mem
      (t.triangleLTGE_distinguished n Y) (Iso.refl _)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    suffices ((t.truncLT n).map f) = e.hom.hom₁ by
      rw [this]
      infer_instance
    apply to_truncLT_obj_ext
    refine' Eq.trans _ e.hom.comm₁
    aesop_cat

lemma isIso_truncLEmap_iff {X Y : C} (f : X ⟶ Y) (a b : ℤ) (h : a + 1 = b) :
    IsIso ((t.truncLE a).map f) ↔
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ ((t.truncLE a).obj X)⟦1⟧)
        (_ : Triangle.mk ((t.truncLEι a).app X ≫ f) g h ∈ distTriang _), t.IsGE Z b := by
  subst h
  apply isIso_truncLTmap_iff

lemma isIso_truncGEmap_iff {Y Z : C} (g : Y ⟶ Z) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    IsIso ((t.truncGE n₁).map g) ↔
      ∃ (X : C) (f : X ⟶ Y) (h : ((t.truncGE n₁).obj Z) ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f (g ≫ (t.truncGEπ n₁).app Z) h ∈ distTriang _), t.IsLE X n₀ := by
  constructor
  · intro hf
    refine' ⟨(t.truncLE n₀).obj Y, (t.truncLEι n₀).app Y,
      inv ((t.truncGE n₁).map g) ≫ (t.truncGEδLE n₀ n₁ hn₁).app Y,
      isomorphic_distinguished _ (t.triangleLEGE_distinguished n₀ n₁ hn₁ Y) _ _,
      inferInstance⟩
    refine' Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso ((t.truncGE n₁).map g)) _ _ _)
    · aesop_cat
    · dsimp
      rw [id_comp]
      exact ((t.truncGEπ n₁).naturality g).symm
    · aesop_cat
  · rintro ⟨X, f, h, mem, _⟩
    obtain ⟨e, he⟩ := t.triangle_iso_exists n₀ n₁ (by linarith) _ _
      (t.triangleLEGE_distinguished n₀ n₁ hn₁ Y) mem (Iso.refl _)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    suffices ((t.truncGE n₁).map g) = e.hom.hom₃ by
      rw [this]
      infer_instance
    apply from_truncGE_obj_ext
    refine' Eq.trans _ e.hom.comm₂.symm
    dsimp at he ⊢
    rw [he, id_comp]
    exact ((t.truncGEπ n₁).naturality g).symm

lemma isIso_truncGTmap_iff {Y Z : C} (g : Y ⟶ Z) (n : ℤ) :
    IsIso ((t.truncGT n).map g) ↔
      ∃ (X : C) (f : X ⟶ Y) (h : ((t.truncGT n).obj Z) ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f (g ≫ (t.truncGTπ n).app Z) h ∈ distTriang _), t.IsLE X n :=
  t.isIso_truncGEmap_iff g n (n+1) rfl

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncLE a).obj X) b := by
  by_cases h : a ≤ b
  · exact t.isLE_of_LE _ _ _ h
  · simp only [not_le] at h
    have : t.IsLE X a := t.isLE_of_LE X b a (by linarith)
    apply t.isLE_of_iso (show X ≅ _ from (asIso ((t.truncLEι a).app X)).symm)

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncLT a).obj X) b :=
  t.isLE_of_iso ((t.truncLEIsoTruncLT (a-1) a (by linarith)).app X) b

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncGE b).obj X) a := by
  by_cases h : a ≤ b
  · exact t.isGE_of_GE _ _ _ h
  · simp only [not_le] at h
    have : t.IsGE X b := t.isGE_of_GE X b a (by linarith)
    apply t.isGE_of_iso (show X ≅ _ from asIso ((t.truncGEπ b).app X))

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncGT b).obj X) a :=
  t.isGE_of_iso ((t.truncGTIsoTruncGE b (b+1) (by linarith)).symm.app X) a

noncomputable def truncGELT (a b : ℤ) : C ⥤ C := t.truncLT b ⋙ t.truncGE a

noncomputable def truncLTGE (a b : ℤ) : C ⥤ C := t.truncGE a ⋙ t.truncLT b

noncomputable def truncLEGE (a b : ℤ) : C ⥤ C := t.truncGE a ⋙ t.truncLE b

noncomputable def truncGELE (a b : ℤ) : C ⥤ C := t.truncLE b ⋙ t.truncGE a

noncomputable def truncGELEIsoTruncGELT (a b b' : ℤ) (hb' : b + 1 = b') :
    t.truncGELE a b ≅ t.truncGELT a b' :=
  isoWhiskerRight (t.truncLEIsoTruncLT b b' hb') _

/- Now, we need the octahedron axiom -/

variable [IsTriangulated C]

lemma isIso₁_truncLE_map_of_GE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₃ : t.IsGE T.obj₃ n₁) :
    IsIso ((t.truncLE n₀).map T.mor₁) := by
  rw [isIso_truncLEmap_iff _ _ _ _ h]
  obtain ⟨Z, g, k, mem⟩ := distinguished_cocone_triangle ((t.truncLEι n₀).app T.obj₁ ≫ T.mor₁)
  refine' ⟨_, _, _, mem, _⟩
  have H := someOctahedron rfl (t.triangleLEGE_distinguished n₀ n₁ h T.obj₁) hT mem
  exact t.isGE₂ _ H.mem n₁ (by dsimp ; infer_instance) (by dsimp ; infer_instance)

lemma isIso₁_truncLT_map_of_GE (T : Triangle C) (hT : T ∈ distTriang C)
    (n : ℤ) (h₃ : t.IsGE T.obj₃ n) : IsIso ((t.truncLT n).map T.mor₁) := by
  rw [← NatIso.isIso_map_iff (t.truncLEIsoTruncLT (n-1) n (by linarith))]
  exact t.isIso₁_truncLE_map_of_GE T hT (n-1) n (by linarith) h₃

lemma isIso₂_truncGE_map_of_LE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) :
    IsIso ((t.truncGE n₁).map T.mor₂) := by
  rw [isIso_truncGEmap_iff _ _ _ _ h]
  obtain ⟨X, f, k, mem⟩ := distinguished_cocone_triangle₁ (T.mor₂ ≫ (t.truncGEπ n₁).app T.obj₃)
  refine' ⟨_, _, _, mem, _⟩
  have H := someOctahedron rfl (rot_of_distTriang _ hT)
    (rot_of_distTriang _ (t.triangleLEGE_distinguished n₀ n₁ h T.obj₃))
    (rot_of_distTriang _ mem)
  have : t.IsLE (X⟦(1 : ℤ)⟧) (n₀-1) := t.isLE₂ _ H.mem (n₀-1)
    (t.isLE_shift T.obj₁ n₀ 1 (n₀-1) (by linarith))
    (t.isLE_shift ((t.truncLE n₀).obj T.obj₃) n₀ 1 (n₀-1) (by linarith))
  exact t.isLE_of_shift X n₀ 1 (n₀-1) (by linarith)

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncLE b).obj X) a := by
  rw [t.isGE_iff_isZero_truncLE_obj (a-1) a (by linarith)]
  have := t.isIso₁_truncLE_map_of_GE _ ((t.triangleLEGE_distinguished b (b+1) rfl X))
    (a-1) a (by linarith) (by dsimp ; infer_instance)
  dsimp at this
  exact IsZero.of_iso (t.isZero_truncLE_obj_of_isGE (a-1) a (by linarith) X)
    (asIso ((t.truncLE (a - 1)).map ((t.truncLEι b).app X)))

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncLT b).obj X) a :=
  t.isGE_of_iso ((t.truncLEIsoTruncLT (b-1) b (by linarith)).app X) a

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncGE a).obj X) b := by
  rw [t.isLE_iff_isZero_truncGE_obj b (b+1) rfl]
  have := t.isIso₂_truncGE_map_of_LE _ ((t.triangleLEGE_distinguished (a-1) a (by linarith) X))
    b (b+1) rfl (by dsimp ; infer_instance)
  dsimp at this
  exact IsZero.of_iso (t.isZero_truncGE_obj_of_isLE b (b+1) rfl X)
    (asIso ((t.truncGE (b+1)).map ((t.truncGEπ  a).app X))).symm

instance (X : C) (a b : ℤ) : t.IsGE ((t.truncGELE a b).obj X) a := by
  dsimp [truncGELE]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsLE ((t.truncGELE a b).obj X) b := by
  dsimp [truncGELE]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsGE ((t.truncGELT a b).obj X) a := by
  dsimp [truncGELT]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsLE ((t.truncGELT a b).obj X) (b-1) := by
  dsimp [truncGELT]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsGE ((t.truncLTGE a b).obj X) a := by
  dsimp [truncLTGE]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsLE ((t.truncLTGE a b).obj X) (b-1) := by
  dsimp [truncLTGE]
  infer_instance

instance (a b : ℤ) : (t.truncGELT a b).Additive := by
  dsimp only [truncGELT]
  infer_instance

instance (a b : ℤ) : (t.truncGELE a b).Additive := by
  dsimp only [truncGELE]
  infer_instance

instance (i : ℤt) : (t.truncGEt.obj i).Additive := by
  obtain (rfl|⟨i, rfl⟩|rfl) := i.three_cases
  · dsimp
    infer_instance
  · dsimp
    infer_instance
  · constructor
    aesop_cat

instance (i : ℤt) : (t.truncLTt.obj i).Additive := by
  obtain (rfl|⟨i, rfl⟩|rfl) := i.three_cases
  · constructor
    dsimp
    aesop_cat
  · dsimp
    infer_instance
  · dsimp
    infer_instance

lemma isZero_truncLTt_obj_obj (X : C) (n : ℤ) [t.IsGE X n] (j : ℤt) (hj : j ≤ ℤt.mk n) :
    IsZero ((t.truncLTt.obj j).obj X) := by
  obtain (rfl|⟨j, rfl⟩|rfl) := j.three_cases
  · apply Functor.zero_obj
  · simp at hj
    dsimp
    rw [← t.isGE_iff_isZero_truncLT_obj]
    exact t.isGE_of_GE  _ _ _ hj
  · simp at hj

lemma isZero_truncGEt_obj_obj (X : C) (n : ℤ) [t.IsLE X n] (j : ℤt) (hj : ℤt.mk n < j) :
    IsZero ((t.truncGEt.obj j).obj X) := by
  obtain (rfl|⟨j, rfl⟩|rfl) := j.three_cases
  · simp at hj
  · simp at hj
    dsimp
    rw [← t.isLE_iff_isZero_truncGE_obj (j - 1) j (by simp)]
    exact t.isLE_of_LE X n (j - 1) (by linarith)
  · apply Functor.zero_obj

lemma truncGEt_obj_obj_isGE (n : ℤ) (i : ℤt) (h : ℤt.mk n ≤ i) (X : C) :
    t.IsGE ((t.truncGEt.obj i).obj X) n := by
  obtain (rfl|⟨i, rfl⟩|rfl) := i.three_cases
  · simp at h
  · simp at h
    dsimp
    exact t.isGE_of_GE  _ _ _ h
  · dsimp
    apply t.isGE_of_isZero
    apply Functor.zero_obj

lemma truncLTt_obj_obj_isLE (n : ℤ) (i : ℤt) (h : i ≤ ℤt.mk (n + 1)) (X : C) :
    t.IsLE (((t.truncLTt.obj i)).obj X) n := by
  obtain (rfl|⟨i, rfl⟩|rfl) := i.three_cases
  · dsimp
    apply t.isLE_of_isZero
    apply Functor.zero_obj
  · simp at h
    dsimp
    exact t.isLE_of_LE _ (i - 1) n (by linarith)
  · simp at h

noncomputable def homology'' (n : ℤ) : C ⥤ C := t.truncGELE n n ⋙ shiftFunctor C n

instance (X : C) (n : ℤ) : t.IsLE ((t.homology'' n).obj X) 0 :=
  t.isLE_shift _ n n 0 (add_zero n)

instance (X : C) (n : ℤ) : t.IsGE ((t.homology'' n).obj X) 0 :=
  t.isGE_shift _ n n 0 (add_zero n)

lemma homology''_obj_mem_heart (n : ℤ) (X : C) : t.heart ((t.homology'' n).obj X) := by
  rw [mem_heart_iff]
  exact ⟨inferInstance, inferInstance⟩

noncomputable def homology' (n : ℤ) : C ⥤ t.Heart' :=
  FullSubcategory.lift _ (t.truncGELE n n ⋙ shiftFunctor C n) (t.homology''_obj_mem_heart n)

noncomputable def homologyCompιHeart' (n : ℤ) :
  t.homology' n ⋙ t.ιHeart' ≅ t.truncGELE n n ⋙ shiftFunctor C n :=
    FullSubcategory.lift_comp_inclusion _ _ _

noncomputable def homology₀CompιHeart'IsoTruncGELE : t.homology' 0 ⋙ t.ιHeart' ≅ t.truncGELE 0 0 :=
  t.homologyCompιHeart' 0 ≪≫ isoWhiskerLeft (t.truncGELE 0 0) (shiftFunctorZero C ℤ)

noncomputable def homologyCompιHeartDegreeIsoHomology' (q : ℤ) :
    t.homology' q ⋙ t.ιHeartDegree q ≅ t.truncGELE q q :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (t.homologyCompιHeart' q) _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _  (shiftFunctorCompIsoId C q (-q) (add_right_neg q)) ≪≫
    Functor.rightUnitor _

lemma isIso_truncGE_map_truncGEπ_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((t.truncGE b).map ((t.truncGEπ a).app X)) :=
  t.isIso₂_truncGE_map_of_LE _
    (t.triangleLEGE_distinguished (a-1) a (by linarith) X) (b-1) b (by linarith)
      (t.isLE_of_LE ((t.truncLE (a-1)).obj X) (a-1) (b-1) (by linarith))

lemma isIso_truncLT_map_truncLTι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLT a).map ((t.truncLTι b).app X)) :=
  t.isIso₁_truncLT_map_of_GE _ (t.triangleLTGE_distinguished b X) a
    (t.isGE_of_GE ((t.truncGE b).obj X) a b (by linarith))

lemma isIso_truncLE_map_truncLEι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLE a).map ((t.truncLEι b).app X)) := by
  apply isIso_truncLT_map_truncLTι_app
  linarith

instance (X : C) (n : ℤ) : IsIso ((t.truncLE n).map ((t.truncLEι n).app X)) := by
  apply t.isIso_truncLE_map_truncLEι_app
  rfl

instance (X : C) (n : ℤ) : IsIso ((t.truncGE n).map ((t.truncGEπ n).app X)) := by
  apply t.isIso_truncGE_map_truncGEπ_app
  rfl

lemma isIso_truncGEt_obj_map_truncGEπ_app (a b : ℤt) (h : a ≤ b) (X : C) :
    IsIso ((t.truncGEt.obj b).map ((t.abstractSpectralObject.truncGEπ a).app X)) := by
  obtain (rfl|⟨b, rfl⟩|rfl) := b.three_cases
  · simp only [ℤt.le_bot_iff] at h
    subst h
    dsimp
    simp only [AbstractSpectralObject.truncGEπ_bot_app]
    infer_instance
  · obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
    · dsimp
      infer_instance
    · simp only [ℤt.mk_le_mk_iff] at h
      dsimp
      simp only [AbstractSpectralObject.truncGEπ_mk]
      exact t.isIso_truncGE_map_truncGEπ_app a b h X
    · simp at h
  · refine' ⟨0, IsZero.eq_of_src _ _ _, IsZero.eq_of_src _ _ _⟩
    all_goals
      simp only [truncGEt_obj_top, Functor.zero_obj]

lemma isIso_truncLTt_obj_map_truncLTπ_app (a b : ℤt) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLTt.obj a).map ((t.abstractSpectralObject.truncLTι b).app X)) := by
  obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
  · refine' ⟨0, IsZero.eq_of_src _ _ _, IsZero.eq_of_src _ _ _⟩
    all_goals
      simp only [truncLTt_obj_bot, Functor.zero_obj]
  · obtain (rfl|⟨b, rfl⟩|rfl) := b.three_cases
    · simp at h
    · simp only [ℤt.mk_le_mk_iff] at h
      dsimp
      simp only [AbstractSpectralObject.truncLEι_mk]
      exact t.isIso_truncLT_map_truncLTι_app a b h X
    · dsimp
      infer_instance
  · simp only [ℤt.top_le_iff] at h
    subst h
    dsimp
    simp only [AbstractSpectralObject.truncLTι_top_app]
    infer_instance

instance (D : Arrow ℤt) (X : C) :
  IsIso ((t.abstractSpectralObject.truncGEToTruncGEGE.app D).app X) :=
    t.isIso_truncGEt_obj_map_truncGEπ_app _ _ (leOfHom D.hom) X

instance (D : Arrow ℤt) (X : C) :
  IsIso ((t.abstractSpectralObject.truncLTLTToTruncLT.app D).app X) :=
    t.isIso_truncLTt_obj_map_truncLTπ_app _ _ (leOfHom D.hom) X

instance (D : Arrow ℤt) : IsIso (t.abstractSpectralObject.truncGEToTruncGEGE.app D) :=
  NatIso.isIso_of_isIso_app _

instance (D : Arrow ℤt) : IsIso (t.abstractSpectralObject.truncLTLTToTruncLT.app D) :=
  NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncGEToTruncGEGE) := NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncLTLTToTruncLT) := NatIso.isIso_of_isIso_app _

lemma truncGEπ_compatibility (a : ℤt) (X : C) :
  (t.abstractSpectralObject.truncGE.obj a).map ((t.abstractSpectralObject.truncGEπ a).app X) =
    (t.abstractSpectralObject.truncGEπ a).app
      ((t.abstractSpectralObject.truncGE.obj a).obj X) := by
  obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
  · rfl
  · dsimp
    simp only [AbstractSpectralObject.truncGEπ_mk]
    apply from_truncGE_obj_ext
    exact ((t.truncGEπ a).naturality ((t.truncGEπ a).app X)).symm
  · apply IsZero.eq_of_src
    dsimp
    simp

lemma truncLTι_compatibility (a : ℤt) (X : C) :
    (t.abstractSpectralObject.truncLT.obj a).map ((t.abstractSpectralObject.truncLTι a).app X) =
      (t.abstractSpectralObject.truncLTι a).app
        ((t.abstractSpectralObject.truncLT.obj a).obj X) := by
  obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
  · apply IsZero.eq_of_src
    dsimp
    simp
  · dsimp
    simp only [AbstractSpectralObject.truncLEι_mk]
    apply to_truncLT_obj_ext
    exact ((t.truncLTι a).naturality ((t.truncLTι a).app X))
  · rfl

lemma isIso_truncLTι_app_truncGELT_obj (a b : ℤt) (h : a ≤ b) (X : C) :
    IsIso ((t.abstractSpectralObject.truncLTι b).app
      ((t.truncLTt.obj b ⋙ t.truncGEt.obj a).obj X)) := by
  obtain (rfl|⟨b, rfl⟩|rfl) := b.three_cases
  · refine' ⟨0, IsZero.eq_of_src _ _ _, IsZero.eq_of_src _ _ _⟩
    · dsimp
      simp
    · dsimp
      refine' IsZero.of_iso (isZero_zero _)
        (Functor.mapIso _ (IsZero.isoZero (Functor.zero_obj _)) ≪≫
          (t.truncGEt.obj a).mapZeroObject)
  · dsimp [SpectralObject.AbstractSpectralObject.truncLTι]
    simp only [comp_id]
    rw [← t.isLE_iff_isIso_truncLTι_app (b-1) b (by linarith)]
    obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
    · dsimp
      infer_instance
    · dsimp
      infer_instance
    · dsimp
      apply t.isLE_of_isZero
      simp
  · dsimp [SpectralObject.AbstractSpectralObject.truncLTι]
    erw [comp_id, Functor.map_id]
    dsimp
    infer_instance

instance (D : Arrow ℤt) (X : C) :
    IsIso ((t.abstractSpectralObject.truncLTGELTSelfToTruncGELT.app D).app X) :=
  t.isIso_truncLTι_app_truncGELT_obj D.left D.right (leOfHom D.hom) X

instance (D : Arrow ℤt) : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncGELT.app D) :=
  NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncGELT) :=
  NatIso.isIso_of_isIso_app _

instance (a b : ℤ) (X : C) : t.IsLE ((t.truncGELT a b).obj X) (b-1) := by
  dsimp [truncGELT]
  infer_instance

noncomputable def natTransTruncGELTTruncLTGE (a b : ℤ) :
    t.truncGELT a b ⟶ t.truncLTGE a b where
  app X := t.liftTruncLT (t.descTruncGE
    ((t.truncLTι b).app X ≫ (t.truncGEπ a).app X) a) (b-1) b (by linarith)
  naturality X Y f := by
    dsimp [truncGELT, truncLTGE]
    apply t.to_truncLT_obj_ext
    dsimp
    apply t.from_truncGE_obj_ext
    simp only [Functor.id_obj, assoc, liftTruncLT_ι, NatTrans.naturality,
      Functor.id_map, liftTruncLT_ι_assoc, π_descTruncGE_assoc,
      ← NatTrans.naturality_assoc, π_descTruncGE]
    rw [← NatTrans.naturality, NatTrans.naturality_assoc]

@[reassoc (attr := simp)]
lemma natTransTruncGELETruncLEGE_app_pentagon (a b : ℤ) (X : C) :
    (t.truncGEπ a).app _ ≫ (t.natTransTruncGELTTruncLTGE a b).app X ≫ (t.truncLTι b).app _ =
      (t.truncLTι b).app X ≫ (t.truncGEπ a).app X := by simp [natTransTruncGELTTruncLTGE]

lemma natTransTruncGELETruncLEGE_app_pentagon_uniqueness (a b : ℤ) (X : C)
    (φ : (t.truncGELT a b).obj X ⟶ (t.truncLTGE a b).obj X)
    (hφ : (t.truncGEπ a).app _ ≫ φ ≫ (t.truncLTι b).app _ =
      (t.truncLTι b).app X ≫ (t.truncGEπ a).app X) :
    φ = (t.natTransTruncGELTTruncLTGE a b).app X := by
  apply t.to_truncLT_obj_ext
  dsimp
  apply t.from_truncGE_obj_ext
  rw [hφ, natTransTruncGELETruncLEGE_app_pentagon]

noncomputable def truncGELTδLT (a b : ℤ) :
    t.truncGELT a b ⟶ t.truncLT a ⋙ shiftFunctor C (1 : ℤ) :=
  whiskerLeft (t.truncLT b) (t.truncGEδLT a) ≫
    whiskerRight (t.truncLTι b) (t.truncLT a ⋙ shiftFunctor C (1 : ℤ))

@[simps!]
noncomputable def triangleLTLTGELT (a b : ℤ) (h : a ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.natTransTruncLTOfLE a b h)
    (whiskerLeft (t.truncLT b) (t.truncGEπ a)) (t.truncGELTδLT a b)

lemma triangleLTLTGELT_distinguished (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.triangleLTLTGELT a b h).obj X ∈ distTriang C := by
  have := t.isIso_truncLT_map_truncLTι_app a b h X
  refine' isomorphic_distinguished _ (t.triangleLTGE_distinguished a ((t.truncLT b).obj X)) _ _
  refine' Triangle.isoMk _ _ ((asIso ((t.truncLT a).map ((t.truncLTι b).app X))).symm)
    (Iso.refl _) (Iso.refl _) _ _ _
  · dsimp
    simp only [comp_id, IsIso.eq_inv_comp]
    apply t.to_truncLT_obj_ext
    simp only [Functor.id_obj, NatTrans.naturality, assoc, Functor.id_map,
      natTransTruncLTOfLE_ι_app_assoc]
  · dsimp
    simp only [comp_id, id_comp]
  · dsimp [truncGELTδLT]
    simp only [Functor.map_inv, assoc, IsIso.hom_inv_id, comp_id, id_comp]

instance (a b : ℤ) (X : C) : IsIso ((t.natTransTruncGELTTruncLTGE a b).app X) := by
  by_cases h : a ≤ b
  · let u₁₂ := (t.natTransTruncLTOfLE a b h).app X
    let u₂₃ : (t.truncLT b).obj X ⟶ X := (t.truncLTι b).app X
    let u₁₃ : _ ⟶ X := (t.truncLTι a).app X
    have eq : u₁₂ ≫ u₂₃ = u₁₃ := by simp [u₁₂, u₂₃, u₁₃]
    have H := someOctahedron eq (t.triangleLTLTGELT_distinguished a b h X)
      (t.triangleLTGE_distinguished b X) (t.triangleLTGE_distinguished a X)
    let m₁ : (t.truncGELT a b).obj X ⟶  _ := H.m₁
    have := t.isIso₁_truncLT_map_of_GE _ H.mem b (by dsimp ; infer_instance)
    dsimp at this
    have eq' : t.liftTruncLT m₁ (b-1) b (by linarith) =
        (t.natTransTruncGELTTruncLTGE a b).app X := by
      apply t.to_truncLT_obj_ext
      dsimp
      apply t.from_truncGE_obj_ext
      simp_rw [natTransTruncGELETruncLEGE_app_pentagon, liftTruncLT_ι]
      exact H.comm₁
    rw [← eq']
    have fac : (t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)) ≫
        t.liftTruncLT m₁ (b-1) b (by linarith) = (t.truncLT b).map m₁ :=
      t.to_truncLT_obj_ext _ _ _ _ (by simp [truncGELT])
    have : IsIso ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X))) := by
      rw [← t.isLE_iff_isIso_truncLTι_app (b-1) b (by linarith)]
      infer_instance
    exact IsIso.of_isIso_fac_left fac
  · refine' ⟨0, _, _⟩
    all_goals
      apply IsZero.eq_of_src
      refine' t.isZero _ (b-1) a (by linarith)

instance (a b : ℤ) : IsIso (t.natTransTruncGELTTruncLTGE a b) :=
  NatIso.isIso_of_isIso_app _

noncomputable def truncGELTIsoLTGE (a b : ℤ) : t.truncGELT a b ≅ t.truncLTGE a b :=
  asIso (t.natTransTruncGELTTruncLTGE a b)

noncomputable def truncGELEIsoLEGE (a b : ℤ) : t.truncGELE a b ≅ t.truncLEGE a b :=
  t.truncGELTIsoLTGE a (b + 1)

instance (a b : ℤ) (X : C) :
  IsIso ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X))) := by
    rw [← t.isLE_iff_isIso_truncLTι_app (b-1) b (by linarith)]
    infer_instance

lemma truncLT_map_truncGE_map_truncLTι_app_fac (a b : ℤ) (X : C) :
    (t.truncLT b).map ((t.truncGE a).map ((t.truncLTι b).app X)) =
      (t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)) ≫
        (t.natTransTruncGELTTruncLTGE a b).app X := by
  rw [← cancel_epi (inv ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)))),
    IsIso.inv_hom_id_assoc]
  apply t.natTransTruncGELETruncLEGE_app_pentagon_uniqueness
  simp only [Functor.id_obj, assoc, NatTrans.naturality, Functor.id_map, IsIso.inv_hom_id_assoc]
  exact ((t.truncGEπ a).naturality ((t.truncLTι b).app X)).symm

lemma isIso_truncLT_map_truncGE_map_truncLTι_app (a b : ℤ) (X : C) :
    IsIso ((t.truncLT b).map ((t.truncGE a).map ((t.truncLTι b).app X))) := by
  rw [t.truncLT_map_truncGE_map_truncLTι_app_fac a b X]
  infer_instance

instance (D : Arrow ℤt) (X : C) :
    IsIso ((t.abstractSpectralObject.truncLTGELTSelfToTruncLTGE.app D).app X) := by
  obtain ⟨a, b, f : a ⟶ b⟩ := D
  have h : a ≤ b := leOfHom f
  obtain (rfl|⟨b, rfl⟩|rfl) := b.three_cases
  · simp only [ℤt.le_bot_iff] at h
    subst h
    exact ⟨0, IsZero.eq_of_src (Functor.zero_obj _) _ _,
      IsZero.eq_of_src (Functor.zero_obj _) _ _⟩
  dsimp [SpectralObject.AbstractSpectralObject.truncLTGELTSelfToTruncLTGE,
      SpectralObject.AbstractSpectralObject.truncLTGE]
  · obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
    · simp only [AbstractSpectralObject.truncLEι_mk]
      exact t.isIso_truncLT_map_truncLTι_app b b (by rfl) X
    · simp only [ℤt.mk_le_mk_iff] at h
      simp only [truncGEt_obj_mk, AbstractSpectralObject.truncLEι_mk]
      exact t.isIso_truncLT_map_truncGE_map_truncLTι_app a b X
    · refine' ⟨0, IsZero.eq_of_src _ _ _,
        IsZero.eq_of_src _ _ _⟩
      all_goals
        exact IsZero.of_iso (isZero_zero _)
          ((t.truncLT b).mapIso ((Functor.zero_obj _).isoZero) ≪≫
          (t.truncLT b).mapZeroObject)
  · dsimp [SpectralObject.AbstractSpectralObject.truncLTGELTSelfToTruncLTGE]
    simp only [AbstractSpectralObject.truncLTι_top_app, Functor.map_id]
    infer_instance

instance (D : Arrow ℤt) : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncLTGE.app D) :=
  NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncLTGE) :=
  NatIso.isIso_of_isIso_app _

instance : t.abstractSpectralObject.IsCompatible where
  distinguished := AbstractSpectralObject.distinguished t
  truncGEπ_compatibility' := t.truncGEπ_compatibility
  truncLTι_compatibility' := t.truncLTι_compatibility

@[simps!]
noncomputable def spectralObject (X : C) : SpectralObject C ℤt :=
  t.abstractSpectralObject.spectralObject X

noncomputable def shiftSpectralObjectω₁IsoHomologyιHeart' (X : C) (q q' : ℤ) (hq' : q + 1 = q') :
    ((t.spectralObject X).ω₁ ⋙ shiftFunctor C q).obj
      (ComposableArrows.mk₁ (homOfLE (by simp; linarith) : ℤt.mk q ⟶ ℤt.mk q')) ≅
      (t.homology' q ⋙ t.ιHeart').obj X :=
  (shiftFunctor C q).mapIso ((t.truncGELEIsoTruncGELT q q q' hq').symm.app X) ≪≫
    (t.homologyCompιHeart' q).symm.app X

noncomputable def homology₀CompιHeartIsoTruncLEGE : t.homology' 0 ⋙ t.ιHeart' ≅ t.truncLEGE 0 0 :=
  t.homology₀CompιHeart'IsoTruncGELE ≪≫ t.truncGELEIsoLEGE 0 0

end TStructure

namespace Subcategory

lemma HasInducedTStructure.mk' (S : Subcategory C) (t : TStructure C)
    (h : ∀ (X : C) (_ : S.P X) (n : ℤ), S.P ((t.truncLE n).obj X) ∧
      (S.P ((t.truncGE n).obj X))) :
    S.HasInducedTStructure t where
  exists_triangle_zero_one X hX := by
    refine' ⟨_, _, _, _, _, _, _,
      t.triangleLEGE_distinguished 0 1 (by linarith) X,
      ⟨⟨(t.truncLE 0).obj X, (h X hX 0).1⟩, ⟨Iso.refl _⟩⟩,
      ⟨⟨(t.truncGE 1).obj X, (h X hX 1).2⟩, ⟨Iso.refl _⟩⟩⟩
    exact TStructure.mem_of_isLE  _ _ _
    exact TStructure.mem_of_isGE  _ _ _

lemma mem_of_hasInductedTStructure (S : Subcategory C) (t : TStructure C)
    [ClosedUnderIsomorphisms S.P] [S.HasInducedTStructure t]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) (h₂ : S.P T.obj₂)
    (h₃ : t.IsGE T.obj₃ n₁) :
    S.P T.obj₁ ∧ S.P T.obj₃ := by
  obtain ⟨e, _⟩ := t.triangle_iso_exists n₀ n₁ (by omega) _ _ hT
    (S.ι.map_distinguished _ ((S.tStructure t).triangleLEGE_distinguished n₀ n₁ h ⟨_, h₂⟩))
    (Iso.refl _) inferInstance inferInstance (by
      dsimp
      rw [← S.tStructure_isLE_iff]
      infer_instance) (by
      dsimp
      rw [← S.tStructure_isGE_iff]
      infer_instance)
  exact ⟨(mem_iff_of_iso S.P (Triangle.π₁.mapIso e)).2 (S.ι_obj_mem _),
    (mem_iff_of_iso S.P (Triangle.π₃.mapIso e)).2 (S.ι_obj_mem _)⟩

instance (S S' : Subcategory C) (t : TStructure C) [S.HasInducedTStructure t]
    [S'.HasInducedTStructure t]
    [ClosedUnderIsomorphisms S.P] [ClosedUnderIsomorphisms S'.P] :
    (S.inter S').HasInducedTStructure t :=
  HasInducedTStructure.mk' _ _ (by
    rintro X ⟨hX, hX'⟩ n
    exact
      ⟨⟨(S.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
        (by dsimp; infer_instance) hX (by dsimp; infer_instance)).1,
      (S'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
        (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).1⟩,
        ⟨(S.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by omega) X)
        (n - 1) n (by omega) (by dsimp; infer_instance) hX (by dsimp; infer_instance)).2,
      (S'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by omega) X)
        (n - 1) n (by omega) (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).2⟩⟩)

end Subcategory

instance [IsTriangulated C] : t.plus.HasInducedTStructure t := by
  apply Subcategory.HasInducedTStructure.mk'
  rintro X ⟨a, _⟩ n
  exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩

instance [IsTriangulated C] : t.minus.HasInducedTStructure t := by
  apply Subcategory.HasInducedTStructure.mk'
  rintro X ⟨a, _⟩ n
  exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩

instance [IsTriangulated C] : t.bounded.HasInducedTStructure t := by
  dsimp [TStructure.bounded]
  infer_instance

namespace TStructure

instance (X : C) (n : ℤ) [t.IsLE X n] (i : ℤt) :
    t.IsLE ((t.truncLTt.obj i).obj X) n := by
  obtain rfl|⟨i, rfl⟩|rfl := ℤt.three_cases i
  · apply isLE_of_isZero
    simp
  · dsimp
    infer_instance
  · dsimp
    infer_instance

instance [IsTriangulated C] (X : C) (n : ℤ) [t.IsGE X n] (i : ℤt) :
    t.IsGE ((t.truncLTt.obj i).obj X) n := by
  obtain rfl|⟨i, rfl⟩|rfl := ℤt.three_cases i
  · apply isGE_of_isZero
    simp
  · dsimp
    infer_instance
  · dsimp
    infer_instance

instance [IsTriangulated C] (X : C) (n : ℤ) [t.IsLE X n] (i : ℤt) :
    t.IsLE ((t.truncGEt.obj i).obj X) n := by
  obtain rfl|⟨i, rfl⟩|rfl := ℤt.three_cases i
  · dsimp
    infer_instance
  · dsimp
    infer_instance
  · apply isLE_of_isZero
    simp

instance (X : C) (n : ℤ) [t.IsGE X n] (i : ℤt) :
    t.IsGE ((t.truncGEt.obj i).obj X) n := by
  obtain rfl|⟨i, rfl⟩|rfl := ℤt.three_cases i
  · dsimp
    infer_instance
  · dsimp
    infer_instance
  · apply isGE_of_isZero
    simp

end TStructure

end Triangulated

end CategoryTheory
