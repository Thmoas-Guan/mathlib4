/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.Restrict
import Mathlib.Tactic.FailIfNoProgress

#align_import analysis.normed_space.affine_isometry from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Affine isometries

In this file we define `AffineIsometry 𝕜 P P₂` to be an affine isometric embedding of normed
add-torsors `P` into `P₂` over normed `𝕜`-spaces and `AffineIsometryEquiv` to be an affine
isometric equivalence between `P` and `P₂`.

We also prove basic lemmas and provide convenience constructors.  The choice of these lemmas and
constructors is closely modelled on those for the `LinearIsometry` and `AffineMap` theories.

Since many elementary properties don't require `‖x‖ = 0 → x = 0` we initially set up the theory for
`SeminormedAddCommGroup` and specialize to `NormedAddCommGroup` only when needed.

## Notation

We introduce the notation `P →ᵃⁱ[𝕜] P₂` for `AffineIsometry 𝕜 P P₂`, and `P ≃ᵃⁱ[𝕜] P₂` for
`AffineIsometryEquiv 𝕜 P P₂`.  In contrast with the notation `→ₗᵢ` for linear isometries, `≃ᵢ`
for isometric equivalences, etc., the "i" here is a superscript.  This is for aesthetic reasons to
match the superscript "a" (note that in mathlib `→ᵃ` is an affine map, since `→ₐ` has been taken by
algebra-homomorphisms.)

-/


open Function Set

variable (𝕜 : Type*) {V V₁ V₁' V₂ V₃ V₄ : Type*} {P₁ P₁' : Type*} (P P₂ : Type*) {P₃ P₄ : Type*}
  [NormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [SeminormedAddCommGroup V₁] [NormedSpace 𝕜 V₁] [PseudoMetricSpace P₁] [NormedAddTorsor V₁ P₁]
  [SeminormedAddCommGroup V₁'] [NormedSpace 𝕜 V₁'] [MetricSpace P₁'] [NormedAddTorsor V₁' P₁']
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂]
  [SeminormedAddCommGroup V₃] [NormedSpace 𝕜 V₃] [PseudoMetricSpace P₃] [NormedAddTorsor V₃ P₃]
  [SeminormedAddCommGroup V₄] [NormedSpace 𝕜 V₄] [PseudoMetricSpace P₄] [NormedAddTorsor V₄ P₄]

/-- A `𝕜`-affine isometric embedding of one normed add-torsor over a normed `𝕜`-space into
another. -/
structure AffineIsometry extends P →ᵃ[𝕜] P₂ where
  norm_map : ∀ x : V, ‖linear x‖ = ‖x‖
#align affine_isometry AffineIsometry

variable {𝕜 P P₂}

@[inherit_doc]
notation:25 -- `→ᵃᵢ` would be more consistent with the linear isometry notation, but it is uglier
P " →ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometry 𝕜 P P₂

namespace AffineIsometry

variable (f : P →ᵃⁱ[𝕜] P₂)

/-- The underlying linear map of an affine isometry is in fact a linear isometry. -/
protected def linearIsometry : V →ₗᵢ[𝕜] V₂ :=
  { f.linear with norm_map' := f.norm_map }
#align affine_isometry.linear_isometry AffineIsometry.linearIsometry

@[simp]
lemma linear_eq_linearIsometry : f.linear = f.linearIsometry.toLinearMap := by
  ext
  rfl
#align affine_isometry.linear_eq_linear_isometry AffineIsometry.linear_eq_linearIsometry

instance : FunLike (P →ᵃⁱ[𝕜] P₂) P P₂ :=
  { coe := fun f => f.toFun,
    coe_injective' := fun f g => by cases f; cases g; simp }

@[simp]
lemma coe_toAffineMap : ⇑f.toAffineMap = f := by
  rfl
#align affine_isometry.coe_to_affine_map AffineIsometry.coe_toAffineMap

lemma toAffineMap_injective : Injective (toAffineMap : (P →ᵃⁱ[𝕜] P₂) → P →ᵃ[𝕜] P₂) := by
  rintro ⟨f, _⟩ ⟨g, _⟩ rfl
  rfl
#align affine_isometry.to_affine_map_injective AffineIsometry.toAffineMap_injective

lemma coeFn_injective : @Injective (P →ᵃⁱ[𝕜] P₂) (P → P₂) (↑) :=
  AffineMap.coeFn_injective.comp toAffineMap_injective
#align affine_isometry.coe_fn_injective AffineIsometry.coeFn_injective

@[ext]
lemma ext {f g : P →ᵃⁱ[𝕜] P₂} (h : ∀ x, f x = g x) : f = g :=
  coeFn_injective <| funext h
#align affine_isometry.ext AffineIsometry.ext

end AffineIsometry

namespace LinearIsometry

variable (f : V →ₗᵢ[𝕜] V₂)

/-- Reinterpret a linear isometry as an affine isometry. -/
def toAffineIsometry : V →ᵃⁱ[𝕜] V₂ :=
  { f.toLinearMap.toAffineMap with norm_map := f.norm_map }
#align linear_isometry.to_affine_isometry LinearIsometry.toAffineIsometry

@[simp]
lemma coe_toAffineIsometry : ⇑(f.toAffineIsometry : V →ᵃⁱ[𝕜] V₂) = f :=
  rfl
#align linear_isometry.coe_to_affine_isometry LinearIsometry.coe_toAffineIsometry

@[simp]
lemma toAffineIsometry_linearIsometry : f.toAffineIsometry.linearIsometry = f := by
  ext
  rfl
#align linear_isometry.to_affine_isometry_linear_isometry LinearIsometry.toAffineIsometry_linearIsometry

-- somewhat arbitrary choice of simp direction
@[simp]
lemma toAffineIsometry_toAffineMap : f.toAffineIsometry.toAffineMap = f.toLinearMap.toAffineMap :=
  rfl
#align linear_isometry.to_affine_isometry_to_affine_map LinearIsometry.toAffineIsometry_toAffineMap

end LinearIsometry

namespace AffineIsometry

variable (f : P →ᵃⁱ[𝕜] P₂) (f₁ : P₁' →ᵃⁱ[𝕜] P₂)

@[simp]
lemma map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linearIsometry v +ᵥ f p :=
  f.toAffineMap.map_vadd p v
#align affine_isometry.map_vadd AffineIsometry.map_vadd

@[simp]
lemma map_vsub (p1 p2 : P) : f.linearIsometry (p1 -ᵥ p2) = f p1 -ᵥ f p2 :=
  f.toAffineMap.linearMap_vsub p1 p2
#align affine_isometry.map_vsub AffineIsometry.map_vsub

@[simp]
lemma dist_map (x y : P) : dist (f x) (f y) = dist x y := by
  rw [dist_eq_norm_vsub V₂, dist_eq_norm_vsub V, ← map_vsub, f.linearIsometry.norm_map]
#align affine_isometry.dist_map AffineIsometry.dist_map

@[simp]
lemma nndist_map (x y : P) : nndist (f x) (f y) = nndist x y := by simp [nndist_dist]
#align affine_isometry.nndist_map AffineIsometry.nndist_map

@[simp]
lemma edist_map (x y : P) : edist (f x) (f y) = edist x y := by simp [edist_dist]
#align affine_isometry.edist_map AffineIsometry.edist_map

protected lemma isometry : Isometry f :=
  f.edist_map
#align affine_isometry.isometry AffineIsometry.isometry

protected lemma injective : Injective f₁ :=
  f₁.isometry.injective
#align affine_isometry.injective AffineIsometry.injective

@[simp]
lemma map_eq_iff {x y : P₁'} : f₁ x = f₁ y ↔ x = y :=
  f₁.injective.eq_iff
#align affine_isometry.map_eq_iff AffineIsometry.map_eq_iff

lemma map_ne {x y : P₁'} (h : x ≠ y) : f₁ x ≠ f₁ y :=
  f₁.injective.ne h
#align affine_isometry.map_ne AffineIsometry.map_ne

protected lemma lipschitz : LipschitzWith 1 f :=
  f.isometry.lipschitz
#align affine_isometry.lipschitz AffineIsometry.lipschitz

protected lemma antilipschitz : AntilipschitzWith 1 f :=
  f.isometry.antilipschitz
#align affine_isometry.antilipschitz AffineIsometry.antilipschitz

@[continuity]
protected lemma continuous : Continuous f :=
  f.isometry.continuous
#align affine_isometry.continuous AffineIsometry.continuous

lemma ediam_image (s : Set P) : EMetric.diam (f '' s) = EMetric.diam s :=
  f.isometry.ediam_image s
#align affine_isometry.ediam_image AffineIsometry.ediam_image

lemma ediam_range : EMetric.diam (range f) = EMetric.diam (univ : Set P) :=
  f.isometry.ediam_range
#align affine_isometry.ediam_range AffineIsometry.ediam_range

lemma diam_image (s : Set P) : Metric.diam (f '' s) = Metric.diam s :=
  f.isometry.diam_image s
#align affine_isometry.diam_image AffineIsometry.diam_image

lemma diam_range : Metric.diam (range f) = Metric.diam (univ : Set P) :=
  f.isometry.diam_range
#align affine_isometry.diam_range AffineIsometry.diam_range

@[simp]
lemma comp_continuous_iff {α : Type*} [TopologicalSpace α] {g : α → P} :
    Continuous (f ∘ g) ↔ Continuous g :=
  f.isometry.comp_continuous_iff
#align affine_isometry.comp_continuous_iff AffineIsometry.comp_continuous_iff

/-- The identity affine isometry. -/
def id : P →ᵃⁱ[𝕜] P :=
  ⟨AffineMap.id 𝕜 P, fun _ => rfl⟩
#align affine_isometry.id AffineIsometry.id

@[simp]
lemma coe_id : ⇑(id : P →ᵃⁱ[𝕜] P) = _root_.id :=
  rfl
#align affine_isometry.coe_id AffineIsometry.coe_id

@[simp]
lemma id_apply (x : P) : (AffineIsometry.id : P →ᵃⁱ[𝕜] P) x = x :=
  rfl
#align affine_isometry.id_apply AffineIsometry.id_apply

@[simp]
lemma id_toAffineMap : (id.toAffineMap : P →ᵃ[𝕜] P) = AffineMap.id 𝕜 P :=
  rfl
#align affine_isometry.id_to_affine_map AffineIsometry.id_toAffineMap

instance : Inhabited (P →ᵃⁱ[𝕜] P) :=
  ⟨id⟩

/-- Composition of affine isometries. -/
def comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : P →ᵃⁱ[𝕜] P₃ :=
  ⟨g.toAffineMap.comp f.toAffineMap, fun _ => (g.norm_map _).trans (f.norm_map _)⟩
#align affine_isometry.comp AffineIsometry.comp

@[simp]
lemma coe_comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : ⇑(g.comp f) = g ∘ f :=
  rfl
#align affine_isometry.coe_comp AffineIsometry.coe_comp

@[simp]
lemma id_comp : (id : P₂ →ᵃⁱ[𝕜] P₂).comp f = f :=
  ext fun _ => rfl
#align affine_isometry.id_comp AffineIsometry.id_comp

@[simp]
lemma comp_id : f.comp id = f :=
  ext fun _ => rfl
#align affine_isometry.comp_id AffineIsometry.comp_id

lemma comp_assoc (f : P₃ →ᵃⁱ[𝕜] P₄) (g : P₂ →ᵃⁱ[𝕜] P₃) (h : P →ᵃⁱ[𝕜] P₂) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align affine_isometry.comp_assoc AffineIsometry.comp_assoc

instance : Monoid (P →ᵃⁱ[𝕜] P) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
lemma coe_one : ⇑(1 : P →ᵃⁱ[𝕜] P) = _root_.id :=
  rfl
#align affine_isometry.coe_one AffineIsometry.coe_one

@[simp]
lemma coe_mul (f g : P →ᵃⁱ[𝕜] P) : ⇑(f * g) = f ∘ g :=
  rfl
#align affine_isometry.coe_mul AffineIsometry.coe_mul

end AffineIsometry

namespace AffineSubspace

/-- `AffineSubspace.subtype` as an `AffineIsometry`. -/
def subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] : s →ᵃⁱ[𝕜] P :=
  { s.subtype with norm_map := s.direction.subtypeₗᵢ.norm_map }
#align affine_subspace.subtypeₐᵢ AffineSubspace.subtypeₐᵢ

lemma subtypeₐᵢ_linear (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.linear = s.direction.subtype :=
  rfl
#align affine_subspace.subtypeₐᵢ_linear AffineSubspace.subtypeₐᵢ_linear

@[simp]
lemma subtypeₐᵢ_linearIsometry (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.linearIsometry = s.direction.subtypeₗᵢ :=
  rfl
#align affine_subspace.subtypeₐᵢ_linear_isometry AffineSubspace.subtypeₐᵢ_linearIsometry

@[simp]
lemma coe_subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] : ⇑s.subtypeₐᵢ = s.subtype :=
  rfl
#align affine_subspace.coe_subtypeₐᵢ AffineSubspace.coe_subtypeₐᵢ

@[simp]
lemma subtypeₐᵢ_toAffineMap (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.toAffineMap = s.subtype :=
  rfl
#align affine_subspace.subtypeₐᵢ_to_affine_map AffineSubspace.subtypeₐᵢ_toAffineMap

end AffineSubspace

variable (𝕜 P P₂)

/-- An affine isometric equivalence between two normed vector spaces. -/
structure AffineIsometryEquiv extends P ≃ᵃ[𝕜] P₂ where
  norm_map : ∀ x, ‖linear x‖ = ‖x‖
#align affine_isometry_equiv AffineIsometryEquiv

variable {𝕜 P P₂}

-- `≃ᵃᵢ` would be more consistent with the linear isometry equiv notation, but it is uglier
notation:25 P " ≃ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometryEquiv 𝕜 P P₂

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

/-- The underlying linear equiv of an affine isometry equiv is in fact a linear isometry equiv. -/
protected def linearIsometryEquiv : V ≃ₗᵢ[𝕜] V₂ :=
  { e.linear with norm_map' := e.norm_map }
#align affine_isometry_equiv.linear_isometry_equiv AffineIsometryEquiv.linearIsometryEquiv

@[simp]
lemma linear_eq_linear_isometry : e.linear = e.linearIsometryEquiv.toLinearEquiv := by
  ext
  rfl
#align affine_isometry_equiv.linear_eq_linear_isometry AffineIsometryEquiv.linear_eq_linear_isometry

instance : EquivLike (P ≃ᵃⁱ[𝕜] P₂) P P₂ :=
  { coe := fun f => f.toFun
    inv := fun f => f.invFun
    left_inv := fun f => f.left_inv
    right_inv := fun f => f.right_inv,
    coe_injective' := fun f g h _ => by
      cases f
      cases g
      congr
      simpa [DFunLike.coe_injective.eq_iff] using h }

@[simp]
lemma coe_mk (e : P ≃ᵃ[𝕜] P₂) (he : ∀ x, ‖e.linear x‖ = ‖x‖) : ⇑(mk e he) = e :=
  rfl
#align affine_isometry_equiv.coe_mk AffineIsometryEquiv.coe_mk

@[simp]
lemma coe_toAffineEquiv (e : P ≃ᵃⁱ[𝕜] P₂) : ⇑e.toAffineEquiv = e :=
  rfl
#align affine_isometry_equiv.coe_to_affine_equiv AffineIsometryEquiv.coe_toAffineEquiv

lemma toAffineEquiv_injective : Injective (toAffineEquiv : (P ≃ᵃⁱ[𝕜] P₂) → P ≃ᵃ[𝕜] P₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align affine_isometry_equiv.to_affine_equiv_injective AffineIsometryEquiv.toAffineEquiv_injective

@[ext]
lemma ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  toAffineEquiv_injective <| AffineEquiv.ext h
#align affine_isometry_equiv.ext AffineIsometryEquiv.ext

/-- Reinterpret an `AffineIsometryEquiv` as an `AffineIsometry`. -/
def toAffineIsometry : P →ᵃⁱ[𝕜] P₂ :=
  ⟨e.1.toAffineMap, e.2⟩
#align affine_isometry_equiv.to_affine_isometry AffineIsometryEquiv.toAffineIsometry

@[simp]
lemma coe_toAffineIsometry : ⇑e.toAffineIsometry = e :=
  rfl
#align affine_isometry_equiv.coe_to_affine_isometry AffineIsometryEquiv.coe_toAffineIsometry

/-- Construct an affine isometry equivalence by verifying the relation between the map and its
linear part at one base point. Namely, this function takes a map `e : P₁ → P₂`, a linear isometry
equivalence `e' : V₁ ≃ᵢₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`. -/
def mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  { AffineEquiv.mk' e e'.toLinearEquiv p h with norm_map := e'.norm_map }
#align affine_isometry_equiv.mk' AffineIsometryEquiv.mk'

@[simp]
lemma coe_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) : ⇑(mk' e e' p h) = e :=
  rfl
#align affine_isometry_equiv.coe_mk' AffineIsometryEquiv.coe_mk'

@[simp]
lemma linearIsometryEquiv_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) :
    (mk' e e' p h).linearIsometryEquiv = e' := by
  ext
  rfl
#align affine_isometry_equiv.linear_isometry_equiv_mk' AffineIsometryEquiv.linearIsometryEquiv_mk'

end AffineIsometryEquiv

namespace LinearIsometryEquiv

variable (e : V ≃ₗᵢ[𝕜] V₂)

/-- Reinterpret a linear isometry equiv as an affine isometry equiv. -/
def toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂ :=
  { e.toLinearEquiv.toAffineEquiv with norm_map := e.norm_map }
#align linear_isometry_equiv.to_affine_isometry_equiv LinearIsometryEquiv.toAffineIsometryEquiv

@[simp]
lemma coe_toAffineIsometryEquiv : ⇑(e.toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂) = e := by
  rfl
#align linear_isometry_equiv.coe_to_affine_isometry_equiv LinearIsometryEquiv.coe_toAffineIsometryEquiv

@[simp]
lemma toAffineIsometryEquiv_linearIsometryEquiv :
    e.toAffineIsometryEquiv.linearIsometryEquiv = e := by
  ext
  rfl
#align linear_isometry_equiv.to_affine_isometry_equiv_linear_isometry_equiv LinearIsometryEquiv.toAffineIsometryEquiv_linearIsometryEquiv

-- somewhat arbitrary choice of simp direction
@[simp]
lemma toAffineIsometryEquiv_toAffineEquiv :
    e.toAffineIsometryEquiv.toAffineEquiv = e.toLinearEquiv.toAffineEquiv :=
  rfl
#align linear_isometry_equiv.to_affine_isometry_equiv_to_affine_equiv LinearIsometryEquiv.toAffineIsometryEquiv_toAffineEquiv

-- somewhat arbitrary choice of simp direction
@[simp]
lemma toAffineIsometryEquiv_toAffineIsometry :
    e.toAffineIsometryEquiv.toAffineIsometry = e.toLinearIsometry.toAffineIsometry :=
  rfl
#align linear_isometry_equiv.to_affine_isometry_equiv_to_affine_isometry LinearIsometryEquiv.toAffineIsometryEquiv_toAffineIsometry

end LinearIsometryEquiv

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

protected lemma isometry : Isometry e :=
  e.toAffineIsometry.isometry
#align affine_isometry_equiv.isometry AffineIsometryEquiv.isometry

/-- Reinterpret an `AffineIsometryEquiv` as an `IsometryEquiv`. -/
def toIsometryEquiv : P ≃ᵢ P₂ :=
  ⟨e.toAffineEquiv.toEquiv, e.isometry⟩
#align affine_isometry_equiv.to_isometry_equiv AffineIsometryEquiv.toIsometryEquiv

@[simp]
lemma coe_toIsometryEquiv : ⇑e.toIsometryEquiv = e :=
  rfl
#align affine_isometry_equiv.coe_to_isometry_equiv AffineIsometryEquiv.coe_toIsometryEquiv

lemma range_eq_univ (e : P ≃ᵃⁱ[𝕜] P₂) : Set.range e = Set.univ := by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _
#align affine_isometry_equiv.range_eq_univ AffineIsometryEquiv.range_eq_univ

/-- Reinterpret an `AffineIsometryEquiv` as a `Homeomorph`. -/
def toHomeomorph : P ≃ₜ P₂ :=
  e.toIsometryEquiv.toHomeomorph
#align affine_isometry_equiv.to_homeomorph AffineIsometryEquiv.toHomeomorph

@[simp]
lemma coe_toHomeomorph : ⇑e.toHomeomorph = e :=
  rfl
#align affine_isometry_equiv.coe_to_homeomorph AffineIsometryEquiv.coe_toHomeomorph

protected lemma continuous : Continuous e :=
  e.isometry.continuous
#align affine_isometry_equiv.continuous AffineIsometryEquiv.continuous

protected lemma continuousAt {x} : ContinuousAt e x :=
  e.continuous.continuousAt
#align affine_isometry_equiv.continuous_at AffineIsometryEquiv.continuousAt

protected lemma continuousOn {s} : ContinuousOn e s :=
  e.continuous.continuousOn
#align affine_isometry_equiv.continuous_on AffineIsometryEquiv.continuousOn

protected lemma continuousWithinAt {s x} : ContinuousWithinAt e s x :=
  e.continuous.continuousWithinAt
#align affine_isometry_equiv.continuous_within_at AffineIsometryEquiv.continuousWithinAt

variable (𝕜 P)

/-- Identity map as an `AffineIsometryEquiv`. -/
def refl : P ≃ᵃⁱ[𝕜] P :=
  ⟨AffineEquiv.refl 𝕜 P, fun _ => rfl⟩
#align affine_isometry_equiv.refl AffineIsometryEquiv.refl

variable {𝕜 P}

instance : Inhabited (P ≃ᵃⁱ[𝕜] P) :=
  ⟨refl 𝕜 P⟩

@[simp]
lemma coe_refl : ⇑(refl 𝕜 P) = id :=
  rfl
#align affine_isometry_equiv.coe_refl AffineIsometryEquiv.coe_refl

@[simp]
lemma toAffineEquiv_refl : (refl 𝕜 P).toAffineEquiv = AffineEquiv.refl 𝕜 P :=
  rfl
#align affine_isometry_equiv.to_affine_equiv_refl AffineIsometryEquiv.toAffineEquiv_refl

@[simp]
lemma toIsometryEquiv_refl : (refl 𝕜 P).toIsometryEquiv = IsometryEquiv.refl P :=
  rfl
#align affine_isometry_equiv.to_isometry_equiv_refl AffineIsometryEquiv.toIsometryEquiv_refl

@[simp]
lemma toHomeomorph_refl : (refl 𝕜 P).toHomeomorph = Homeomorph.refl P :=
  rfl
#align affine_isometry_equiv.to_homeomorph_refl AffineIsometryEquiv.toHomeomorph_refl

/-- The inverse `AffineIsometryEquiv`. -/
def symm : P₂ ≃ᵃⁱ[𝕜] P :=
  { e.toAffineEquiv.symm with norm_map := e.linearIsometryEquiv.symm.norm_map }
#align affine_isometry_equiv.symm AffineIsometryEquiv.symm

@[simp]
lemma apply_symm_apply (x : P₂) : e (e.symm x) = x :=
  e.toAffineEquiv.apply_symm_apply x
#align affine_isometry_equiv.apply_symm_apply AffineIsometryEquiv.apply_symm_apply

@[simp]
lemma symm_apply_apply (x : P) : e.symm (e x) = x :=
  e.toAffineEquiv.symm_apply_apply x
#align affine_isometry_equiv.symm_apply_apply AffineIsometryEquiv.symm_apply_apply

@[simp]
lemma symm_symm : e.symm.symm = e :=
  ext fun _ => rfl
#align affine_isometry_equiv.symm_symm AffineIsometryEquiv.symm_symm

@[simp]
lemma toAffineEquiv_symm : e.toAffineEquiv.symm = e.symm.toAffineEquiv :=
  rfl
#align affine_isometry_equiv.to_affine_equiv_symm AffineIsometryEquiv.toAffineEquiv_symm

@[simp]
lemma toIsometryEquiv_symm : e.toIsometryEquiv.symm = e.symm.toIsometryEquiv :=
  rfl
#align affine_isometry_equiv.to_isometry_equiv_symm AffineIsometryEquiv.toIsometryEquiv_symm

@[simp]
lemma toHomeomorph_symm : e.toHomeomorph.symm = e.symm.toHomeomorph :=
  rfl
#align affine_isometry_equiv.to_homeomorph_symm AffineIsometryEquiv.toHomeomorph_symm

/-- Composition of `AffineIsometryEquiv`s as an `AffineIsometryEquiv`. -/
def trans (e' : P₂ ≃ᵃⁱ[𝕜] P₃) : P ≃ᵃⁱ[𝕜] P₃ :=
  ⟨e.toAffineEquiv.trans e'.toAffineEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩
#align affine_isometry_equiv.trans AffineIsometryEquiv.trans

@[simp]
lemma coe_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl
#align affine_isometry_equiv.coe_trans AffineIsometryEquiv.coe_trans

@[simp]
lemma trans_refl : e.trans (refl 𝕜 P₂) = e :=
  ext fun _ => rfl
#align affine_isometry_equiv.trans_refl AffineIsometryEquiv.trans_refl

@[simp]
lemma refl_trans : (refl 𝕜 P).trans e = e :=
  ext fun _ => rfl
#align affine_isometry_equiv.refl_trans AffineIsometryEquiv.refl_trans

@[simp]
lemma self_trans_symm : e.trans e.symm = refl 𝕜 P :=
  ext e.symm_apply_apply
#align affine_isometry_equiv.self_trans_symm AffineIsometryEquiv.self_trans_symm

@[simp]
lemma symm_trans_self : e.symm.trans e = refl 𝕜 P₂ :=
  ext e.apply_symm_apply
#align affine_isometry_equiv.symm_trans_self AffineIsometryEquiv.symm_trans_self

@[simp]
lemma coe_symm_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) :
    ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
  rfl
#align affine_isometry_equiv.coe_symm_trans AffineIsometryEquiv.coe_symm_trans

lemma trans_assoc (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P₄) :
    ePP₂.trans (eP₂G.trans eGG') = (ePP₂.trans eP₂G).trans eGG' :=
  rfl
#align affine_isometry_equiv.trans_assoc AffineIsometryEquiv.trans_assoc

/-- The group of affine isometries of a `NormedAddTorsor`, `P`. -/
instance instGroup : Group (P ≃ᵃⁱ[𝕜] P) where
  mul e₁ e₂ := e₂.trans e₁
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc _ _ _ := trans_assoc _ _ _
  mul_left_inv := self_trans_symm

@[simp]
lemma coe_one : ⇑(1 : P ≃ᵃⁱ[𝕜] P) = id :=
  rfl
#align affine_isometry_equiv.coe_one AffineIsometryEquiv.coe_one

@[simp]
lemma coe_mul (e e' : P ≃ᵃⁱ[𝕜] P) : ⇑(e * e') = e ∘ e' :=
  rfl
#align affine_isometry_equiv.coe_mul AffineIsometryEquiv.coe_mul

@[simp]
lemma coe_inv (e : P ≃ᵃⁱ[𝕜] P) : ⇑e⁻¹ = e.symm :=
  rfl
#align affine_isometry_equiv.coe_inv AffineIsometryEquiv.coe_inv

@[simp]
lemma map_vadd (p : P) (v : V) : e (v +ᵥ p) = e.linearIsometryEquiv v +ᵥ e p :=
  e.toAffineIsometry.map_vadd p v
#align affine_isometry_equiv.map_vadd AffineIsometryEquiv.map_vadd

@[simp]
lemma map_vsub (p1 p2 : P) : e.linearIsometryEquiv (p1 -ᵥ p2) = e p1 -ᵥ e p2 :=
  e.toAffineIsometry.map_vsub p1 p2
#align affine_isometry_equiv.map_vsub AffineIsometryEquiv.map_vsub

@[simp]
lemma dist_map (x y : P) : dist (e x) (e y) = dist x y :=
  e.toAffineIsometry.dist_map x y
#align affine_isometry_equiv.dist_map AffineIsometryEquiv.dist_map

@[simp]
lemma edist_map (x y : P) : edist (e x) (e y) = edist x y :=
  e.toAffineIsometry.edist_map x y
#align affine_isometry_equiv.edist_map AffineIsometryEquiv.edist_map

protected lemma bijective : Bijective e :=
  e.1.bijective
#align affine_isometry_equiv.bijective AffineIsometryEquiv.bijective

protected lemma injective : Injective e :=
  e.1.injective
#align affine_isometry_equiv.injective AffineIsometryEquiv.injective

protected lemma surjective : Surjective e :=
  e.1.surjective
#align affine_isometry_equiv.surjective AffineIsometryEquiv.surjective

-- @[simp] Porting note (#10618): simp can prove this
lemma map_eq_iff {x y : P} : e x = e y ↔ x = y :=
  e.injective.eq_iff
#align affine_isometry_equiv.map_eq_iff AffineIsometryEquiv.map_eq_iff

lemma map_ne {x y : P} (h : x ≠ y) : e x ≠ e y :=
  e.injective.ne h
#align affine_isometry_equiv.map_ne AffineIsometryEquiv.map_ne

protected lemma lipschitz : LipschitzWith 1 e :=
  e.isometry.lipschitz
#align affine_isometry_equiv.lipschitz AffineIsometryEquiv.lipschitz

protected lemma antilipschitz : AntilipschitzWith 1 e :=
  e.isometry.antilipschitz
#align affine_isometry_equiv.antilipschitz AffineIsometryEquiv.antilipschitz

@[simp]
lemma ediam_image (s : Set P) : EMetric.diam (e '' s) = EMetric.diam s :=
  e.isometry.ediam_image s
#align affine_isometry_equiv.ediam_image AffineIsometryEquiv.ediam_image

@[simp]
lemma diam_image (s : Set P) : Metric.diam (e '' s) = Metric.diam s :=
  e.isometry.diam_image s
#align affine_isometry_equiv.diam_image AffineIsometryEquiv.diam_image

variable {α : Type*} [TopologicalSpace α]

@[simp]
lemma comp_continuousOn_iff {f : α → P} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.isometry.comp_continuousOn_iff
#align affine_isometry_equiv.comp_continuous_on_iff AffineIsometryEquiv.comp_continuousOn_iff

@[simp]
lemma comp_continuous_iff {f : α → P} : Continuous (e ∘ f) ↔ Continuous f :=
  e.isometry.comp_continuous_iff
#align affine_isometry_equiv.comp_continuous_iff AffineIsometryEquiv.comp_continuous_iff

section Constructions

variable (𝕜)

/-- The map `v ↦ v +ᵥ p` as an affine isometric equivalence between `V` and `P`. -/
def vaddConst (p : P) : V ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.vaddConst 𝕜 p with norm_map := fun _ => rfl }
#align affine_isometry_equiv.vadd_const AffineIsometryEquiv.vaddConst

variable {𝕜}

@[simp]
lemma coe_vaddConst (p : P) : ⇑(vaddConst 𝕜 p) = fun v => v +ᵥ p :=
  rfl
#align affine_isometry_equiv.coe_vadd_const AffineIsometryEquiv.coe_vaddConst

@[simp]
lemma coe_vaddConst' (p : P) : ↑(AffineEquiv.vaddConst 𝕜 p) = fun v => v +ᵥ p :=
  rfl

@[simp]
lemma coe_vaddConst_symm (p : P) : ⇑(vaddConst 𝕜 p).symm = fun p' => p' -ᵥ p :=
  rfl
#align affine_isometry_equiv.coe_vadd_const_symm AffineIsometryEquiv.coe_vaddConst_symm

@[simp]
lemma vaddConst_toAffineEquiv (p : P) :
    (vaddConst 𝕜 p).toAffineEquiv = AffineEquiv.vaddConst 𝕜 p :=
  rfl
#align affine_isometry_equiv.vadd_const_to_affine_equiv AffineIsometryEquiv.vaddConst_toAffineEquiv

variable (𝕜)

/-- `p' ↦ p -ᵥ p'` as an affine isometric equivalence. -/
def constVSub (p : P) : P ≃ᵃⁱ[𝕜] V :=
  { AffineEquiv.constVSub 𝕜 p with norm_map := norm_neg }
#align affine_isometry_equiv.const_vsub AffineIsometryEquiv.constVSub

variable {𝕜}

@[simp]
lemma coe_constVSub (p : P) : ⇑(constVSub 𝕜 p) = (p -ᵥ ·) :=
  rfl
#align affine_isometry_equiv.coe_const_vsub AffineIsometryEquiv.coe_constVSub

@[simp]
lemma symm_constVSub (p : P) :
    (constVSub 𝕜 p).symm =
      (LinearIsometryEquiv.neg 𝕜).toAffineIsometryEquiv.trans (vaddConst 𝕜 p) := by
  ext
  rfl
#align affine_isometry_equiv.symm_const_vsub AffineIsometryEquiv.symm_constVSub

variable (𝕜 P)

/-- Translation by `v` (that is, the map `p ↦ v +ᵥ p`) as an affine isometric automorphism of `P`.
-/
def constVAdd (v : V) : P ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.constVAdd 𝕜 P v with norm_map := fun _ => rfl }
#align affine_isometry_equiv.const_vadd AffineIsometryEquiv.constVAdd

variable {𝕜 P}

@[simp]
lemma coe_constVAdd (v : V) : ⇑(constVAdd 𝕜 P v : P ≃ᵃⁱ[𝕜] P) = (v +ᵥ ·) :=
  rfl
#align affine_isometry_equiv.coe_const_vadd AffineIsometryEquiv.coe_constVAdd

@[simp]
lemma constVAdd_zero : constVAdd 𝕜 P (0 : V) = refl 𝕜 P :=
  ext <| zero_vadd V
#align affine_isometry_equiv.const_vadd_zero AffineIsometryEquiv.constVAdd_zero

/-- The map `g` from `V` to `V₂` corresponding to a map `f` from `P` to `P₂`, at a base point `p`,
is an isometry if `f` is one. -/
theorem vadd_vsub {f : P → P₂} (hf : Isometry f) {p : P} {g : V → V₂}
    (hg : ∀ v, g v = f (v +ᵥ p) -ᵥ f p) : Isometry g := by
  convert (vaddConst 𝕜 (f p)).symm.isometry.comp (hf.comp (vaddConst 𝕜 p).isometry)
  exact funext hg
#align affine_isometry_equiv.vadd_vsub AffineIsometryEquiv.vadd_vsub

variable (𝕜)

/-- Point reflection in `x` as an affine isometric automorphism. -/
def pointReflection (x : P) : P ≃ᵃⁱ[𝕜] P :=
  (constVSub 𝕜 x).trans (vaddConst 𝕜 x)
#align affine_isometry_equiv.point_reflection AffineIsometryEquiv.pointReflection

variable {𝕜}

lemma pointReflection_apply (x y : P) : (pointReflection 𝕜 x) y = x -ᵥ y +ᵥ x :=
  rfl
#align affine_isometry_equiv.point_reflection_apply AffineIsometryEquiv.pointReflection_apply

@[simp]
lemma pointReflection_toAffineEquiv (x : P) :
    (pointReflection 𝕜 x).toAffineEquiv = AffineEquiv.pointReflection 𝕜 x :=
  rfl
#align affine_isometry_equiv.point_reflection_to_affine_equiv AffineIsometryEquiv.pointReflection_toAffineEquiv

@[simp]
lemma pointReflection_self (x : P) : pointReflection 𝕜 x x = x :=
  AffineEquiv.pointReflection_self 𝕜 x
#align affine_isometry_equiv.point_reflection_self AffineIsometryEquiv.pointReflection_self

lemma pointReflection_involutive (x : P) : Function.Involutive (pointReflection 𝕜 x) :=
  Equiv.pointReflection_involutive x
#align affine_isometry_equiv.point_reflection_involutive AffineIsometryEquiv.pointReflection_involutive

@[simp]
lemma pointReflection_symm (x : P) : (pointReflection 𝕜 x).symm = pointReflection 𝕜 x :=
  toAffineEquiv_injective <| AffineEquiv.pointReflection_symm 𝕜 x
#align affine_isometry_equiv.point_reflection_symm AffineIsometryEquiv.pointReflection_symm

@[simp]
lemma dist_pointReflection_fixed (x y : P) : dist (pointReflection 𝕜 x y) x = dist y x := by
  rw [← (pointReflection 𝕜 x).dist_map y x, pointReflection_self]
#align affine_isometry_equiv.dist_point_reflection_fixed AffineIsometryEquiv.dist_pointReflection_fixed

set_option linter.deprecated false in
lemma dist_pointReflection_self' (x y : P) : dist (pointReflection 𝕜 x y) y = ‖bit0 (x -ᵥ y)‖ :=
  by rw [pointReflection_apply, dist_eq_norm_vsub V, vadd_vsub_assoc, bit0]
#align affine_isometry_equiv.dist_point_reflection_self' AffineIsometryEquiv.dist_pointReflection_self'

set_option linter.deprecated false in
lemma dist_pointReflection_self (x y : P) :
    dist (pointReflection 𝕜 x y) y = ‖(2 : 𝕜)‖ * dist x y := by
  rw [dist_pointReflection_self', ← two_smul' 𝕜 (x -ᵥ y), norm_smul, ← dist_eq_norm_vsub V]
#align affine_isometry_equiv.dist_point_reflection_self AffineIsometryEquiv.dist_pointReflection_self

lemma pointReflection_fixed_iff [Invertible (2 : 𝕜)] {x y : P} :
    pointReflection 𝕜 x y = y ↔ y = x :=
  AffineEquiv.pointReflection_fixed_iff_of_module 𝕜
#align affine_isometry_equiv.point_reflection_fixed_iff AffineIsometryEquiv.pointReflection_fixed_iff

variable [NormedSpace ℝ V]

lemma dist_pointReflection_self_real (x y : P) : dist (pointReflection ℝ x y) y = 2 * dist x y :=
  by rw [dist_pointReflection_self, Real.norm_two]
#align affine_isometry_equiv.dist_point_reflection_self_real AffineIsometryEquiv.dist_pointReflection_self_real

@[simp]
lemma pointReflection_midpoint_left (x y : P) : pointReflection ℝ (midpoint ℝ x y) x = y :=
  AffineEquiv.pointReflection_midpoint_left x y
#align affine_isometry_equiv.point_reflection_midpoint_left AffineIsometryEquiv.pointReflection_midpoint_left

@[simp]
lemma pointReflection_midpoint_right (x y : P) : pointReflection ℝ (midpoint ℝ x y) y = x :=
  AffineEquiv.pointReflection_midpoint_right x y
#align affine_isometry_equiv.point_reflection_midpoint_right AffineIsometryEquiv.pointReflection_midpoint_right

end Constructions

end AffineIsometryEquiv

/-- If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
theorem AffineMap.continuous_linear_iff {f : P →ᵃ[𝕜] P₂} : Continuous f.linear ↔ Continuous f := by
  inhabit P
  have :
    (f.linear : V → V₂) =
      (AffineIsometryEquiv.vaddConst 𝕜 <| f default).toHomeomorph.symm ∘
        f ∘ (AffineIsometryEquiv.vaddConst 𝕜 default).toHomeomorph := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']
#align affine_map.continuous_linear_iff AffineMap.continuous_linear_iff

/-- If `f` is an affine map, then its linear part is an open map iff `f` is an open map. -/
theorem AffineMap.isOpenMap_linear_iff {f : P →ᵃ[𝕜] P₂} : IsOpenMap f.linear ↔ IsOpenMap f := by
  inhabit P
  have :
    (f.linear : V → V₂) =
      (AffineIsometryEquiv.vaddConst 𝕜 <| f default).toHomeomorph.symm ∘
        f ∘ (AffineIsometryEquiv.vaddConst 𝕜 default).toHomeomorph := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_isOpenMap_iff, Homeomorph.comp_isOpenMap_iff']
#align affine_map.is_open_map_linear_iff AffineMap.isOpenMap_linear_iff

attribute [local instance] AffineSubspace.nonempty_map -- Porting note: removed `fails_quickly`

namespace AffineSubspace

/-- An affine subspace is isomorphic to its image under an injective affine map.
This is the affine version of `Submodule.equivMapOfInjective`.
-/
@[simps linear, simps! toFun]
noncomputable def equivMapOfInjective (E : AffineSubspace 𝕜 P₁) [Nonempty E] (φ : P₁ →ᵃ[𝕜] P₂)
    (hφ : Function.Injective φ) : E ≃ᵃ[𝕜] E.map φ :=
  { Equiv.Set.image _ (E : Set P₁) hφ with
    linear :=
      (E.direction.equivMapOfInjective φ.linear (φ.linear_injective_iff.mpr hφ)).trans
        (LinearEquiv.ofEq _ _ (AffineSubspace.map_direction _ _).symm)
    map_vadd' := fun p v => Subtype.ext <| φ.map_vadd p v }
#align affine_subspace.equiv_map_of_injective AffineSubspace.equivMapOfInjective

/-- Restricts an affine isometry to an affine isometry equivalence between a nonempty affine
subspace `E` and its image.

This is an isometry version of `AffineSubspace.equivMap`, having a stronger premise and a stronger
conclusion.
-/
noncomputable def isometryEquivMap (φ : P₁' →ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁') [Nonempty E] :
    E ≃ᵃⁱ[𝕜] E.map φ.toAffineMap :=
  ⟨E.equivMapOfInjective φ.toAffineMap φ.injective, fun _ => φ.norm_map _⟩
#align affine_subspace.isometry_equiv_map AffineSubspace.isometryEquivMap

@[simp]
lemma isometryEquivMap.apply_symm_apply {E : AffineSubspace 𝕜 P₁'} [Nonempty E]
    {φ : P₁' →ᵃⁱ[𝕜] P₂} (x : E.map φ.toAffineMap) : φ ((E.isometryEquivMap φ).symm x) = x :=
  congr_arg Subtype.val <| (E.isometryEquivMap φ).apply_symm_apply _
#align affine_subspace.isometry_equiv_map.apply_symm_apply AffineSubspace.isometryEquivMap.apply_symm_apply

@[simp]
lemma isometryEquivMap.coe_apply (φ : P₁' →ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁') [Nonempty E]
    (g : E) : ↑(E.isometryEquivMap φ g) = φ g :=
  rfl
#align affine_subspace.isometry_equiv_map.coe_apply AffineSubspace.isometryEquivMap.coe_apply

@[simp]
lemma isometryEquivMap.toAffineMap_eq (φ : P₁' →ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁')
    [Nonempty E] :
    (E.isometryEquivMap φ).toAffineMap = E.equivMapOfInjective φ.toAffineMap φ.injective :=
  rfl
#align affine_subspace.isometry_equiv_map.to_affine_map_eq AffineSubspace.isometryEquivMap.toAffineMap_eq

end AffineSubspace
