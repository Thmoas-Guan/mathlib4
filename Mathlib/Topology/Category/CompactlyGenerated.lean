/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Topology.Instances.ENat
/-!

# Compactly generated topological spaces

This file defines the category of compactly generated topological spaces. These are spaces `X` such
that a map `f : X → Y` is continuous whenever the composition `S → X → Y` is continuous for all
compact Hausdorff spaces `S` mapping continuously to `X`.

## TODO

* `CompactlyGenerated` is a reflective subcategory of `TopCat`.
* `CompactlyGenerated` is cartesian closed.
* Every first-countable space is `u`-compactly generated for every universe `u`.
-/

attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

universe u w

open CategoryTheory Topology TopologicalSpace

/--
The compactly generated topology on a topological space `X`. This is the finest topology
which makes all maps from compact Hausdorff spaces to `X`, which are continuous for the original
topology, continuous.

Note: this definition should be used with an explicit universe parameter `u` for the size of the
compact Hausdorff spaces mapping to `X`.
-/
def TopologicalSpace.compactlyGenerated (X : Type w) [TopologicalSpace X] : TopologicalSpace X :=
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  coinduced f inferInstance

lemma continuous_from_compactlyGenerated {X : Type w} [TopologicalSpace X]
    {Y : Type*} [t : TopologicalSpace Y] (f : X → Y)
      (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) :
        Continuous[compactlyGenerated.{u} X, t] f := by
  rw [continuous_coinduced_dom]
  continuity

/--
A topological space `X` is compactly generated if its topology is finer than (and thus equal to)
the compactly generated topology, i.e. it is coinduced by the continuous maps from compact
Hausdorff spaces to `X`.
-/
class CompactlyGeneratedSpace (X : Type w) [t : TopologicalSpace X] : Prop where
  /-- The topology of `X` is finer than the compactly generated topology. -/
  le_compactlyGenerated : t ≤ compactlyGenerated.{u} X

lemma eq_compactlyGenerated {X : Type w} [t : TopologicalSpace X] [CompactlyGeneratedSpace.{u} X] :
    t = compactlyGenerated.{u} X := by
  apply le_antisymm
  · exact CompactlyGeneratedSpace.le_compactlyGenerated
  · simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
      Sigma.forall]
    exact fun S f ↦ f.2

instance (X : Type w) [t : TopologicalSpace X] [DiscreteTopology X] :
    CompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    rw [DiscreteTopology.eq_bot (t := t)]
    exact bot_le

lemma continuous_from_compactlyGeneratedSpace {X : Type w} [TopologicalSpace X]
    [CompactlyGeneratedSpace.{u} X] {Y : Type*} [TopologicalSpace Y] (f : X → Y)
      (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) : Continuous f := by
  apply continuous_le_dom CompactlyGeneratedSpace.le_compactlyGenerated
  exact continuous_from_compactlyGenerated f h

lemma compactlyGeneratedSpace_of_continuous_maps {X : Type w} [t : TopologicalSpace X]
    (h : ∀ {Y : Type w} [tY : TopologicalSpace Y] (f : X → Y),
      (∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) → Continuous f) :
        CompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    suffices Continuous[t, compactlyGenerated.{u} X] (id : X → X) by
      rwa [← continuous_id_iff_le]
    apply h (tY := compactlyGenerated.{u} X)
    intro S g
    let f : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
    suffices ∀ (i : (T : CompHaus.{u}) × C(T, X)),
      Continuous[inferInstance, compactlyGenerated X] (fun (a : i.fst) ↦ f ⟨i, a⟩) from this ⟨S, g⟩
    rw [← @continuous_sigma_iff]
    apply continuous_coinduced_rng

theorem compactlyGeneratedSpace_of_isClosed {X : Type u} [TopologicalSpace X]
    (h : ∀ (s : Set X), (∀ {K : Type w} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsClosed (f ⁻¹' s)) → IsClosed s) :
    CompactlyGeneratedSpace.{w} X := by
  refine compactlyGeneratedSpace_of_continuous_maps fun f h' ↦
    continuous_iff_isClosed.2 fun t ht ↦ h _ ?_
  intro K _ _ _ g hg
  exact ht.preimage (h' (CompHaus.of K) { toFun := g, continuous_toFun := hg })

theorem compactlyGeneratedSpace_of_isOpen {X : Type u} [TopologicalSpace X]
    (h : ∀ (s : Set X), (∀ {K : Type w} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsOpen (f ⁻¹' s)) → IsOpen s) :
    CompactlyGeneratedSpace.{w} X := by
  refine compactlyGeneratedSpace_of_continuous_maps fun f h' ↦
    continuous_def.2 fun t ht ↦ h _ ?_
  intro K _ _ _ g hg
  exact ht.preimage (h' (CompHaus.of K) { toFun := g, continuous_toFun := hg })

theorem CompactlyGeneratedSpace.isClosed {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace.{w} X] {s : Set X}
    (hs : ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K)) : IsClosed s := by
  rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isClosed_coinduced,
    isClosed_sigma_iff]
  rintro ⟨K, f⟩
  change IsClosed (f ⁻¹' s)
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range f.continuous)).preimage f.continuous

theorem CompactlyGeneratedSpace.isOpen {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace.{w} X] {s : Set X}
    (hs : ∀ ⦃K⦄, IsCompact K → IsOpen (s ∩ K)) : IsOpen s := by
  rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isOpen_coinduced,
    isOpen_sigma_iff]
  rintro ⟨K, f⟩
  change IsOpen (f ⁻¹' s)
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range f.continuous)).preimage f.continuous

instance {X : Type*} [TopologicalSpace X] [SequentialSpace X] : CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦
    SequentialSpace.isClosed_of_seq _ fun u p hu hup ↦ ?_
  let g : ULift.{u_2} ENat → X := (compactSequence u p) ∘ ULift.down
  change ⊤ ∈ g ⁻¹' s
  apply IsClosed.mem_of_tendsto _ ((continuous_uLift_up.tendsto ⊤).comp ENat.tendsto_coe_atTop)
  · simp only [Set.mem_preimage, Filter.eventually_atTop, ge_iff_le]
    exact ⟨0, fun b _ ↦ hu b⟩
  · have : CompactSpace (ULift.{u_2} ENat) := ULift.closedEmbedding_down.compactSpace
    exact h g ((continuous_compactSequence u p hup).comp continuous_uLift_down)

theorem IsClosed.isClosedMap_subtype_val {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsClosed s) : IsClosedMap (@Subtype.val X s) :=
  hs.closedEmbedding_subtype_val.isClosedMap

theorem compactlyGeneratedSpace_of_isClosed_of_t2 {X : Type u} [TopologicalSpace X] [T2Space X]
    (h : ∀ s, (∀ (K : Set X), IsCompact K → IsClosed (s ∩ K)) → IsClosed s) :
    CompactlyGeneratedSpace.{u} X := by
  refine compactlyGeneratedSpace_of_isClosed fun s hs ↦ h s fun K hK ↦ ?_
  rw [Set.inter_comm, ← Subtype.image_preimage_coe]
  apply hK.isClosed.isClosedMap_subtype_val
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs Subtype.val continuous_subtype_val

instance {X : Type u} [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [T2Space X] :
    CompactlyGeneratedSpace.{u} X := by
  refine compactlyGeneratedSpace_of_isClosed_of_t2 fun s h ↦ ?_
  rw [isClosed_iff_forall_filter]
  intro x ℱ hℱ₁ hℱ₂ hℱ₃
  rcases exists_compact_mem_nhds x with ⟨K, hK, K_mem⟩
  exact Set.mem_of_mem_inter_left <| isClosed_iff_forall_filter.1 (h _ hK) x ℱ hℱ₁
    (Filter.inf_principal ▸ le_inf hℱ₂ (le_trans hℱ₃ <| Filter.le_principal_iff.2 K_mem)) hℱ₃

/-- The type of `u`-compactly generated `w`-small topological spaces. -/
structure CompactlyGenerated where
  /-- The underlying topological space of an object of `CompactlyGenerated`. -/
  toTop : TopCat.{w}
  /-- The underlying topological space is compactly generated. -/
  [is_compactly_generated : CompactlyGeneratedSpace.{u} toTop]

namespace CompactlyGenerated

instance : Inhabited CompactlyGenerated.{u, w} :=
  ⟨{ toTop := { α := ULift (Fin 37) } }⟩

instance : CoeSort CompactlyGenerated Type* :=
  ⟨fun X => X.toTop⟩

attribute [instance] is_compactly_generated

instance : Category.{w, w+1} CompactlyGenerated.{u, w} :=
  InducedCategory.category toTop

instance : ConcreteCategory.{w} CompactlyGenerated.{u, w} :=
  InducedCategory.concreteCategory _

variable (X : Type w) [TopologicalSpace X] [CompactlyGeneratedSpace.{u} X]

/-- Constructor for objects of the category `CompactlyGenerated`. -/
def of : CompactlyGenerated.{u, w} where
  toTop := TopCat.of X
  is_compactly_generated := ‹_›

/-- The fully faithful embedding of `CompactlyGenerated` in `TopCat`. -/
@[simps!]
def compactlyGeneratedToTop : CompactlyGenerated.{u, w} ⥤ TopCat.{w} :=
  inducedFunctor _

/-- `compactlyGeneratedToTop` is fully faithful. -/
def fullyFaithfulCompactlyGeneratedToTop : compactlyGeneratedToTop.{u, w}.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : compactlyGeneratedToTop.{u, w}.Full := fullyFaithfulCompactlyGeneratedToTop.full

instance : compactlyGeneratedToTop.{u, w}.Faithful := fullyFaithfulCompactlyGeneratedToTop.faithful

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv]
def isoOfHomeo {X Y : CompactlyGenerated.{u, w}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ⟨f, f.continuous⟩
  inv := ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso {X Y : CompactlyGenerated.{u, w}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous

/-- The equivalence between isomorphisms in `CompactlyGenerated` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo {X Y : CompactlyGenerated.{u, w}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl

end CompactlyGenerated
