/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Topological entropy of the image of a set under a semiconjugacy
The main lemma is `image_entropy`/`image_entropy'`: the entropy of the image of a set by a
semiconjugacy is the entropy of the set for the inverse image filter. This lemma needs very little
hypotheses, and generalizes many important results.

First, a uniformly continuous semiconjugacy descreases the entropy of subsets:
`image_entropy_uniformContinuous_le`, `image_entropy'_uniformContinuous_le`.

Second, the entropy of `Set.univ` for a subsystem is equal to the entropy of the subset, which
justifies the implementation of the entropy of a subset: `subset_restriction_entropy`.

TODO: Investigate the consequences of `image_entropy` for embeddings.

TODO: There are some interesting related results about the entropy of fibered systems.

/- TODO : Is it possible to have an implicit instance of UniformSpace X instead of an explicit
  argument ?-/

/- TODO : Try to get a lower bound on the entropy of the image. What is a right hypothesis on φ ?
  Of course UX ≤ UniformSpace.comap φ UY works, but are there "natural" statements
  (proper map...) ? -/
-/

namespace Dynamics

open Function Set Uniformity UniformSpace

variable {X Y : Type*} {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T)

lemma dynNet_preimage {F : Set X} {V : Set (Y × Y)} {n : ℕ} {t : Finset Y}
    (h' : IsDynNetOf T (φ '' F) V n t) :
    ∃ s : Finset X, IsDynNetOf S F ((Prod.map φ φ) ⁻¹' V) n s ∧ t.card ≤ s.card := by
  classical
  rcases t.eq_empty_or_nonempty with (rfl | t_nemp)
  . use ∅
    simp [dynNet_by_empty S F ((Prod.map φ φ) ⁻¹' V) n]
  have _ : Nonempty X := Nonempty.to_type (Nonempty.of_image (Nonempty.mono h'.1 t_nemp))
  have : ∀ y ∈ t, ∃ x ∈ F, φ x = y := fun y y_t ↦ h'.1 y_t
  choose! f f_section using this
  use Finset.image f t
  split_ands
  . intro y y_ft
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at y_ft
    rcases y_ft with ⟨x, x_t, y_fx⟩
    rw [← y_fx]
    exact (f_section x x_t).1
  . rw [Finset.coe_image, ← preimage_of_dynamical_uni h V n]
    apply (InjOn.pairwiseDisjoint_image _).2
    · intro x x_t y y_t x_y inter_balls inter_x inter_y z z_inter
      specialize inter_x z_inter
      specialize inter_y z_inter
      simp only [ball, comp_apply, mem_preimage, Prod.map_apply] at inter_x inter_y
      rw [(f_section x x_t).2] at inter_x
      rw [(f_section y y_t).2] at inter_y
      replace inter_x : {φ z} ⊆ ball x (DynamicalUni T V n) := singleton_subset_iff.2 inter_x
      replace inter_y : {φ z} ⊆ ball y (DynamicalUni T V n) := singleton_subset_iff.2 inter_y
      have := h'.2 x_t y_t x_y inter_x inter_y
      simp at this
    · intro x x_t y y_t fx_fy
      rw [← (f_section x x_t).2, ← (f_section y y_t).2, fx_fy]
  . apply le_trans (b := (Finset.image (φ ∘ f) t).card)
    · refine Finset.card_mono (fun x x_t ↦ ?_)
      rw [← (f_section x x_t).2]
      exact Finset.mem_image_of_mem (φ ∘ f) x_t
    · rw [← Finset.image_image]
      exact Finset.card_image_le

lemma dynCover_preimage {F : Set X} {V : Set (Y × Y)} (V_symm : SymmetricRel V) {n : ℕ}
    {t : Finset Y} (h' : IsDynCoverOf T (φ '' F) V n t) :
    ∃ s : Finset X, IsDynCoverOf S F ((Prod.map φ φ) ⁻¹' (V ○ V)) n s ∧ s.card ≤ t.card := by
  classical
  rcases isEmpty_or_nonempty X with (_ | _)
  . use ∅
    simp [eq_empty_of_isEmpty F]
  rcases dynCover_elim h' with ⟨s, s_cover, s_card, s_inter⟩
  replace s_inter := fun (x : Y) (h : x ∈ s) ↦ nonempty_def.1 (s_inter x h)
  choose! g gs_cover using s_inter
  have : ∀ y ∈ φ '' F, ∃ x ∈ F, φ x = y := fun y a ↦ a
  choose! f f_section using this
  use Finset.image f (Finset.image g s)
  apply And.intro _ (le_trans Finset.card_image_le (le_trans Finset.card_image_le s_card))
  intro x x_F
  rw [← preimage_of_dynamical_uni h (V ○ V) n, mem_iUnion₂]
  simp only [Finset.coe_image, mem_image, Finset.mem_coe, exists_exists_and_eq_and, ball,
    mem_preimage, Prod.map_apply, exists_prop]
  specialize s_cover (mem_image_of_mem φ x_F)
  simp only [Finset.mem_coe, mem_iUnion, exists_prop] at s_cover
  rcases s_cover with ⟨y, y_s, hy⟩
  use y, y_s
  specialize gs_cover y y_s
  rw [(f_section (g y) gs_cover.2).2]
  exact (dynamical_uni_of_comp T V V n)
    (mem_comp_of_mem_ball (dynamical_uni_of_symm T V_symm n) gs_cover.1 hy)

lemma netMaxcard_image_le (F : Set X) (V : Set (Y × Y)) (n : ℕ) :
    netMaxcard T (φ '' F) V n ≤ netMaxcard S F ((Prod.map φ φ) ⁻¹' V) n := by
  rcases lt_or_eq_of_le (le_top (a := netMaxcard T (φ '' F) V n)) with (h' | h')
  . rcases (netMaxcard_finite_iff T (φ '' F) V n).1 h' with ⟨t, t_net, t_card⟩
    rcases dynNet_preimage h t_net with ⟨s, s_net, s_card⟩
    rw [← t_card]
    exact le_trans (WithTop.coe_le_coe.2 s_card) (card_le_netMaxcard s_net)
  . apply le_of_le_of_eq le_top (Eq.symm _)
    apply (netMaxcard_infinite_iff S F ((Prod.map φ φ) ⁻¹' V) n).2
    intro k
    rcases (netMaxcard_infinite_iff T (φ '' F) V n).1 h' k with ⟨t, t_net, t_card⟩
    rcases dynNet_preimage h t_net with ⟨s, s_net, s_card⟩
    use s
    exact ⟨s_net, le_trans t_card s_card⟩

lemma le_coverMincard_image (F : Set X) {V : Set (Y × Y)} (V_symm : SymmetricRel V) (n : ℕ) :
    coverMincard S F ((Prod.map φ φ) ⁻¹' (V ○ V)) n ≤ coverMincard T (φ '' F) V n := by
  rcases eq_top_or_lt_top (coverMincard T (φ '' F) V n) with (h' | h')
  . exact h' ▸ le_top
  . rcases (coverMincard_finite_iff T (φ '' F) V n).1 h' with ⟨t, t_cover, t_card⟩
    rcases dynCover_preimage h V_symm t_cover with ⟨s, s_cover, s_card⟩
    rw [← t_card]
    exact le_trans (coverMincard_le_card s_cover) (WithTop.coe_le_coe.2 s_card)

open ENNReal Filter

lemma netEntropyInfUni_image_le (F : Set X) (V : Set (Y × Y)) :
    netEntropyInfUni T (φ '' F) V ≤ netEntropyInfUni S F ((Prod.map φ φ) ⁻¹' V) :=
  liminf_le_liminf <| eventually_of_forall
    fun n ↦ EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (netMaxcard_image_le h F V n))

lemma netEntropySupUni_image_le (F : Set X) (V : Set (Y × Y)) :
    netEntropySupUni T (φ '' F) V ≤ netEntropySupUni S F ((Prod.map φ φ) ⁻¹' V) :=
  limsup_le_limsup <| eventually_of_forall
    fun n ↦ EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (netMaxcard_image_le h F V n))

lemma le_coverEntropyInfUni_image (F : Set X) {V : Set (Y × Y)} (V_symm : SymmetricRel V) :
    coverEntropyInfUni S F ((Prod.map φ φ) ⁻¹' (V ○ V)) ≤ coverEntropyInfUni T (φ '' F) V :=
  liminf_le_liminf <| eventually_of_forall
    fun n ↦ EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (le_coverMincard_image h F V_symm n))

lemma le_coverEntropySupUni_image (F : Set X) {V : Set (Y × Y)} (V_symm : SymmetricRel V) :
    coverEntropySupUni S F ((Prod.map φ φ) ⁻¹' (V ○ V)) ≤ coverEntropySupUni T (φ '' F) V :=
  limsup_le_limsup <| eventually_of_forall
    fun n ↦ EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (le_coverMincard_image h F V_symm n))

theorem coverEntropyInf_image {X Y : Type*} (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropyInf T (φ '' F) = @coverEntropyInf X (comap φ u) S F := by
  apply le_antisymm
  . rw [← netEntropyInf_eq_coverEntropyInf T (φ '' F),
      ← @netEntropyInf_eq_coverEntropyInf X (comap φ u) S F]
    refine iSup₂_le fun V V_uni ↦ ?_
    apply le_trans (netEntropyInfUni_image_le h F V)
    apply @netEntropyInfUni_le_netEntropyInf X (comap φ u) S F
    rw [uniformity_comap φ, mem_comap]
    use V
  . refine iSup₂_le fun U U_uni ↦ ?_
    simp only [uniformity_comap φ, mem_comap] at U_uni
    rcases U_uni with ⟨V, V_uni, V_sub⟩
    rcases comp_symm_mem_uniformity_sets V_uni with ⟨W, W_uni, W_symm, W_V⟩
    apply le_trans _ (le_iSup₂ W W_uni)
    apply le_trans _ (le_coverEntropyInfUni_image h F W_symm)
    exact (coverEntropyInfUni_antitone S F) (le_trans (preimage_mono W_V) V_sub)

theorem coverEntropySup_image {X Y : Type*} (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropySup T (φ '' F) = @coverEntropySup X (comap φ u) S F := by
  apply le_antisymm
  . rw [← netEntropySup_eq_coverEntropySup T (φ '' F),
      ← @netEntropySup_eq_coverEntropySup X (comap φ u) S F]
    refine iSup₂_le fun V V_uni ↦ ?_
    apply le_trans (netEntropySupUni_image_le h F V)
    apply @netEntropySupUni_le_netEntropySup X (comap φ u) S F
    rw [uniformity_comap φ, mem_comap]
    use V
  . refine iSup₂_le fun U U_uni ↦ ?_
    simp only [uniformity_comap φ, mem_comap] at U_uni
    rcases U_uni with ⟨V, V_uni, V_sub⟩
    rcases comp_symm_mem_uniformity_sets V_uni with ⟨W, W_uni, W_symm, W_V⟩
    apply le_trans _ (le_iSup₂ W W_uni)
    apply le_trans _ (le_coverEntropySupUni_image h F W_symm)
    exact (coverEntropySupUni_antitone S F) (le_trans (preimage_mono W_V) V_sub)

lemma coverEntropyInf_image_le_of_uniformContinuous {X Y : Type*} [UniformSpace X]
    [UniformSpace Y] {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T)
    (h' : UniformContinuous φ) (F : Set X) :
    coverEntropyInf T (φ '' F) ≤ coverEntropyInf S F := by
  rw [coverEntropyInf_image _ h F]
  exact coverEntropyInf_antitone_filter S F (uniformContinuous_iff.1 h')

lemma coverEntropySup_image_le_of_uniformContinuous {X Y : Type*} [UniformSpace X]
    [UniformSpace Y] {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T)
    (h' : UniformContinuous φ) (F : Set X) :
    coverEntropySup T (φ '' F) ≤ coverEntropySup S F := by
  rw [coverEntropySup_image _ h F]
  exact coverEntropySup_antitone_filter S F (uniformContinuous_iff.1 h')

theorem coverEntropyInf_of_restrict {X : Type*} (u : UniformSpace X) {T : X → X} {F : Set X}
    (h : MapsTo T F F) :
    coverEntropyInf (MapsTo.restrict T F F h) univ = coverEntropyInf T F := by
  have : Semiconj (fun x : F ↦ x.val) (MapsTo.restrict T F F h) T := MapsTo.val_restrict_apply h
  rw [← coverEntropyInf_image u this univ, image_univ, Subtype.range_coe_subtype, setOf_mem_eq]

theorem coverEntropySup_of_restrict {X : Type*} (u : UniformSpace X) {T : X → X} {F : Set X}
    (h : MapsTo T F F) :
    coverEntropySup (MapsTo.restrict T F F h) univ = coverEntropySup T F := by
  have : Semiconj (fun x : F ↦ x.val) (MapsTo.restrict T F F h) T := MapsTo.val_restrict_apply h
  rw [← coverEntropySup_image u this univ, image_univ, Subtype.range_coe_subtype, setOf_mem_eq]

end Dynamics

#lint
