/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Topological entropy of subsets: monotonicity, closure
Proof that the topological entropy depends monotonically on the subset. Main results
are `entropy_monotone_space₁`/`entropy'_monotone_space₁` (for the cover version)
and `entropy_monotone_space₂`/`entropy'_monotone_space₂` (for the net version). I have decided
to keep all the intermediate steps, since they may be useful in the study of other systems.

For uniformly continuous maps, proof that the entropy of a subset is the entropy of its closure.
Main results are `entropy_of_closure` and `entropy'_of_closure`.

TODO: I think one could implement a notion of Hausdorff onvergence for subsets using uniform
spaces, and then prove the semicontinuity of the topological entropy. It would be a nice
generalization of these lemmas on closures.
-/

namespace Dynamics

open EReal ENNReal Filter Set

variable {X : Type*}

/-! ### Monotonicity of entropy as a function of the subset -/

theorem IsDynCoverOf.of_subset {T : X → X} {F G : Set X} (F_G : F ⊆ G) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h : IsDynCoverOf T G U n s) :
    IsDynCoverOf T F U n s := Subset.trans F_G h

theorem IsDynNetOf.of_subset {T : X → X} {F G : Set X} (F_G : F ⊆ G ) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h : IsDynNetOf T F U n s) :
    IsDynNetOf T G U n s := ⟨Subset.trans h.1 F_G, h.2⟩

theorem coverMincard_monotone_space (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone fun F : Set X ↦ coverMincard T F U n :=
  fun _ _ F_G ↦ biInf_mono fun _ h ↦ h.of_subset F_G

theorem netMaxcard_monotone_space (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone fun F : Set X ↦ netMaxcard T F U n :=
  fun _ _ F_G ↦ biSup_mono fun _ h ↦ h.of_subset F_G

theorem coverEntropyInfEnt_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone fun F : Set X ↦ coverEntropyInfEnt T F U := by
  refine fun F G F_G ↦ (liminf_le_liminf) <| Eventually.of_forall fun n ↦ ?_
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact coverMincard_monotone_space T U n F_G

theorem coverEntropyEnt_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone fun F : Set X ↦ coverEntropyEnt T F U := by
  refine fun F G F_G ↦ (limsup_le_limsup) <| Eventually.of_forall fun n ↦ ?_
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact coverMincard_monotone_space T U n F_G

theorem netEntropyInfEnt_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone fun F : Set X ↦ netEntropyInfEnt T F U := by
  refine fun F G F_G ↦ (liminf_le_liminf) <| Eventually.of_forall fun n ↦ ?_
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact netMaxcard_monotone_space T U n F_G

theorem netEntropyEnt_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone fun F : Set X ↦ netEntropyEnt T F U := by
  refine fun F G F_G ↦ (limsup_le_limsup) <| Eventually.of_forall fun n ↦ ?_
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact netMaxcard_monotone_space T U n F_G

theorem coverEntropyInf_monotone_space [UniformSpace X] (T : X → X) :
    Monotone fun F : Set X ↦ coverEntropyInf T F :=
  fun _ _ F_G ↦ iSup₂_mono fun U _ ↦ coverEntropyInfEnt_monotone_space T U F_G

theorem coverEntropy_monotone_space [UniformSpace X] (T : X → X) :
    Monotone fun F : Set X ↦ coverEntropy T F :=
  fun _ _ F_G ↦ iSup₂_mono fun U _ ↦ coverEntropyEnt_monotone_space T U F_G

/-! ### Topological entropy of closure -/

open Function Uniformity UniformSpace

theorem IsDynCoverOf.closure [UniformSpace X] {T : X → X} (T_cont : UniformContinuous T) {F : Set X}
    {U V : Set (X × X)} (V_uni : V ∈ 𝓤 X) {n : ℕ} {s : Set X} (h : IsDynCoverOf T F U n s) :
    IsDynCoverOf T (closure F) (U ○ V) n s := by
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_V⟩
  rw [id_eq] at W_V
  refine IsDynCoverOf.of_entourage_subset (compRel_mono (Subset.refl U) W_V) fun x x_clos ↦ ?_
  rcases mem_closure_iff_ball.1 x_clos (dynEntourage_mem_uniformity T_cont W_uni n)
    with ⟨y, y_x, y_F⟩
  specialize h y_F
  simp only [iUnion_coe_set, mem_iUnion, exists_prop] at h
  rcases h with ⟨z, z_s, y_z⟩
  simp only [iUnion_coe_set, mem_iUnion, exists_prop]
  use z, z_s
  rw [mem_ball_symmetry (SymmetricRel.dynEntourage T W_symm n)] at y_x
  exact ball_mono (dynEntourage_comp_subset T U W n) z (mem_ball_comp y_z y_x)

theorem coverMincard_of_closure [UniformSpace X] {T : X → X} (T_cont : UniformContinuous T)
    (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) (n : ℕ) :
    coverMincard T (closure F) (U ○ V) n ≤ coverMincard T F U n := by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h | h
  · exact h ▸ le_top
  · rcases (coverMincard_finite_iff T F U n).1 h with ⟨s, s_cover, s_card⟩
    exact s_card ▸ coverMincard_le_card (s_cover.closure T_cont V_uni)

theorem coverEntropyInfEnt_closure [UniformSpace X] {T : X → X} (T_cont : UniformContinuous T)
    (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) :
    coverEntropyInfEnt T (closure F) (U ○ V) ≤ coverEntropyInfEnt T F U := by
  refine (liminf_le_liminf) <| Eventually.of_forall fun n ↦ ?_
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact coverMincard_of_closure T_cont F U V_uni n

theorem coverEntropyEnt_closure [UniformSpace X] {T : X → X} (T_cont : UniformContinuous T)
    (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) :
    coverEntropyEnt T (closure F) (U ○ V) ≤ coverEntropyEnt T F U := by
  refine (limsup_le_limsup) <| Eventually.of_forall fun n ↦ ?_
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact coverMincard_of_closure T_cont F U V_uni n

theorem coverEntropyInf_closure [UniformSpace X] {T : X → X} (T_cont : UniformContinuous T)
    (F : Set X) :
    coverEntropyInf T (closure F) = coverEntropyInf T F := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm
    (coverEntropyInf_monotone_space T (subset_closure (s := F)))
  rcases comp_mem_uniformity_sets U_uni with ⟨V, V_uni, V_U⟩
  exact le_iSup₂_of_le V V_uni ((coverEntropyInfEnt_antitone T (closure F) V_U).trans
    (coverEntropyInfEnt_closure T_cont F V V_uni))

theorem coverEntropy_closure [UniformSpace X] {T : X → X} (T_cont : UniformContinuous T)
    (F : Set X) :
    coverEntropy T (closure F) = coverEntropy T F := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm
    (coverEntropy_monotone_space T (subset_closure (s := F)))
  rcases comp_mem_uniformity_sets U_uni with ⟨V, V_uni, V_U⟩
  exact le_iSup₂_of_le V V_uni ((coverEntropyEnt_antitone T (closure F) V_U).trans
    (coverEntropyEnt_closure T_cont F V V_uni))

/-! ### Topological entropy of unions -/

theorem isDynCoverOf_union {T : X → X} {F G : Set X} {U : Set (X × X)} {n : ℕ} {s t : Set X}
    (hs : IsDynCoverOf T F U n s) (ht : IsDynCoverOf T G U n t) :
    IsDynCoverOf T (F ∪ G) U n (s ∪ t) := by
  intro x x_FG
  rcases x_FG with x_F | x_G
  · exact mem_of_subset_of_mem (iSup₂_mono' fun y y_s ↦ ⟨y, mem_union_left t y_s, le_refl _⟩)
      (hs x_F)
  · exact mem_of_subset_of_mem (iSup₂_mono' fun y y_t ↦ ⟨y, mem_union_right s y_t, le_refl _⟩)
      (ht x_G)

theorem coverMincard_union_le (T : X → X) (F G : Set X) (U : Set (X × X)) (n : ℕ) :
    coverMincard T (F ∪ G) U n ≤ coverMincard T F U n + coverMincard T G U n := by
  classical
  rcases eq_top_or_lt_top (coverMincard T F U n) with hF | hF
  · rw [hF, top_add]; exact le_top
  rcases eq_top_or_lt_top (coverMincard T G U n) with hG | hG
  · rw [hG, add_top]; exact le_top
  rcases (coverMincard_finite_iff T F U n).1 hF with ⟨s, s_cover, s_coverMincard⟩
  rcases (coverMincard_finite_iff T G U n).1 hG with ⟨t, t_cover, t_coverMincard⟩
  rw [← s_coverMincard, ← t_coverMincard]
  have := isDynCoverOf_union s_cover t_cover
  rw [← Finset.coe_union s t] at this
  apply (coverMincard_le_card this).trans ((WithTop.coe_mono (Finset.card_union_le s t)).trans _)
  norm_cast

theorem coverEntropyEnt_union (T : X → X) (F G : Set X) (U : Set (X × X)) :
    coverEntropyEnt T (F ∪ G) U = max (coverEntropyEnt T F U) (coverEntropyEnt T G U) := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  apply le_antisymm _ (max_le (coverEntropyEnt_monotone_space T U subset_union_left)
    (coverEntropyEnt_monotone_space T U subset_union_right))
  simp only
  have key : ∀ n : ℕ, log (coverMincard T (F ∪ G) U n) / n
      ≤ log (max (coverMincard T F U n) (coverMincard T G U n)) / n + log (2 : ENNReal) / n := by
    intro n
    have h_logm : 0 ≤ log (max (coverMincard T F U n) (coverMincard T G U n)) := by
      rw [Monotone.map_max log_monotone]
      exact (log_coverMincard_nonneg T hF U n).trans (le_max_left _ _)
    rw [← div_right_distrib_of_nonneg (c := n) h_logm (zero_le_log_iff.2 one_le_two)]
    apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n)
    rw [← log_mul_add]
    apply log_monotone
    norm_cast
    rw [mul_two]
    exact (coverMincard_union_le T F G U n).trans (add_le_add (le_max_left _ _) (le_max_right _ _))
  apply ((limsup_le_limsup) (Eventually.of_forall fun n ↦ key n)).trans
  have := Filter.Tendsto.limsup_eq <| EReal.tendsto_const_div_atTop_nhds_zero_nat
    (bot_lt_log_iff.2 Nat.ofNat_pos).ne.symm (log_lt_top_iff.2 two_lt_top).ne
  apply (limsup_add_le_add_limsup (Or.inr (this ▸ EReal.zero_ne_top))
    (Or.inr (this ▸ EReal.zero_ne_bot))).trans (le_of_eq _)
  rw [coverEntropyEnt, coverEntropyEnt, this, add_zero, ← limsup_max]
  congr
  ext n
  rw [Monotone.map_max log_monotone,
    Monotone.map_max (EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n))]

theorem coverEntropy_union [UniformSpace X] (T : X → X) (F G : Set X) :
    coverEntropy T (F ∪ G) = max (coverEntropy T F) (coverEntropy T G) := by
  rw [coverEntropy, coverEntropy, coverEntropy, iSup_subtype', iSup_subtype', iSup_subtype',
    ← _root_.sup_eq_max, ← iSup_sup_eq]
  congr
  ext U_uni
  exact coverEntropyEnt_union T F G U_uni.1

/-! ### Topological entropy of finite unions -/

theorem coverEntropy_iUnion_le {ι : Type*} [UniformSpace X] (T : X → X) (F : ι → Set X) :
    ⨆ i, coverEntropy T (F i) ≤ coverEntropy T (⋃ i, F i) :=
  iSup_le fun i ↦ coverEntropy_monotone_space T (subset_iUnion F i)

theorem coverEntropy_biUnion_le {ι : Type*} [UniformSpace X] (s : Set ι) (T : X → X)
   (F : ι → Set X) :
    ⨆ i ∈ s, coverEntropy T (F i) ≤ coverEntropy T (⋃ i ∈ s, F i) :=
  iSup₂_le fun _ i_s ↦ coverEntropy_monotone_space T (subset_biUnion_of_mem i_s)

theorem coverEntropyInf_iUnion_le {ι : Type*} [UniformSpace X] (T : X → X) (F : ι → Set X) :
    ⨆ i, coverEntropyInf T (F i) ≤ coverEntropyInf T (⋃ i, F i) :=
  iSup_le fun i ↦ coverEntropyInf_monotone_space T (subset_iUnion F i)

theorem coverEntropyInf_biUnion_le {ι : Type*} [UniformSpace X] (s : Set ι) (T : X → X)
   (F : ι → Set X) :
    ⨆ i ∈ s, coverEntropyInf T (F i) ≤ coverEntropyInf T (⋃ i ∈ s, F i) :=
  iSup₂_le fun _ i_s ↦ coverEntropyInf_monotone_space T (subset_biUnion_of_mem i_s)

theorem coverEntropy_finite_iUnion {ι : Type*} [UniformSpace X] [Fintype ι] (T : X → X)
    (F : ι → Set X) :
    coverEntropy T (⋃ i, F i) = ⨆ i, coverEntropy T (F i) := by
  apply Fintype.induction_empty_option (P := fun ι _ ↦ ∀ F : ι → Set X,
    coverEntropy T (⋃ i, F i) = ⨆ i, coverEntropy T (F i))
  · intro α β _ α_β h F
    specialize h (F ∘ α_β)
    simp only [comp_apply] at h
    rw [← iUnion_congr_of_surjective (g := F) α_β (Equiv.surjective α_β) (fun _ ↦ comp_apply), h]
    exact Equiv.iSup_comp (g := fun i : β ↦ coverEntropy T (F i)) α_β
  · intro _
    simp only [iUnion_of_empty, coverEntropy_empty, ciSup_of_empty]
  · intro α _ h F
    rw [iSup_option, iUnion_option, coverEntropy_union T (F none) (⋃ i, F (some i)),
      _root_.sup_eq_max]
    congr
    exact h fun i : α ↦ F (some i)

theorem coverEntropy_finite_biUnion {ι : Type*} [UniformSpace X] (s : Finset ι) (T : X → X)
    (F : ι → Set X) :
    coverEntropy T (⋃ i ∈ s, F i) = ⨆ i ∈ s, coverEntropy T (F i) := by
  have fin_coe : Fintype { i // i ∈ s } := FinsetCoe.fintype s
  have := @coverEntropy_finite_iUnion X {i // i ∈ s} _ fin_coe T fun i ↦ F i
  rw [iSup_subtype', ← this, iUnion_subtype]

end Dynamics

#lint
