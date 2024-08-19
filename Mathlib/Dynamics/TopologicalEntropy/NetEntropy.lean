/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy via covers
We implement Bowen-Dinaburg's definitions of the topological entropy, via nets.

All is stated in the vocabulary of uniform spaces. For compact spaces, the uniform structure
is canonical, so the topological entropy depends only on the topological structure. This will give
a clean proof that the topological entropy is a topological invariant of the dynamics.

A notable choice is that we define the topological entropy of a subset `F` of the whole space.
Usually, one defines the entropy of an invariant subset `F` as the entropy of the restriction of the
transformation to `F`. We avoid the latter definition as it would involve frequent manipulation of
subtypes. Our version directly gives a meaning to the topological entropy of a subsystem, and a
single lemma (`subset_restriction_entropy` in `.Morphism`) will give the equivalence between
both versions.

Another choice is to give a meaning to the entropy of `∅` (it must be `-∞` to stay coherent) and to
keep the possibility for the entropy to be infinite. Hence, the entropy takes values in the extended
reals `[-∞, +∞]`. The consequence is that we use `ℕ∞`, `ℝ≥0∞` and `EReal` numbers.

We relate in this file `CoverEntropy` and `NetEntropy`. This file is downstream of
`Mathlib.Dynamics.TopologicalEntropy.CoverEntropy` since the submultiplicative argument there
(specifically `dyncover_iterate`) is more natural for covers.

## Main definitions
- `IsDynNetOf`: property that dynamical balls centered on a subset `s` of `F` are disjoint.
- `netMaxcard`: maximal cardinal of a dynamical net. Takes values in `ℕ∞`.
- `netEntropyInfUni`/`netEntropySupUni`: exponential growth of `netMaxcard`. The former is
defined with a `liminf`, the later with a `limsup`. Take values in `EReal`.

## Tags
net, entropy

## TODO
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

namespace Dynamics

open Set Uniformity UniformSpace

variable {X : Type*}

/-! ### Dynamical nets -/

/-- Given a subset `F`, a uniform neighborhood `U` and an integer `n`, a subset `s` of `F` is a
`(n, U)`-dynamical net of `F` if no two orbits of length `n` of points in `s` shadow each other.-/
def IsDynNetOf (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) : Prop :=
    s ⊆ F ∧ s.PairwiseDisjoint (fun x : X ↦ ball x (dynEntourage T U n))

lemma IsDynNetOf.of_le {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ} (m_n : m ≤ n) {s : Set X}
    (h : IsDynNetOf T F U m s) :
    IsDynNetOf T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 (fun x ↦ ball_mono (dynEntourage_antitone T U m_n) x)⟩

lemma IsDynNetOf.of_entourage_subset {T : X → X} {F : Set X} {U V : Set (X × X)} (U_V : U ⊆ V)
    {n : ℕ} {s : Set X} (h : IsDynNetOf T F V n s) :
    IsDynNetOf T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 (fun x ↦ ball_mono (dynEntourage_monotone T n U_V) x)⟩

lemma isDynNetOf_empty (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    IsDynNetOf T F U n ∅ :=
  ⟨empty_subset F, pairwise_empty _⟩

lemma isDynNetOf_singleton (T : X → X) {F : Set X} (U : Set (X × X)) (n : ℕ) {x : X} (h : x ∈ F) :
    IsDynNetOf T F U n {x} :=
  ⟨singleton_subset_iff.2 h, pairwise_singleton x _⟩

/-- Given an entourage `U` and a time `n`, a dynamical net has a smaller cardinal than a dynamical
  cover. This lemma is the first of two key results to compare two versions topological entropy:
  with cover and with nets, the second being `coverMincard_comp_le_netMaxcard`.-/
lemma isDynNetOf_card_le_isDynCoverOf_card {T : X → X} {F : Set X} {U : Set (X × X)}
    (U_symm : SymmetricRel U) {n : ℕ} {s t : Finset X} (hs : IsDynNetOf T F U n s)
    (ht : IsDynCoverOf T F U n t) :
    s.card ≤ t.card := by
  have (x : X) (x_s : x ∈ s) : ∃ z ∈ t, x ∈ ball z (dynEntourage T U n) := by
    specialize ht (hs.1 x_s)
    simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, exists_prop] at ht
    exact ht
  choose! F s_t using this
  simp only [mem_ball_symmetry (U_symm.dynEntourage T n)] at s_t
  apply Finset.card_le_card_of_injOn F (fun x x_s ↦ (s_t x x_s).1)
  intro x x_s y y_s Fx_Fy
  exact PairwiseDisjoint.elim_set hs.2 x_s y_s (F x) (s_t x x_s).2 (Fx_Fy ▸ (s_t y y_s).2)

/-! ### Maximal cardinal of dynamical nets -/

/-- The largest cardinal of a `(n, U)`-dynamical net of `F`. Takes values in `ℕ∞`, and is infinite
if and only if `F` admits nets of arbitrarily large size.-/
noncomputable def netMaxcard (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) : ℕ∞ :=
  ⨆ (s : Finset X) (_ : IsDynNetOf T F U n s), (s.card : ℕ∞)

lemma card_le_netMaxcard {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynNetOf T F U n s) :
    s.card ≤ netMaxcard T F U n :=
  le_iSup₂ (α := ℕ∞) s h

lemma netMaxcard_monotone_time (T : X → X) (F : Set X) (U : Set (X × X)) :
    Monotone (fun n : ℕ ↦ netMaxcard T F U n) :=
  fun _ _ m_n ↦ biSup_mono (fun _ h ↦ h.of_le m_n)

lemma netMaxcard_antitone (T : X → X) (F : Set X) (n : ℕ) :
    Antitone (fun U : Set (X × X) ↦ netMaxcard T F U n) :=
  fun _ _ U_V ↦ biSup_mono (fun _ h ↦ h.of_entourage_subset U_V)

lemma netMaxcard_finite_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    netMaxcard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynNetOf T F U n s ∧ (s.card : ℕ∞) = netMaxcard T F U n := by
  apply Iff.intro <;> intro h
  · rcases WithTop.ne_top_iff_exists.1 (ne_of_lt h) with ⟨k, k_max⟩
    rw [← k_max]
    simp only [ENat.some_eq_coe, Nat.cast_inj]
    have : netMaxcard T F U n
      = sSup (WithTop.some '' (Finset.card '' {s : Finset X | IsDynNetOf T F U n s})) := by
      rw [netMaxcard, ← image_comp, sSup_image]
      simp only [mem_setOf_eq, ENat.some_eq_coe, Function.comp_apply]
    rw [this] at k_max
    have h_bdda : BddAbove (Finset.card '' {s : Finset X | IsDynNetOf T F U n s}) := by
      use k
      rw [mem_upperBounds]
      simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intros s h
      rw [← WithTop.coe_le_coe, k_max]
      apply le_sSup
      simp only [ENat.some_eq_coe, mem_image, mem_setOf_eq, Nat.cast_inj, exists_eq_right]
      use s
    have h_nemp : (Finset.card '' {s : Finset X | IsDynNetOf T F U n s}).Nonempty := by
      use 0
      simp only [mem_image, mem_setOf_eq, Finset.card_eq_zero, exists_eq_right, Finset.coe_empty]
      exact isDynNetOf_empty T F U n
    have key := Nat.sSup_mem h_nemp h_bdda
    rw [← WithTop.coe_sSup' h_bdda, ENat.some_eq_coe, Nat.cast_inj] at k_max
    rw [← k_max, mem_image] at key
    simp only [mem_setOf_eq] at key
    exact key
  · rcases h with ⟨s, _, s_netMaxcard⟩
    rw [← s_netMaxcard]
    exact WithTop.coe_lt_top s.card

@[simp]
lemma netMaxcard_zero {T : X → X} {U : Set (X × X)} {n : ℕ} : netMaxcard T ∅ U n = 0 := by
  rw [netMaxcard, ← bot_eq_zero, iSup₂_eq_bot]
  intro s s_net
  replace s_net := subset_empty_iff.1 s_net.1
  norm_cast at s_net
  rw [s_net, Finset.card_empty, CharP.cast_eq_zero, bot_eq_zero']

lemma netMaxcard_zero_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    netMaxcard T F U n = 0 ↔ F = ∅ := by
  refine Iff.intro (fun h ↦ ?_) (fun h ↦ by rw [h, netMaxcard_zero])
  rw [eq_empty_iff_forall_not_mem]
  intros x x_F
  have key := isDynNetOf_singleton T U n x_F
  rw [← Finset.coe_singleton] at key
  replace key := card_le_netMaxcard key
  rw [Finset.card_singleton, Nat.cast_one, h] at key
  exact not_lt_of_le key zero_lt_one

lemma netMaxcard_pos_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    1 ≤ netMaxcard T F U n ↔ F.Nonempty := by
  rw [ENat.one_le_iff_ne_zero, nonempty_iff_ne_empty]
  exact not_iff_not.2 (netMaxcard_zero_iff T F U n)

lemma netMaxcard_time_zero (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    netMaxcard T F U 0 = 1 := by
  apply le_antisymm (iSup₂_le _) ((netMaxcard_pos_iff T F U 0).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_zero, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 (fun x x_s y y_s ↦ ?_)
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)

lemma netMaxcard_univ (T : X → X) {F : Set X} (h : F.Nonempty) (n : ℕ) :
    netMaxcard T F univ n = 1 := by
  apply le_antisymm (iSup₂_le _) ((netMaxcard_pos_iff T F univ n).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_univ, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 (fun x x_s y y_s ↦ ?_)
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)

lemma netMaxcard_infinite_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    netMaxcard T F U n = ⊤ ↔ ∀ k : ℕ, ∃ s : Finset X, IsDynNetOf T F U n s ∧ k ≤ s.card := by
  apply Iff.intro <;> intro h
  · intro k
    rw [netMaxcard, iSup_subtype', iSup_eq_top] at h
    specialize h k (ENat.coe_lt_top k)
    simp only [Nat.cast_lt, Subtype.exists, exists_prop] at h
    rcases h with ⟨s, s_net, s_k⟩
    exact ⟨s, ⟨s_net, s_k.le⟩⟩
  · refine WithTop.forall_lt_iff_eq_top.1 fun k ↦ ?_
    specialize h (k + 1)
    rcases h with ⟨s, s_net, s_card⟩
    apply lt_of_lt_of_le _ (card_le_netMaxcard s_net)
    rw [ENat.some_eq_coe, Nat.cast_lt]
    exact lt_of_lt_of_le (lt_add_one k) s_card

lemma netMaxcard_le_coverMincard (T : X → X) (F : Set X) {U : Set (X × X)} (h : SymmetricRel U)
    (n : ℕ) :
    netMaxcard T F U n ≤ coverMincard T F U n := by
  rcases (eq_top_or_lt_top (coverMincard T F U n)) with h' | h'
  · exact h' ▸ le_top
  · rcases ((coverMincard_finite_iff T F U n).1 h') with ⟨t, t_cover, t_mincard⟩
    rw [← t_mincard]
    exact iSup₂_le
      (fun s s_net ↦ Nat.cast_le.2 (isDynNetOf_card_le_isDynCoverOf_card h s_net t_cover))

/-- Given an entourage `U` and a time `n`, a minimal dynamical cover by `U ○ U` has a smaller
  cardinal than a maximal dynamical net by `U`. This lemma is the second of two key results to
  compare two versions topological entropy: with cover and with nets.-/
lemma coverMincard_comp_le_netMaxcard (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : SymmetricRel U) (n : ℕ) :
    coverMincard T F (U ○ U) n ≤ netMaxcard T F U n := by
  classical
  rcases (eq_top_or_lt_top (netMaxcard T F U n)) with h | h
  · exact h ▸ le_top
  · rcases ((netMaxcard_finite_iff T F U n).1 h) with ⟨s, s_net, s_netMaxcard⟩
    rw [← s_netMaxcard]
    apply coverMincard_le_card
    by_contra h
    rcases not_subset.1 h with ⟨x, x_F, x_uncov⟩
    simp only [Finset.mem_coe, mem_iUnion, exists_prop, not_exists, not_and] at x_uncov
    have larger_net : IsDynNetOf T F U n (insert x s) := by
      apply And.intro (insert_subset x_F s_net.1)
      refine pairwiseDisjoint_insert.2 (And.intro s_net.2 (fun y y_s _ ↦ ?_))
      refine disjoint_left.2 (fun z z_x z_y ↦ x_uncov y y_s ?_)
      exact mem_ball_dynEntourage_comp T n U_symm x y (nonempty_of_mem ⟨z_x, z_y⟩)
    rw [← Finset.coe_insert x s] at larger_net
    apply not_le_of_lt _ (card_le_netMaxcard larger_net)
    rw [← s_netMaxcard, Nat.cast_lt]
    refine lt_of_lt_of_eq (lt_add_one s.card) (Finset.card_insert_of_not_mem fun x_s ↦ ?_).symm
    apply x_uncov x x_s
    apply ball_mono (dynEntourage_monotone T n (subset_comp_self U_rfl)) x
    apply ball_mono (idRel_subset_dynEntourage T U_rfl n) x
    simp only [ball, mem_preimage, mem_idRel]

open ENNReal EReal

lemma log_netMaxcard_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) (n : ℕ) :
    0 ≤ log (netMaxcard T F U n) := by
  apply zero_le_log_iff.2
  rw [← ENat.toENNReal_one, ENat.toENNReal_le]
  exact (netMaxcard_pos_iff T F U n).2 h

/-! ### Net entropy of entourages -/

open Filter

/--The entropy of an entourage `U`, defined as the exponential rate of growth of the size of the
largest `(n, U)`-dynamical net of `F`. Takes values in the space of extended real numbers
`[-∞,+∞]`. This version uses a `liminf`.-/
noncomputable def netEntropyInfUni (T : X → X) (F : Set X) (U : Set (X × X)) :=
  atTop.liminf fun n : ℕ ↦ log (netMaxcard T F U n) / n

/--The entropy of an entourage `U`, defined as the exponential rate of growth of the size of the
largest `(n, U)`-dynamical net of `F`. Takes values in the space of extended real numbers
`[-∞,+∞]`. This version uses a `limsup`.-/
noncomputable def netEntropySupUni (T : X → X) (F : Set X) (U : Set (X × X)) :=
  atTop.limsup fun n : ℕ ↦ log (netMaxcard T F U n) / n

lemma netEntropyInfUni_antitone (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ netEntropyInfUni T F U) :=
  fun _ _ U_V ↦ (liminf_le_liminf) <| Eventually.of_forall
    fun n ↦ EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (netMaxcard_antitone T F n U_V))

lemma netEntropySupUni_antitone (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ netEntropySupUni T F U) :=
  fun _ _ U_V ↦ (limsup_le_limsup) <| Eventually.of_forall
    fun n ↦ EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (netMaxcard_antitone T F n U_V))

lemma netEntropyInfUni_le_netEntropySupUni (T : X → X) (F : Set X) (U : Set (X × X)) :
    netEntropyInfUni T F U ≤ netEntropySupUni T F U :=
  liminf_le_limsup

@[simp]
lemma netEntropySupUni_bot {T : X → X} {U : Set (X × X)} : netEntropySupUni T ∅ U = ⊥ := by
  suffices h : ∀ᶠ n : ℕ in atTop, log (netMaxcard T ∅ U n) / n = ⊥ by
    rw [netEntropySupUni, limsup_congr h]
    exact limsup_const ⊥
  · simp only [netMaxcard_zero, ENat.toENNReal_zero, log_zero, eventually_atTop]
    use 1
    exact fun n n_pos ↦ bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)

@[simp]
lemma netEntropyInfUni_bot {T : X → X} {U : Set (X × X)} : netEntropyInfUni T ∅ U = ⊥ :=
  eq_bot_mono (netEntropyInfUni_le_netEntropySupUni T ∅ U) netEntropySupUni_bot

lemma netEntropyInfUni_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    0 ≤ netEntropyInfUni T F U :=
  le_trans (le_iInf fun n ↦ EReal.div_nonneg (log_netMaxcard_nonneg T h U n)
    (Nat.cast_nonneg' n)) iInf_le_liminf

lemma netEntropySupUni_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    0 ≤ netEntropySupUni T F U :=
  le_trans (netEntropyInfUni_nonneg T h U) (netEntropyInfUni_le_netEntropySupUni T F U)

lemma netEntropyInfUni_univ (T : X → X) {F : Set X} (h : F.Nonempty) :
    netEntropyInfUni T F univ = 0 := by
  simp [netEntropyInfUni, netMaxcard_univ T h]

lemma netEntropySupUni_univ (T : X → X) {F : Set X} (h : F.Nonempty) :
    netEntropySupUni T F univ = 0 := by
  simp [netEntropySupUni, netMaxcard_univ T h]

lemma netEntropyInfUni_le_CoverEntropyInfUni (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : SymmetricRel U) :
    netEntropyInfUni T F U ≤ coverEntropyInfUni T F U := by
  refine (liminf_le_liminf) (Eventually.of_forall fun n ↦ ?_)
  apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  exact ENat.toENNReal_le.2 (netMaxcard_le_coverMincard T F h n)

lemma CoverEntropyInfUni_comp_le_netEntropyInfUni (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : SymmetricRel U) :
    coverEntropyInfUni T F (U ○ U) ≤ netEntropyInfUni T F U := by
  refine (liminf_le_liminf) (Eventually.of_forall fun n ↦ ?_)
  apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  exact ENat.toENNReal_le.2 (coverMincard_comp_le_netMaxcard T F U_rfl U_symm n)

lemma netEntropySupUni_le_CoverEntropySupUni (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : SymmetricRel U) :
    netEntropySupUni T F U ≤ coverEntropySupUni T F U := by
  refine (limsup_le_limsup) (Eventually.of_forall fun n ↦ ?_)
  apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  exact ENat.toENNReal_le.2 (netMaxcard_le_coverMincard T F h n)

lemma CoverEntropySupUni_comp_le_netEntropySupUni (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : SymmetricRel U) :
    coverEntropySupUni T F (U ○ U) ≤ netEntropySupUni T F U := by
  refine (limsup_le_limsup) (Eventually.of_forall fun n ↦ ?_)
  apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  exact ENat.toENNReal_le.2 (coverMincard_comp_le_netMaxcard T F U_rfl U_symm n)

/-! ### Relationship with cover entropy -/

variable [UniformSpace X] (T : X → X) (F : Set X)

lemma coverEntropyInf_eq_iSup_netEntropyInfUni :
    coverEntropyInf T F = ⨆ U ∈ 𝓤 X, netEntropyInfUni T F U := by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni ↦ ?_
  · rcases (comp_symm_mem_uniformity_sets U_uni) with ⟨V, V_uni, V_symm, V_comp_U⟩
    apply (coverEntropyInfUni_antitone T F V_comp_U).trans (le_iSup₂_of_le V V_uni _)
    exact CoverEntropyInfUni_comp_le_netEntropyInfUni T F (refl_le_uniformity V_uni) V_symm
  · apply (netEntropyInfUni_antitone T F (symmetrizeRel_subset_self U)).trans
    apply le_trans _ (le_iSup₂ (symmetrizeRel U) (symmetrize_mem_uniformity U_uni))
    exact netEntropyInfUni_le_CoverEntropyInfUni T F (symmetric_symmetrizeRel U)

lemma coverEntropySup_eq_iSup_netEntropySupUni :
    coverEntropySup T F = ⨆ U ∈ 𝓤 X, netEntropySupUni T F U := by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni ↦ ?_
  · rcases (comp_symm_mem_uniformity_sets U_uni) with ⟨V, V_uni, V_symm, V_comp_U⟩
    exact (coverEntropySupUni_antitone T F V_comp_U).trans <| le_iSup₂_of_le V V_uni
      <| CoverEntropySupUni_comp_le_netEntropySupUni T F (refl_le_uniformity V_uni) V_symm
  · apply (netEntropySupUni_antitone T F (symmetrizeRel_subset_self U)).trans
    apply le_trans _ (le_iSup₂ (symmetrizeRel U) (symmetrize_mem_uniformity U_uni))
    exact netEntropySupUni_le_CoverEntropySupUni T F (symmetric_symmetrizeRel U)

lemma netEntropyInfUni_le_coverEntropyInf {U : Set (X × X)} (h : U ∈ 𝓤 X) :
    netEntropyInfUni T F U ≤ coverEntropyInf T F := by
  rw [coverEntropyInf_eq_iSup_netEntropyInfUni T F]
  exact le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ netEntropyInfUni T F U) U h

lemma netEntropySupUni_le_coverEntropySup {U : Set (X × X)} (h : U ∈ 𝓤 X) :
    netEntropySupUni T F U ≤ coverEntropySup T F := by
  rw [coverEntropySup_eq_iSup_netEntropySupUni T F]
  exact le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ netEntropySupUni T F U) U h

end Dynamics

#lint
