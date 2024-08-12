/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.Morphism

/-!
# Topological entropy of products
The topological entropy of product is the sum of the topological entropies.

TODO: Get the less easy bounds. Need some work on EReal :
-> something like iSup (f + a) = (iSup f) + a, and maybe, more generally,
  iSup (f + g) ≤ iSup f + iSup g.
-> there's maybe something clever to do using limsup + liminf ≤ limsup and so on to get lower bounds
on coverEntropySupUni, and so on. May be especially interesting for arbitrary products (get weaker
hypotheses for various formulae)

TODO: Extend it to finite/arbitrary products.
-/

namespace Dynamics

open Prod Set Uniformity UniformSpace

variable {X Y : Type*}

/-Miscellaneae.-/

/--Notation for the product of two uniform neighborhoods.-/
def UniformityProd (U : Set (X × X)) (V : Set (Y × Y)) : Set ((X × Y) × X × Y) :=
  {W : (X × Y) × X × Y | (W.1.1, W.2.1) ∈ U ∧ (W.1.2, W.2.2) ∈ V}

theorem UniformityProd_def {α β : Type*} {u : Set (α × α)} {v : Set (β × β)} {p : (α × β) × α × β} :
    p ∈ UniformityProd u v ↔ (p.1.1, p.2.1) ∈ u ∧ (p.1.2, p.2.2) ∈ v := by rfl

theorem ball_prod (U : Set (X × X)) (V : Set (Y × Y)) (xy : X × Y) :
    ball xy (UniformityProd U V) = ball xy.1 U ×ˢ ball xy.2 V := by
  ext p
  simp only [ball, UniformityProd, mem_setOf_eq, mem_prod, mem_preimage]

theorem UniformityProd_of_uniform_prod {α β : Type*} [UniformSpace α] [UniformSpace β]
    {s : Set ((α × β) × α × β)} (h : s ∈ 𝓤 (α × β)) :
    ∃ u ∈ 𝓤 α, ∃ v ∈ 𝓤 β, UniformityProd u v ⊆ s := by
  simp only [uniformity_prod, Filter.mem_inf_iff_superset, Filter.mem_comap] at h
  rcases h with ⟨u, ⟨a, a_uni, a_sub⟩, v, ⟨b, b_uni, b_sub⟩, uv_sub⟩
  use a, a_uni, b, b_uni
  refine subset_trans (subset_trans (fun _ ↦ ?_) (inter_subset_inter a_sub b_sub)) uv_sub
  simp [UniformityProd]

theorem dynamical_uni_prod (S : X → X) (T : Y → Y) (U : Set (X × X)) (V : Set (Y × Y))
    (n : ℕ) :
    DynamicalUni (map S T) (UniformityProd U V) n =
    UniformityProd (DynamicalUni S U n) (DynamicalUni T V n) := by
  ext xy
  rw [dynamical_uni_mem]
  simp only [UniformityProd, mem_setOf_eq]
  rw [dynamical_uni_mem, dynamical_uni_mem, ← forall₂_and]
  refine forall₂_congr fun k _ ↦ ?_
  simp only [map_iterate, map_fst, map_snd]

/-! ### Map swapping -/

theorem Function.Semiconj.prod_map_swap (S : X → X) (T : Y → Y) :
    Function.Semiconj swap (map S T) (map T S) := by
  rw [Function.semiconj_iff_comp_eq, map_comp_swap]

theorem uniformContinuous_swap [UniformSpace X] [UniformSpace Y] :
    UniformContinuous (swap : X × Y → Y × X) :=
  UniformContinuous.prod_mk uniformContinuous_snd uniformContinuous_fst

theorem uniformSpace_comap_swap [UniformSpace X] [UniformSpace Y] :
    comap swap (@instUniformSpaceProd Y X _ _) = (@instUniformSpaceProd X Y _ _) := by
  apply le_antisymm _ (uniformContinuous_iff.1 (@uniformContinuous_swap X Y _ _))
  have := comap_mono (f := swap) (uniformContinuous_iff.1 (@uniformContinuous_swap Y X _ _))
  simp at this
  rw [← @comap_comap (X × Y) (Y × X) (X × Y) _ swap swap, swap_swap_eq, uniformSpace_comap_id,
    id_eq _] at this
  exact this

/-End of miscellaneae.-/

theorem coverEntropyInf_prod_swap [UniformSpace X] [UniformSpace Y] (S : X → X) (T : Y → Y)
    (F : Set X) (G : Set Y) :
    coverEntropyInf (map T S) (G ×ˢ F) = coverEntropyInf (map S T) (F ×ˢ G) := by
  have := coverEntropyInf_image instUniformSpaceProd (Function.Semiconj.prod_map_swap T S) (G ×ˢ F)
  rw [← uniformSpace_comap_swap, ← this, image_swap_prod G F]

theorem coverEntropySup_prod_swap [UniformSpace X] [UniformSpace Y] (S : X → X) (T : Y → Y)
    (F : Set X) (G : Set Y) :
    coverEntropySup (map T S) (G ×ˢ F) = coverEntropySup (map S T) (F ×ˢ G) := by
  have := coverEntropySup_image instUniformSpaceProd (Function.Semiconj.prod_map_swap T S) (G ×ˢ F)
  rw [← uniformSpace_comap_swap, ← this, image_swap_prod G F]

/-! ### Entropy of products -/

theorem dynCover_prod {S : X → X} {T : Y → Y} {F : Set X} {G : Set Y} {U : Set (X × X)}
    {V : Set (Y × Y)} {n : ℕ} {s : Set X} {t : Set Y} (hS : IsDynCoverOf S F U n s)
    (hT : IsDynCoverOf T G V n t) :
    IsDynCoverOf (map S T) (F ×ˢ G) (UniformityProd U V) n (s ×ˢ t) := by
  rw [IsDynCoverOf, dynamical_uni_prod S T U V n]
  intro p p_FG
  specialize hS p_FG.1
  specialize hT p_FG.2
  simp at hS hT
  rcases hS with ⟨x, x_s, p_x⟩
  rcases hT with ⟨y, y_t, p_y⟩
  rw [Set.mem_iUnion₂]
  use (x, y), Set.mem_prod.2 ⟨x_s, y_t⟩
  simp only [ball_prod, mem_prod]
  exact ⟨p_x, p_y⟩

theorem dynNet_prod {S : X → X} {T : Y → Y} {F : Set X} {G : Set Y} {U : Set (X × X)}
    {V : Set (Y × Y)} {n : ℕ} {s : Set X} {t : Set Y} (hS : IsDynNetOf S F U n s)
    (hT : IsDynNetOf T G V n t) :
    IsDynNetOf (map S T) (F ×ˢ G) (UniformityProd U V) n (s ×ˢ t) := by
  apply And.intro (Set.prod_mono hS.1 hT.1)
  rw [dynamical_uni_prod S T U V n]
  simp only [ball_prod]
  exact PairwiseDisjoint.prod hS.2 hT.2

theorem coverMincard_prod (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y) (U : Set (X × X))
    (V : Set (Y × Y)) (n : ℕ) :
    coverMincard (map S T) (F ×ˢ G) (UniformityProd U V) n ≤
    coverMincard S F U n * coverMincard T G V n := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  · simp
  rcases G.eq_empty_or_nonempty with (rfl | G_nemp)
  · simp
  rcases eq_top_or_lt_top (coverMincard S F U n) with (h₁ | h₁)
  · rw [h₁]
    apply le_of_le_of_eq le_top (Eq.symm _)
    rw [WithTop.top_mul]
    exact ENat.one_le_iff_ne_zero.1 ((coverMincard_pos_iff T G V n).2 G_nemp)
  rcases eq_top_or_lt_top (coverMincard T G V n) with (h₂ | h₂)
  · rw [h₂]
    apply le_of_le_of_eq le_top (Eq.symm _)
    rw [WithTop.mul_top]
    exact ENat.one_le_iff_ne_zero.1 ((coverMincard_pos_iff S F U n).2 F_nemp)
  rcases (coverMincard_finite_iff S F U n).1 h₁ with ⟨s, s_cover, s_card⟩
  rcases (coverMincard_finite_iff T G V n).1 h₂ with ⟨t, t_cover, t_card⟩
  rw [← s_card, ← t_card, ← Nat.cast_mul, ← Finset.card_product s t]
  apply coverMincard_le_card
  rw [Finset.coe_product]
  exact dynCover_prod s_cover t_cover

theorem netMaxcard_prod (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y) (U : Set (X × X))
    (V : Set (Y × Y)) (n : ℕ) :
    netMaxcard S F U n * netMaxcard T G V n
    ≤ netMaxcard (map S T) (F ×ˢ G) (UniformityProd U V) n := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  · simp
  rcases G.eq_empty_or_nonempty with (rfl | G_nemp)
  · simp
  rcases eq_top_or_lt_top (netMaxcard S F U n) with (h₁ | h₁)
  · refine le_of_le_of_eq le_top (Eq.symm ((netMaxcard_infinite_iff _ _ _ n).2 fun k ↦ ?_))
    rw [netMaxcard_eq_sSup, sSup_eq_top] at h₁
    specialize h₁ (k : ℕ∞) (WithTop.coe_lt_top k)
    simp at h₁
    rcases h₁ with ⟨s, s_net, s_card⟩
    rcases G_nemp with ⟨y, y_G⟩
    use s ×ˢ ({y} : Finset Y)
    rw [Finset.coe_product]
    apply And.intro
    . apply dynNet_prod s_net
      rw [Finset.coe_singleton]
      exact dynNet_by_singleton T V n y_G
    . rw [Finset.card_product s ({y} : Finset Y), Finset.card_singleton y, mul_one]
      exact le_of_lt s_card
  rcases eq_top_or_lt_top (netMaxcard T G V n) with (h₂ | h₂)
  · refine le_of_le_of_eq le_top (Eq.symm ((netMaxcard_infinite_iff _ _ _ n).2 fun k ↦ ?_))
    rw [netMaxcard_eq_sSup, sSup_eq_top] at h₂
    specialize h₂ (k : ℕ∞) (WithTop.coe_lt_top k)
    simp at h₂
    rcases h₂ with ⟨t, t_net, t_card⟩
    rcases F_nemp with ⟨x, x_F⟩
    use ({x} : Finset X) ×ˢ t
    rw [Finset.coe_product]
    apply And.intro
    . apply dynNet_prod _ t_net
      rw [Finset.coe_singleton]
      exact dynNet_by_singleton S U n x_F
    . rw [Finset.card_product ({x} : Finset X) t, Finset.card_singleton x, one_mul]
      exact le_of_lt t_card
  rcases (netMaxcard_finite_iff S F U n).1 h₁ with ⟨s, s_cover, s_card⟩
  rcases (netMaxcard_finite_iff T G V n).1 h₂ with ⟨t, t_cover, t_card⟩
  rw [← s_card, ← t_card, ← Nat.cast_mul, ← Finset.card_product s t]
  apply card_le_netMaxcard
  rw [Finset.coe_product]
  exact dynNet_prod s_cover t_cover

open ENNReal EReal Filter

theorem coverEntropySupUni_prod_le (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : Set (X × X)) (V : Set (Y × Y)) :
    coverEntropySupUni (map S T) (F ×ˢ G) (UniformityProd U V)
    ≤ (coverEntropySupUni S F U) + (coverEntropySupUni T G V) := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  . simp
  rcases G.eq_empty_or_nonempty with (rfl | G_nemp)
  . simp
  apply le_trans _ <| limsup_add_le_add_limsup
    (Or.inl <| ne_of_gt <| lt_of_lt_of_le bot_lt_zero (coverEntropySupUni_nonneg S F_nemp U))
    (Or.inr <| ne_of_gt <| lt_of_lt_of_le bot_lt_zero (coverEntropySupUni_nonneg T G_nemp V))
  refine Filter.limsup_le_limsup <| eventually_of_forall fun n ↦ ?_
  simp only [Pi.add_apply]
  rw [← div_right_distrib_of_nonneg (log_coverMincard_nonneg S F_nemp U n)
    (log_coverMincard_nonneg T G_nemp V n), ← ENNReal.log_mul_add, ← ENat.toENNReal_mul]
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  exact log_monotone (ENat.toENNReal_le.2 (coverMincard_prod S T F G U V n))

theorem le_netEntropyInfUni_prod (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : Set (X × X)) (V : Set (Y × Y)) :
    (netEntropyInfUni S F U) + (netEntropyInfUni T G V)
    ≤ netEntropyInfUni (map S T) (F ×ˢ G) (UniformityProd U V) := by
  rcases F.eq_empty_or_nonempty with (rfl | F_nemp)
  . simp
  rcases G.eq_empty_or_nonempty with (rfl | G_nemp)
  . simp
  apply le_trans add_liminf_le_liminf_add
  refine Filter.liminf_le_liminf <| eventually_of_forall fun n ↦ ?_
  simp only [Pi.add_apply]
  rw [← div_right_distrib_of_nonneg (log_netMaxcard_nonneg S F_nemp U n)
    (log_netMaxcard_nonneg T G_nemp V n), ← ENNReal.log_mul_add, ← ENat.toENNReal_mul]
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  exact log_monotone (ENat.toENNReal_le.2 (netMaxcard_prod S T F G U V n))

variable [UniformSpace X] [UniformSpace Y]

theorem coverEntropySup_prod_le (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y) :
    coverEntropySup (map S T) (F ×ˢ G) ≤ (coverEntropySup S F) + (coverEntropySup T G) := by
  refine iSup₂_le fun W W_uni ↦ ?_
  rcases UniformityProd_of_uniform_prod W_uni with ⟨U, U_uni, V, V_uni, UV_W⟩
  apply le_trans (coverEntropySupUni_antitone (map S T) (F ×ˢ G) UV_W)
  apply le_trans (coverEntropySupUni_prod_le S T F G U V)
  exact add_le_add (coverEntropySupUni_le_coverEntropySup S F U_uni)
    (coverEntropySupUni_le_coverEntropySup T G V_uni)

end Dynamics

#lint
