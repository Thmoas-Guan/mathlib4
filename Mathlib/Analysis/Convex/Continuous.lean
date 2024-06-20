/-
Copyright (c) 2023 Yaël Dillies, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Zichen Wang
-/
import Mathlib.Analysis.Convex.Normed

/-!
# Convex functions are continuous

This file proves that a convex function from a finite dimensional real normed space to `ℝ` is
continuous.
-/

open FiniteDimensional Metric Set List Bornology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {f : E → ℝ} {x₀ : E} {ε r : ℝ}

lemma exists_lipschitzOnWith_of_isBounded (hf : ConvexOn ℝ (ball x₀ r) f) (hε : 0 < ε)
    (f_bounded : IsBounded (f '' ball x₀ r)) : ∃ K, LipschitzOnWith K f (ball x₀ (r - ε)) := by
  rw [isBounded_iff_subset_ball 0] at f_bounded
  simp only [Set.subset_def, mem_image, mem_ball, dist_zero_right, Real.norm_eq_abs,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at f_bounded
  obtain ⟨M, hM⟩ := f_bounded
  set K := 2 * M / ε with hK
  have oneside {x y : E} (hx : x ∈ ball x₀ (r - ε)) (hy : y ∈ ball x₀ (r - ε)) :
      f x - f y ≤ K * ‖x - y‖ := by
    obtain rfl | hxy := eq_or_ne x y
    · simp
    have hx₀r : ball x₀ (r - ε) ⊆ ball x₀ r := ball_subset_ball <| by linarith
    have hx' :  x ∈ ball x₀ r := hx₀r hx
    have hy' :  y ∈ ball x₀ r := hx₀r hy
    let z := x + (ε / ‖x - y‖) • (x - y)
    replace hxy : 0 < ‖x - y‖ := by rwa [norm_sub_pos_iff]
    have hz : z ∈ ball x₀ r := mem_ball_iff_norm.2 <| by
      calc
        _ = ‖(x - x₀) + (ε / ‖x - y‖) • (x - y)‖ := by simp only [z, add_sub_right_comm]
        _ ≤ ‖x - x₀‖ + ‖(ε / ‖x - y‖) • (x - y)‖ := norm_add_le ..
        _ < r - ε + ε :=
          add_lt_add_of_lt_of_le (mem_ball_iff_norm.1 hx) <| by
            simp [norm_smul, abs_of_nonneg, hε.le, hxy.ne']
        _ = r := by simp
    let a := ε / (ε + ‖x - y‖)
    let b := ‖x - y‖ / (ε + ‖x - y‖)
    have hab : a + b = 1 := by field_simp [a, b]
    have hxyz : x = a • y + b • z := by
      calc
        x = a • x + b • x := by rw [Convex.combo_self hab]
        _ = a • y + b • z := by simp [z, a, b, smul_smul, hxy.ne', smul_sub]; abel
    rw [hK, mul_comm, ← mul_div_assoc, le_div_iff' hε]
    calc
      ε * (f x - f y) ≤ ‖x - y‖ * (f z - f x) := by
        rw [mul_sub, mul_sub, sub_le_sub_iff, ← add_mul]
        have h := hf.2 hy' hz (by positivity) (by positivity) hab
        field_simp [← hxyz, a, b, ← mul_div_right_comm] at h
        rwa [← le_div_iff' (by positivity), add_comm (_ * _)]
      _ ≤ _ := by
        rw [sub_eq_add_neg (f _), two_mul]
        gcongr
        · exact (le_abs_self _).trans <| (hM _ hz).le
        · exact (neg_le_abs _).trans <| (hM _ hx').le
  refine ⟨K.toNNReal, .of_dist_le' fun x hx y hy ↦ ?_⟩
  simp_rw [dist_eq_norm_sub, Real.norm_eq_abs, abs_sub_le_iff]
  exact ⟨oneside hx hy, norm_sub_rev x _ ▸ oneside hy hx⟩

lemma ConvexOn.continuousOn_tfae (hC : IsOpen C) (hC' : C.Nonempty) (hf : ConvexOn ℝ C f) :
    TFAE [LocallyLipschitzOn C f, ContinuousOn f C, ∃ x₀ ∈ C, ContinuousAt f x₀,
      ∃ x₀ ∈ C, (𝓝 x₀).IsBoundedUnder (· ≤ ·) f,
      ∀ ⦃x⦄, x ∈ C → (𝓝 x).IsBoundedUnder (· ≤ ·) f,
      ∀ ⦃x⦄, x ∈ C → (𝓝 x).IsBoundedUnder (· ≤ ·) |f|] := by
  tfae_have 1 → 2
  · exact LocallyLipschitzOn.continuousOn
  tfae_have 2 → 3
  · obtain ⟨x₀, hx₀⟩ := hC'
    exact fun h ↦ ⟨x₀, hx₀, h.continuousAt <| hC.mem_nhds hx₀⟩
  tfae_have 3 → 4
  · rintro ⟨x₀, hx₀, h⟩
    exact ⟨x₀, hx₀, f x₀ + 1, by simpa using h.eventually (eventually_le_nhds (by simp))⟩
  tfae_have 4 → 5
  · rintro ⟨x₀, hx₀, r, hr⟩ x hx
    have : ∀ᶠ δ in 𝓝 (0 : ℝ), (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀ ∈ C := by
      have h : ContinuousAt (fun δ : ℝ ↦ (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀) 0 := by
        fun_prop (disch := norm_num)
      exact h (by simpa using hC.mem_nhds hx)
    obtain ⟨δ, hδ₀, hy, hδ₁⟩ := (this.and <| eventually_lt_nhds zero_lt_one).exists_gt
    set y := (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀
    refine ⟨max r (f y), ?_⟩
    simp only [Filter.eventually_map, Pi.abs_apply] at hr ⊢
    obtain ⟨ε, hε, hr⟩ := Metric.eventually_nhds_iff.1 <| hr.and (hC.eventually_mem hx₀)
    refine Metric.eventually_nhds_iff.2 ⟨ε * δ, by positivity, fun z hz ↦ ?_⟩
    have hx₀' : δ⁻¹ • (x - y) + y = x₀ := MulAction.injective₀ (sub_ne_zero.2 hδ₁.ne') <| by
      simp [y, smul_sub, smul_smul, hδ₀.ne', div_eq_mul_inv, sub_ne_zero.2 hδ₁.ne', mul_left_comm,
        sub_mul, sub_smul]
    let w := δ⁻¹ • (z - y) + y
    have hwyz : δ • w + (1 - δ) • y = z := by simp [w, hδ₀.ne', sub_smul]
    have hw : dist w x₀ < ε := by
      simpa [w, ← hx₀', dist_smul₀, abs_of_nonneg, hδ₀.le, inv_mul_lt_iff', hδ₀]
    calc
      f z ≤ max (f w) (f y) :=
        (hf.subset (hf.1.segment_subset (hr hw).2 hy) (convex_segment ..)).le_max_of_mem_segment
          ⟨_, _, hδ₀.le, sub_nonneg.2 hδ₁.le, by simp, hwyz⟩
      _ ≤ max r (f y) := by gcongr; exact (hr hw).1
  tfae_have 5 → 6
  · rintro h x₀ hx₀
    obtain ⟨r, hr⟩ := h hx₀
    refine ⟨|r| + 2 * |f x₀|, ?_⟩
    simp only [Filter.eventually_map, Pi.abs_apply, abs_le'] at hr ⊢
    obtain ⟨ε, hε, hεC, hfr⟩ : ∃ ε > 0, ball x₀ ε ⊆ C ∧ ∀ y ∈ ball x₀ ε, f y ≤ r := by
      simpa using Metric.mem_nhds_iff.1 <| Filter.inter_mem (hC.mem_nhds hx₀) hr
    refine Metric.mem_nhds_iff.2 ⟨ε, hε, fun y hx ↦ ⟨?_, ?_⟩⟩
    · exact (hfr _ hx).trans <| (le_abs_self _).trans <| by simp
    have hx' : 2 • x₀ - y ∈ ball x₀ ε := by
      simpa [two_nsmul, add_sub_add_comm, dist_eq_norm_sub, ← smul_sub, sub_sub_eq_add_sub,
        norm_sub_rev] using hx
    rw [← sub_le_iff_le_add, neg_sub_comm, sub_le_iff_le_add', ← abs_two, ← abs_mul]
    calc
      -|2 * f x₀| ≤ 2 * f x₀ := neg_abs_le _
      _ ≤ f y + f (2 • x₀ - y) := by
        have := hf.2 (hεC hx) (hεC hx') (by positivity) (by positivity) (add_halves _)
        simp [smul_sub, ← Nat.cast_smul_eq_nsmul ℝ] at this
        cancel_denoms at this
        rwa [← Nat.cast_two, Nat.cast_smul_eq_nsmul] at this
      _ ≤ f y + |r| := by gcongr; exact (hfr _ hx').trans (le_abs_self _)
  tfae_have 6 → 1
  · rintro h x hx
    obtain ⟨r, hr⟩ := h hx
    obtain ⟨ε, hε, hεD⟩ := Metric.mem_nhds_iff.1 <| Filter.inter_mem (hC.mem_nhds hx) hr
    simp [hC.nhdsWithin_eq hx, subset_inter_iff] at hεD ⊢
    obtain ⟨K, hK⟩ := exists_lipschitzOnWith_of_isBounded (hf.subset hεD.1 (convex_ball ..))
      (half_pos hε) <| isBounded_iff_forall_norm_le.2 ⟨r, by simpa using hεD.2⟩
    exact ⟨K, _, ball_mem_nhds _ (by simpa), hK⟩
  tfae_finish

lemma ConcaveOn.continuousOn_tfae (hC : IsOpen C) (hC' : C.Nonempty) (hf : ConcaveOn ℝ C f) :
    TFAE [LocallyLipschitzOn C f, ContinuousOn f C, ∃ x₀ ∈ C, ContinuousAt f x₀,
      ∃ x₀ ∈ C, (𝓝 x₀).IsBoundedUnder (· ≥ ·) f,
      ∀ ⦃x⦄, x ∈ C → (𝓝 x).IsBoundedUnder (· ≥ ·) f,
      ∀ ⦃x⦄, x ∈ C → (𝓝 x).IsBoundedUnder (· ≤ ·) |f|] := by
  have := hf.neg.continuousOn_tfae hC hC'
  simp at this
  convert this using 8 <;> exact (Equiv.neg ℝ).exists_congr (by simp)

lemma ConvexOn.locallyLipschitzOn_iff_continuousOn (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
    LocallyLipschitzOn C f ↔ ContinuousOn f C := by
  obtain rfl | hC' := C.eq_empty_or_nonempty
  · simp
  · exact (hf.continuousOn_tfae hC hC').out 0 1

lemma ConcaveOn.locallyLipschitzOn_iff_continuousOn (hC : IsOpen C) (hf : ConcaveOn ℝ C f) :
    LocallyLipschitzOn C f ↔ ContinuousOn f C := by
  simpa using hf.neg.locallyLipschitzOn_iff_continuousOn hC

protected lemma ConvexOn.locallyLipschitzOn (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
    LocallyLipschitzOn C f := by
  obtain rfl | ⟨x₀, hx₀⟩ := C.eq_empty_or_nonempty
  · simp
  · obtain ⟨b, hx₀b, hbC⟩ := exists_mem_interior_convexHull_affineBasis (hC.mem_nhds hx₀)
    refine ((hf.continuousOn_tfae hC ⟨x₀, hx₀⟩).out 3 0).mp ?_
    refine ⟨x₀, hx₀, BddAbove.isBoundedUnder (IsOpen.mem_nhds isOpen_interior hx₀b) ?_⟩
    exact (hf.bddAbove_convexHull ((subset_convexHull ..).trans hbC)
      ((finite_range _).image _).bddAbove).mono (by gcongr; exact interior_subset)

protected lemma ConcaveOn.locallyLipschitzOn (hC : IsOpen C) (hf : ConcaveOn ℝ C f) :
    LocallyLipschitzOn C f := by simpa using hf.neg.locallyLipschitzOn hC

protected lemma ConvexOn.continuousOn (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
    ContinuousOn f C := (hf.locallyLipschitzOn hC).continuousOn

protected lemma ConcaveOn.continuousOn (hC : IsOpen C) (hf : ConcaveOn ℝ C f) :
    ContinuousOn f C := (hf.locallyLipschitzOn hC).continuousOn

lemma ConvexOn.locallyLipschitzOn_interior (hf : ConvexOn ℝ C f) :
    LocallyLipschitzOn (interior C) f :=
  (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior

lemma ConcaveOn.locallyLipschitzOn_interior (hf : ConcaveOn ℝ C f) :
    LocallyLipschitzOn (interior C) f :=
  (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior

lemma ConvexOn.continuousOn_interior (hf : ConvexOn ℝ C f) : ContinuousOn f (interior C) :=
  hf.locallyLipschitzOn_interior.continuousOn

lemma ConcaveOn.continuousOn_interior (hf : ConcaveOn ℝ C f) : ContinuousOn f (interior C) :=
  hf.locallyLipschitzOn_interior.continuousOn

protected lemma ConvexOn.locallyLipschitz (hf : ConvexOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn_interior

protected lemma ConcaveOn.locallyLipschitz (hf : ConcaveOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn_interior

-- proof_wanted ConvexOn.locallyLipschitzOn_intrinsicInterior (hf : ConvexOn ℝ C f) :
--     ContinuousOn f (intrinsicInterior ℝ C)

-- proof_wanted ConcaveOn.locallyLipschitzOn_intrinsicInterior (hf : ConcaveOn ℝ C f) :
--     ContinuousOn f (intrinsicInterior ℝ C)

-- proof_wanted ConvexOn.continuousOn_intrinsicInterior (hf : ConvexOn ℝ C f) :
--     ContinuousOn f (intrinsicInterior ℝ C)

-- proof_wanted ConcaveOn.continuousOn_intrinsicInterior (hf : ConcaveOn ℝ C f) :
--     ContinuousOn f (intrinsicInterior ℝ C)
