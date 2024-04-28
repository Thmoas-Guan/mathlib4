/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Order.SuccPred.LinearLocallyFinite
import Mathlib.Probability.Martingale.Basic

#align_import probability.martingale.optional_sampling from "leanprover-community/mathlib"@"ba074af83b6cf54c3104e59402b39410ddbd6dca"

/-!
# Optional sampling theorem

If `τ` is a bounded stopping time and `σ` is another stopping time, then the value of a martingale
`f` at the stopping time `min τ σ` is almost everywhere equal to
`μ[stoppedValue f τ | hσ.measurableSpace]`.

## Main results

* `stoppedValue_ae_eq_condexp_of_le_const`: the value of a martingale `f` at a stopping time `τ`
  bounded by `n` is the conditional expectation of `f n` with respect to the σ-algebra generated by
  `τ`.
* `stoppedValue_ae_eq_condexp_of_le`: if `τ` and `σ` are two stopping times with `σ ≤ τ` and `τ` is
  bounded, then the value of a martingale `f` at `σ` is the conditional expectation of its value at
  `τ` with respect to the σ-algebra generated by `σ`.
* `stoppedValue_min_ae_eq_condexp`: the optional sampling theorem. If `τ` is a bounded stopping
  time and `σ` is another stopping time, then the value of a martingale `f` at the stopping time
  `min τ σ` is almost everywhere equal to the conditional expectation of `f` stopped at `τ`
  with respect to the σ-algebra generated by `σ`.

-/


open scoped MeasureTheory BigOperators ENNReal

open TopologicalSpace

namespace MeasureTheory

namespace Martingale

variable {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

section FirstCountableTopology

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [FirstCountableTopology ι] {ℱ : Filtration ι m} [SigmaFiniteFiltration μ ℱ] {τ σ : Ω → ι}
  {f : ι → Ω → E} {i n : ι}

theorem condexp_stopping_time_ae_eq_restrict_eq_const
    [(Filter.atTop : Filter ι).IsCountablyGenerated] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) [SigmaFinite (μ.trim hτ.measurableSpace_le)] (hin : i ≤ n) :
    μ[f n|hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] f i := by
  refine' Filter.EventuallyEq.trans _ (ae_restrict_of_ae (h.condexp_ae_eq hin))
  refine' condexp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le (ℱ.le i)
    (hτ.measurableSet_eq' i) fun t => _
  rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_eq_iff]
#align measure_theory.martingale.condexp_stopping_time_ae_eq_restrict_eq_const MeasureTheory.Martingale.condexp_stopping_time_ae_eq_restrict_eq_const

theorem condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le))] (i : ι) :
    μ[f n|hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] f i := by
  by_cases hin : i ≤ n
  · refine' Filter.EventuallyEq.trans _ (ae_restrict_of_ae (h.condexp_ae_eq hin))
    refine' condexp_ae_eq_restrict_of_measurableSpace_eq_on (hτ.measurableSpace_le_of_le hτ_le)
      (ℱ.le i) (hτ.measurableSet_eq' i) fun t => _
    rw [Set.inter_comm _ t, IsStoppingTime.measurableSet_inter_eq_iff]
  · suffices {x : Ω | τ x = i} = ∅ by simp [this]; norm_cast
    ext1 x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
    rintro rfl
    exact hin (hτ_le x)
#align measure_theory.martingale.condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const MeasureTheory.Martingale.condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const

theorem stoppedValue_ae_eq_restrict_eq (h : Martingale f ℱ μ) (hτ : IsStoppingTime ℱ τ)
    (hτ_le : ∀ x, τ x ≤ n) [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le))] (i : ι) :
    stoppedValue f τ =ᵐ[μ.restrict {x | τ x = i}] μ[f n|hτ.measurableSpace] := by
  refine' Filter.EventuallyEq.trans _
    (condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const h hτ hτ_le i).symm
  rw [Filter.EventuallyEq, ae_restrict_iff' (ℱ.le _ _ (hτ.measurableSet_eq i))]
  refine' Filter.eventually_of_forall fun x hx => _
  rw [Set.mem_setOf_eq] at hx
  simp_rw [stoppedValue, hx]
#align measure_theory.martingale.stopped_value_ae_eq_restrict_eq MeasureTheory.Martingale.stoppedValue_ae_eq_restrict_eq

/-- The value of a martingale `f` at a stopping time `τ` bounded by `n` is the conditional
expectation of `f n` with respect to the σ-algebra generated by `τ`. -/
theorem stoppedValue_ae_eq_condexp_of_le_const_of_countable_range (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n) (h_countable_range : (Set.range τ).Countable)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le))] :
    stoppedValue f τ =ᵐ[μ] μ[f n|hτ.measurableSpace] := by
  have : Set.univ = ⋃ i ∈ Set.range τ, {x | τ x = i} := by
    ext1 x
    simp only [Set.mem_univ, Set.mem_range, true_and_iff, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_iUnion, Set.mem_setOf_eq, exists_apply_eq_apply']
  nth_rw 1 [← @Measure.restrict_univ Ω _ μ]
  rw [this, ae_eq_restrict_biUnion_iff _ h_countable_range]
  exact fun i _ => stoppedValue_ae_eq_restrict_eq h _ hτ_le i
#align measure_theory.martingale.stopped_value_ae_eq_condexp_of_le_const_of_countable_range MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le_const_of_countable_range

/-- The value of a martingale `f` at a stopping time `τ` bounded by `n` is the conditional
expectation of `f n` with respect to the σ-algebra generated by `τ`. -/
theorem stoppedValue_ae_eq_condexp_of_le_const [Countable ι] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le))] :
    stoppedValue f τ =ᵐ[μ] μ[f n|hτ.measurableSpace] :=
  h.stoppedValue_ae_eq_condexp_of_le_const_of_countable_range hτ hτ_le (Set.to_countable _)
#align measure_theory.martingale.stopped_value_ae_eq_condexp_of_le_const MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le_const

/-- If `τ` and `σ` are two stopping times with `σ ≤ τ` and `τ` is bounded, then the value of a
martingale `f` at `σ` is the conditional expectation of its value at `τ` with respect to the
σ-algebra generated by `σ`. -/
theorem stoppedValue_ae_eq_condexp_of_le_of_countable_range (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
    (hτ_countable_range : (Set.range τ).Countable) (hσ_countable_range : (Set.range σ).Countable)
    [SigmaFinite (μ.trim (hσ.measurableSpace_le_of_le fun x => (hσ_le_τ x).trans (hτ_le x)))] :
    stoppedValue f σ =ᵐ[μ] μ[stoppedValue f τ|hσ.measurableSpace] := by
  have : SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le)) :=
    sigmaFiniteTrim_mono _ (IsStoppingTime.measurableSpace_mono hσ hτ hσ_le_τ)
  have : μ[stoppedValue f τ|hσ.measurableSpace] =ᵐ[μ]
      μ[μ[f n|hτ.measurableSpace]|hσ.measurableSpace] := condexp_congr_ae
    (h.stoppedValue_ae_eq_condexp_of_le_const_of_countable_range hτ hτ_le hτ_countable_range)
  refine' (Filter.EventuallyEq.trans _
    (condexp_condexp_of_le _ (hτ.measurableSpace_le_of_le hτ_le)).symm).trans this.symm
  · exact h.stoppedValue_ae_eq_condexp_of_le_const_of_countable_range hσ
      (fun x => (hσ_le_τ x).trans (hτ_le x)) hσ_countable_range
  · exact hσ.measurableSpace_mono hτ hσ_le_τ
#align measure_theory.martingale.stopped_value_ae_eq_condexp_of_le_of_countable_range MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le_of_countable_range

/-- If `τ` and `σ` are two stopping times with `σ ≤ τ` and `τ` is bounded, then the value of a
martingale `f` at `σ` is the conditional expectation of its value at `τ` with respect to the
σ-algebra generated by `σ`. -/
theorem stoppedValue_ae_eq_condexp_of_le [Countable ι] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
    [SigmaFinite (μ.trim hσ.measurableSpace_le)] :
    stoppedValue f σ =ᵐ[μ] μ[stoppedValue f τ|hσ.measurableSpace] :=
  h.stoppedValue_ae_eq_condexp_of_le_of_countable_range hτ hσ hσ_le_τ hτ_le (Set.to_countable _)
    (Set.to_countable _)
#align measure_theory.martingale.stopped_value_ae_eq_condexp_of_le MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le

end FirstCountableTopology

section SubsetOfNat

/-! In the following results the index set verifies
`[LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]`, which means that it is order-isomorphic to
a subset of `ℕ`. `ι` is equipped with the discrete topology, which is also the order topology,
and is a measurable space with the Borel σ-algebra. -/


variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι] [TopologicalSpace ι]
  [DiscreteTopology ι] [MeasurableSpace ι] [BorelSpace ι] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {ℱ : Filtration ι m} {τ σ : Ω → ι} {f : ι → Ω → E} {i n : ι}

theorem condexp_stoppedValue_stopping_time_ae_eq_restrict_le (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) [SigmaFinite (μ.trim hσ.measurableSpace_le)]
    (hτ_le : ∀ x, τ x ≤ n) :
    μ[stoppedValue f τ|hσ.measurableSpace] =ᵐ[μ.restrict {x : Ω | τ x ≤ σ x}] stoppedValue f τ := by
  rw [ae_eq_restrict_iff_indicator_ae_eq
    (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))]
  refine' (condexp_indicator (integrable_stoppedValue ι hτ h.integrable hτ_le)
    (hτ.measurableSet_stopping_time_le hσ)).symm.trans _
  have h_int :
      Integrable ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue (fun n : ι => f n) τ)) μ := by
    refine' (integrable_stoppedValue ι hτ h.integrable hτ_le).indicator _
    exact hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
  have h_meas : AEStronglyMeasurable' hσ.measurableSpace
      ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue (fun n : ι => f n) τ)) μ := by
    refine' StronglyMeasurable.aeStronglyMeasurable' _
    refine' StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
      (hτ.measurableSet_le_stopping_time hσ) _ _ _
    · intro t ht
      rw [Set.inter_comm _ t] at ht ⊢
      rw [hτ.measurableSet_inter_le_iff hσ, IsStoppingTime.measurableSet_min_iff hτ hσ] at ht
      exact ht.2
    · refine' StronglyMeasurable.indicator _ (hτ.measurableSet_le_stopping_time hσ)
      refine' Measurable.stronglyMeasurable _
      exact measurable_stoppedValue h.adapted.progMeasurable_of_discrete hτ
    · intro x hx
      simp only [hx, Set.indicator_of_not_mem, not_false_iff]
  exact condexp_of_aestronglyMeasurable' hσ.measurableSpace_le h_meas h_int
#align measure_theory.martingale.condexp_stopped_value_stopping_time_ae_eq_restrict_le MeasureTheory.Martingale.condexp_stoppedValue_stopping_time_ae_eq_restrict_le

-- Adaptation note: 2024-04-28
-- The change to typeclass resolution in
-- https://github.com/leanprover/lean4/pull/4003
-- (See also https://github.com/leanprover/lean4/issues/3996)
-- will hopefully significantly speed up typeclass search in Mathlib.
-- However it causes some breakages.
-- Currently, we're using the backwards compatibility flag to disable the new behaviour
-- as locally as possible, and leaving the task of cleaning this up for later.
set_option backward.synthInstance.canonInstances false in
/-- **Optional Sampling theorem**. If `τ` is a bounded stopping time and `σ` is another stopping
time, then the value of a martingale `f` at the stopping time `min τ σ` is almost everywhere equal
to the conditional expectation of `f` stopped at `τ` with respect to the σ-algebra generated
by `σ`. -/
theorem stoppedValue_min_ae_eq_condexp [SigmaFiniteFiltration μ ℱ] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    [h_sf_min : SigmaFinite (μ.trim (hτ.min hσ).measurableSpace_le)] :
    (stoppedValue f fun x => min (σ x) (τ x)) =ᵐ[μ] μ[stoppedValue f τ|hσ.measurableSpace] := by
  refine'
    (h.stoppedValue_ae_eq_condexp_of_le hτ (hσ.min hτ) (fun x => min_le_right _ _) hτ_le).trans _
  refine' ae_of_ae_restrict_of_ae_restrict_compl {x | σ x ≤ τ x} _ _
  · exact condexp_min_stopping_time_ae_eq_restrict_le hσ hτ
  · suffices μ[stoppedValue f τ|(hσ.min hτ).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ σ x}]
        μ[stoppedValue f τ|hσ.measurableSpace] by
      rw [ae_restrict_iff' (hσ.measurableSpace_le _ (hσ.measurableSet_le_stopping_time hτ).compl)]
      rw [Filter.EventuallyEq, ae_restrict_iff'] at this
      swap; · exact hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
      filter_upwards [this] with x hx hx_mem
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx_mem
      exact hx hx_mem.le
    apply Filter.EventuallyEq.trans _ ((condexp_min_stopping_time_ae_eq_restrict_le hτ hσ).trans _)
    · exact stoppedValue f τ
    · rw [IsStoppingTime.measurableSpace_min hσ, IsStoppingTime.measurableSpace_min hτ, inf_comm]
    · have h1 : μ[stoppedValue f τ|hτ.measurableSpace] = stoppedValue f τ := by
        refine' condexp_of_stronglyMeasurable hτ.measurableSpace_le _ _
        · refine' Measurable.stronglyMeasurable _
          exact measurable_stoppedValue h.adapted.progMeasurable_of_discrete hτ
        · exact integrable_stoppedValue ι hτ h.integrable hτ_le
      rw [h1]
      exact (condexp_stoppedValue_stopping_time_ae_eq_restrict_le h hτ hσ hτ_le).symm
#align measure_theory.martingale.stopped_value_min_ae_eq_condexp MeasureTheory.Martingale.stoppedValue_min_ae_eq_condexp

end SubsetOfNat

end Martingale

end MeasureTheory
