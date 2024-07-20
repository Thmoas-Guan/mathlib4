/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Probability.Kernel.Composition

/-!
# Invariance of measures along a kernel

We say that a measure `μ` is invariant with respect to a kernel `κ` if its push-forward along the
kernel `μ.bind κ` is the same measure.

## Main definitions

* `ProbabilityTheory.kernel.Invariant`: invariance of a given measure with respect to a kernel.

## Useful lemmas

* `ProbabilityTheory.kernel.const_bind_eq_comp_const`, and
  `ProbabilityTheory.kernel.comp_const_apply_eq_bind` established the relationship between
  the push-forward measure and the composition of kernels.

-/


open MeasureTheory

open scoped MeasureTheory ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

namespace kernel

/-! ### Push-forward of measures along a kernel -/


@[simp]
theorem bind_add (μ ν : Measure α) (κ : kernel α β) : (μ + ν).bind κ = μ.bind κ + ν.bind κ := by
  ext1 s hs
  rw [Measure.bind_apply hs (kernel.measurable _), lintegral_add_measure, Measure.coe_add,
    Pi.add_apply, Measure.bind_apply hs (kernel.measurable _),
    Measure.bind_apply hs (kernel.measurable _)]

@[simp]
theorem bind_smul (κ : kernel α β) (μ : Measure α) (r : ℝ≥0∞) : (r • μ).bind κ = r • μ.bind κ := by
  ext1 s hs
  rw [Measure.bind_apply hs (kernel.measurable _), lintegral_smul_measure, Measure.coe_smul,
    Pi.smul_apply, Measure.bind_apply hs (kernel.measurable _), smul_eq_mul]

theorem const_bind_eq_comp_const (κ : kernel α β) (μ : Measure α) :
    const α (μ.bind κ) = κ ∘ₖ const α μ := by
  ext a s hs
  simp_rw [comp_apply' _ _ _ hs, const_apply, Measure.bind_apply hs (kernel.measurable _)]

theorem comp_const_apply_eq_bind (κ : kernel α β) (μ : Measure α) (a : α) :
    (κ ∘ₖ const α μ) a = μ.bind κ := by
  rw [← const_apply (μ.bind κ) a, const_bind_eq_comp_const κ μ]

/-! ### Invariant measures of kernels -/


/-- A measure `μ` is invariant with respect to the kernel `κ` if the push-forward measure of `μ`
along `κ` equals `μ`. -/
def Invariant (κ : kernel α α) (μ : Measure α) : Prop :=
  μ.bind κ = μ

variable {κ η : kernel α α} {μ : Measure α}

theorem Invariant.def (hκ : Invariant κ μ) : μ.bind κ = μ :=
  hκ

theorem Invariant.comp_const (hκ : Invariant κ μ) : κ ∘ₖ const α μ = const α μ := by
  rw [← const_bind_eq_comp_const κ μ, hκ.def]

theorem Invariant.comp [IsSFiniteKernel κ] (hκ : Invariant κ μ) (hη : Invariant η μ) :
    Invariant (κ ∘ₖ η) μ := by
  cases' isEmpty_or_nonempty α with _ hα
  · exact Subsingleton.elim _ _
  · simp_rw [Invariant, ← comp_const_apply_eq_bind (κ ∘ₖ η) μ hα.some, comp_assoc, hη.comp_const,
      hκ.comp_const, const_apply]

end kernel

end ProbabilityTheory
