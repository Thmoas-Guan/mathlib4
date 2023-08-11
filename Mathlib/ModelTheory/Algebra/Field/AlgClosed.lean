/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Algebra.Field.CharP
import Mathlib.ModelTheory.Algebra.Field.FreeCommRing
import Mathlib.RingTheory.FreeCommRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Nat.PrimeFin

namespace FirstOrder

namespace Language

open field FreeCommRing BigOperators Polynomial

variable {K : Type _} [CompatibleField K]

def genericMonicPoly (n : ℕ) : FreeCommRing (Fin (n + 1)) :=
    of (Fin.last _) ^ n + ∑ i : Fin n, of i.castSucc * of (Fin.last _) ^ (i : ℕ)

def monicPolyEquivFin {R : Type _} [CommRing R] [DecidableEq R]
    [Nontrivial R] (n : ℕ) :
    { p : R[X] // p.Monic ∧ p.natDegree = n } ≃ (Fin n → R) :=
  { toFun := fun p i => p.1.coeff i
    invFun := fun v =>
      let p := Polynomial.ofFinsupp
        { toFun := fun i =>
            if h : i < n then v ⟨i, h⟩
            else if i = n then 1 else 0
          support := (Finset.range (n+1)).filter
            (fun i => ∀ h : i < n, v ⟨i, h⟩ ≠ 0 ),
          mem_support_toFun := by
            intro i
            simp
            split_ifs with hi₁ hi₂
            · simp only [Nat.lt_succ_of_lt hi₁, true_and]
              exact ⟨fun h => h hi₁, fun h _ => h⟩
            · subst i
              simp only [lt_add_iff_pos_right, true_and, one_ne_zero,
                not_false_eq_true, iff_true]
              exact fun h => (lt_irrefl _ h).elim
            · simp only [not_true, iff_false, not_and, not_forall, not_not,
                Nat.lt_succ_iff]
              intro h
              exact (hi₂ (le_antisymm h (not_lt.1 hi₁))).elim }
      have hpn : p.natDegree = n := by
        refine le_antisymm ?_ ?_
        · refine natDegree_le_iff_coeff_eq_zero.2 ?_
          intro i hi
          simp [not_lt_of_gt hi, ne_of_gt hi]
        · refine le_natDegree_of_ne_zero ?_
          simp
      have hpm : p.Monic := by
        simp [Monic.def, leadingCoeff, hpn]
      ⟨p, hpm, hpn⟩
    left_inv := by
      intro p
      ext i
      simp only [ne_eq, Finset.mem_range, dite_eq_ite, coeff_ofFinsupp,
        Finsupp.coe_mk, ite_eq_left_iff, not_lt]
      intro hni
      cases lt_or_eq_of_le hni with
      | inr =>
        subst n
        have := p.2.1
        simp [Monic.def, leadingCoeff, p.2.2] at this
        simp [this]
      | inl h =>
        rw [eq_comm, if_neg (ne_of_gt h)]
        exact coeff_eq_zero_of_natDegree_lt (p.2.2.symm ▸ h)
    right_inv := fun _ => by simp }

theorem lift_genericMonicPoly {R : Type _} [CommRing R] [DecidableEq R] [Nontrivial R]
    {n : ℕ} (v : Fin (n+1) → R) :
    FreeCommRing.lift v (genericMonicPoly n) =
    ((monicPolyEquivFin n).symm (v ∘ Fin.castSucc)).1.eval (v (Fin.last _)) := by
  let p := (monicPolyEquivFin n).symm (v ∘ Fin.castSucc)
  simp only [genericMonicPoly, map_add, map_pow, lift_of, map_sum, map_mul,
    eval_eq_sum_range, p.2.2]
  simp [monicPolyEquivFin, Finset.sum_range_succ, add_comm,
    Finset.sum_range, Fin.castSucc, Fin.castAdd, Fin.castLE]

noncomputable def genericMonicPolyHasRoot (n : ℕ) : Language.field.Sentence :=
  (∃' ((termOfFreeCommRing (genericMonicPoly n)).relabel Sum.inr =' 0)).alls

theorem realize_genericMonicPolyHasRoot (n : ℕ) :
    K ⊨ genericMonicPolyHasRoot n ↔
      ∀ p : { p : K[X] // p.Monic ∧ p.natDegree = n }, ∃ x, p.1.eval x = 0 := by
  letI := Classical.decEq K
  rw [Equiv.forall_congr_left' (monicPolyEquivFin n)]
  simp only [Sentence.Realize, genericMonicPolyHasRoot, BoundedFormula.realize_alls,
    BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual, Term.realize_relabel,
    Sum.elim_comp_inr, realize_termOfFreeCommRing, lift_genericMonicPoly, Fin.snoc_last,
    Fin.snoc_comp_castSucc, Term.realize, CompatibleField.funMap_zero]

def Theory.ACF (p : ℕ) : Theory Language.field :=
  Theory.hasChar p ∪ Theory.field ∪ ⋃ (n : ℕ) (_ : 0 < n), {genericMonicPolyHasRoot n}

instance {K : Type _} [CompatibleField K] [CharP K p] [IsAlgClosed K] :
    (Theory.ACF p).Model K := by
  refine Theory.model_union_iff.2
    ⟨Theory.model_union_iff.2 ⟨model_hasChar_of_charP, inferInstance⟩, ?_⟩
  simp only [Theory.model_iff, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop, forall_exists_index, and_imp]
  rintro _ n hn0 rfl
  rw [realize_genericMonicPolyHasRoot]
  rintro ⟨p, _, rfl⟩
  exact IsAlgClosed.exists_root p (ne_of_gt
    (natDegree_pos_iff_degree_pos.1 hn0))

def CompatibleFieldOfModelACF (p : ℕ) (K : Type _) [Language.field.Structure K]
    [h : (Theory.ACF p).Model K] : CompatibleField K := by
  haveI : Theory.field.Model K :=
    Theory.Model.mono h (Set.subset_union_of_subset_left
      (Set.subset_union_right _ _) _)
  exact compatibleFieldOfFieldStructure K

theorem isAlgClosed_of_model_ACF (p : ℕ) (M : Type _)
    [CompatibleField M] [h : (Theory.ACF p).Model M] :
    IsAlgClosed M := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have h : M ⊨ (⋃ (n : ℕ) (_ : 0 < n), {genericMonicPolyHasRoot n}) :=
    Theory.Model.mono h (by simp [Theory.ACF])
  simp only [Theory.model_iff, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop, forall_exists_index, and_imp] at h
  have := h _ p.natDegree (natDegree_pos_iff_degree_pos.2
    (degree_pos_of_irreducible hpi)) rfl
  rw [realize_genericMonicPolyHasRoot] at this
  exact this ⟨_, hpm, rfl⟩

theorem charP_of_model_ACF (p : ℕ) (M : Type _)
    [CompatibleField M] [h : (Theory.ACF p).Model M] :
    CharP M p := by
  have : (Theory.hasChar p).Model M :=
    Theory.Model.mono h
      (Set.subset_union_of_subset_left (Set.subset_union_left _ _) _)
  exact charP_of_model_hasChar

set_option synthInstance.maxHeartbeats 100000 in
theorem ACF0_isSatisfiable : (Theory.ACF 0).IsSatisfiable := by
  letI := compatibleFieldOfField (AlgebraicClosure ℚ)
  haveI : CharP (AlgebraicClosure ℚ) 0 :=
    charP_of_injective_algebraMap
      (RingHom.injective (algebraMap ℚ (AlgebraicClosure ℚ))) 0
  exact ⟨⟨AlgebraicClosure ℚ⟩⟩

theorem ACF0_isSatisfiable_of_prime {p : ℕ} (hp : p.Prime) :
    (Theory.ACF p).IsSatisfiable := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI := compatibleFieldOfField (AlgebraicClosure (ZMod p))
  haveI : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap
      (RingHom.injective (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) p
  exact ⟨⟨AlgebraicClosure (ZMod p)⟩⟩

theorem ACF_isSatisfiable_of_prime_or_zero {p : ℕ} (hp : p.Prime ∨ p = 0) :
    (Theory.ACF p).IsSatisfiable := by
  cases hp with
  | inl hp => exact ACF0_isSatisfiable_of_prime hp
  | inr hp => exact hp ▸ ACF0_isSatisfiable

open Cardinal

theorem ACF_isComplete_of_prime_or_zero {p : ℕ} (hp : p.Prime ∨ p = 0) :
    (Theory.ACF p).IsComplete := by
  apply Categorical.isComplete.{0, 0, 0} (Order.succ ℵ₀) _ _
    (Order.le_succ ℵ₀)
  · simp only [card_field, lift_id']
    exact le_trans (le_of_lt (lt_aleph0_of_finite _)) (Order.le_succ _)
  · exact ACF_isSatisfiable_of_prime_or_zero hp
  · rintro ⟨M⟩
    letI := CompatibleFieldOfModelACF p M
    letI := isAlgClosed_of_model_ACF p M
    infer_instance
  · rintro ⟨M⟩ ⟨N⟩ hM hN
    letI := CompatibleFieldOfModelACF p M
    haveI := isAlgClosed_of_model_ACF p M
    haveI := charP_of_model_ACF p M
    letI := CompatibleFieldOfModelACF p N
    haveI := isAlgClosed_of_model_ACF p N
    haveI := charP_of_model_ACF p N
    constructor
    refine languageEquivEquivRingEquiv ?_
    apply Classical.choice
    refine IsAlgClosed.ringEquivOfCardinalEqOfCharEq p ?_ ?_
    · rw [hM]; exact Order.lt_succ _
    · rw [hM, hN]

theorem ACF0_realize_of_infinite_ACF_prime_realize (φ : Language.field.Sentence)
    (hφ : Set.Infinite { p : Nat.Primes | (Theory.ACF p) ⊨ᵇ φ }) :
    Theory.ACF 0 ⊨ᵇ φ := by
  rw [← @not_not (_ ⊨ᵇ _), ← (ACF_isComplete_of_prime_or_zero (Or.inr rfl)).models_not_iff,
    Theory.models_iff_finset_models]
  push_neg
  intro T0 hT0
  have h1 : ∀ φ ∈ Theory.ACF 0,
      { s : Finset Nat.Primes // ∀ p : Nat.Primes, (¬ (Theory.ACF p) ⊨ᵇ φ) → p ∈ s } := by
    intro φ hφ
    rw [Theory.ACF, Theory.hasChar, Set.union_assoc, Set.mem_union,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion] at hφ
    simp only [Set.mem_iUnion] at hφ
    apply Classical.choice
    rcases hφ with (rfl | ⟨n, hn, rfl⟩) | h
    · refine ⟨⟨∅, ?_⟩⟩
      simp only [Finset.not_mem_empty, Theory.ModelsBoundedFormula, eqZero, Term.equal,
        Nat.cast_zero, Term.relabel, BoundedFormula.realize_bdEqual, Term.realize_relabel,
        Sum.elim_comp_inl, Term.realize_func, Fin.forall_fin_zero_pi, not_forall,
        false_iff, not_exists, not_not, imp_false]
      intro p X _
      letI := CompatibleFieldOfModelACF p X
      simp
    · refine ⟨⟨((Nat.factors n).pmap (fun (p : ℕ) (hp : p.Prime) => ⟨p, hp⟩)
        (fun p => Nat.prime_of_mem_factors)).toFinset, ?_⟩⟩
      intro p hpT
      simp only [List.mem_toFinset, List.mem_pmap]
      simp only [isUnit_zero_iff, zero_dvd_iff] at hn
      suffices : (p : ℕ) ∣ n
      · rw [← Nat.mem_factors_iff_dvd hn p.2] at this
        exact  ⟨_, this, rfl⟩
      simp only [(ACF_isComplete_of_prime_or_zero (Or.inl p.2)).models_not_iff, not_not] at hpT
      simp only [Theory.models_sentence_iff, Nat.isUnit_iff, Sentence.Realize, eqZero, zero_def,
        Formula.realize_equal, Term.realize_constants, constantMap] at hpT
      rcases ACF_isSatisfiable_of_prime_or_zero (Or.inl p.2) with ⟨M⟩
      letI := CompatibleFieldOfModelACF p M
      haveI := charP_of_model_ACF p M
      have := hpT M
      simp only [realize_termOfFreeCommRing, map_natCast, CompatibleField.funMap_zero] at this
      rwa [CharP.cast_eq_zero_iff M p n] at this
    · refine ⟨⟨∅, ?_⟩⟩
      simp only [Finset.not_mem_empty, false_iff, not_not, imp_false]
      intro p
      simp only [Theory.ACF, Set.union_assoc]
      exact Theory.models_sentence_of_mem (Set.mem_union_right _ h)
  have h : ∃ p ∈ { p : Nat.Primes | (Theory.ACF p) ⊨ᵇ φ },
      ∀ φ ∈ T0, Theory.ACF p ⊨ᵇ φ := by
    let s : Finset Nat.Primes := T0.attach.biUnion (fun φ => h1 φ (hT0 φ.2))
    have hs : ∀ (p : Nat.Primes) φ, φ ∈ T0 → ¬ (Theory.ACF p) ⊨ᵇ φ → p ∈ s := by
      intro p φ hφ hpφ
      refine Finset.mem_biUnion.2 ?_
      refine ⟨⟨φ, hφ⟩, Finset.mem_attach _ _, ?_⟩
      exact (h1 φ (hT0 hφ)).2 p hpφ
    have : ∃ p ∈ { p : Nat.Primes | (Theory.ACF p) ⊨ᵇ φ }, p ∉ s :=
      hφ.exists_not_mem_finset s
    rcases this with ⟨p, hp₁, hp₂⟩
    refine ⟨p, hp₁, ?_⟩
    intro φ hφ
    exact not_not.1 (mt (hs p φ hφ) hp₂)
  rcases h with ⟨p, hp1, hp2⟩
  intro h
  have : Theory.ACF p ⊨ᵇ Formula.not φ := Theory.models_of_models_theory hp2 h
  rw [(ACF_isComplete_of_prime_or_zero (Or.inl p.2)).models_not_iff] at this
  exact this hp1

/-- The Lefschetz principle. A first order sentence is modeled by the theory
of algebraically closed fields of characteristic zero if and only if it is modeled by
the theory of algebraically closed fields of characteristic `p` for infinitely many `p`. -/
theorem ACF0_realize_iff_infinite_ACF_prime_realize {φ : Language.field.Sentence} :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Infinite { p : Nat.Primes | Theory.ACF p ⊨ᵇ φ } := by
  refine ⟨?_, ACF0_realize_of_infinite_ACF_prime_realize φ⟩
  rw [← not_imp_not, ← (ACF_isComplete_of_prime_or_zero (Or.inr rfl)).models_not_iff,
    Set.not_infinite]
  intro hs
  apply ACF0_realize_of_infinite_ACF_prime_realize
  apply Set.infinite_of_finite_compl
  convert hs using 1
  ext p
  simp [(ACF_isComplete_of_prime_or_zero (Or.inl p.2)).models_not_iff]

end Language

end FirstOrder
