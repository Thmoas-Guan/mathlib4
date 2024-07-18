/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.IntervalCases

#align_import group_theory.specific_groups.alternating from "leanprover-community/mathlib"@"0f6670b8af2dff699de1c0b4b49039b31bc13c46"

/-!
# Alternating Groups

The alternating group on a finite type `α` is the subgroup of the permutation group `Perm α`
consisting of the even permutations.

## Main definitions

* `alternatingGroup α` is the alternating group on `α`, defined as a `Subgroup (Perm α)`.

## Main results
* `two_mul_card_alternatingGroup` shows that the alternating group is half as large as
  the permutation group it is a subgroup of.

* `closure_three_cycles_eq_alternating` shows that the alternating group is
  generated by 3-cycles.

* `alternatingGroup.isSimpleGroup_five` shows that the alternating group on `Fin 5` is simple.
  The proof shows that the normal closure of any non-identity element of this group contains a
  3-cycle.

## Tags
alternating group permutation


## TODO
* Show that `alternatingGroup α` is simple if and only if `Fintype.card α ≠ 4`.

-/

-- An example on how to determine the order of an element of a finite group.
example : orderOf (-1 : ℤˣ) = 2 :=
  orderOf_eq_prime (Int.units_sq _) (by decide)

open Equiv Equiv.Perm Subgroup Fintype

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- The alternating group on a finite type, realized as a subgroup of `Equiv.Perm`.
  For $A_n$, use `alternatingGroup (Fin n)`. -/
def alternatingGroup : Subgroup (Perm α) :=
  sign.ker
#align alternating_group alternatingGroup

-- Porting note (#10754): manually added instance
instance fta : Fintype (alternatingGroup α) :=
  @Subtype.fintype _ _ sign.decidableMemKer _

instance [Subsingleton α] : Unique (alternatingGroup α) :=
  ⟨⟨1⟩, fun ⟨p, _⟩ => Subtype.eq (Subsingleton.elim p _)⟩

variable {α}

theorem alternatingGroup_eq_sign_ker : alternatingGroup α = sign.ker :=
  rfl
#align alternating_group_eq_sign_ker alternatingGroup_eq_sign_ker

namespace Equiv.Perm

@[simp]
theorem mem_alternatingGroup {f : Perm α} : f ∈ alternatingGroup α ↔ sign f = 1 :=
  sign.mem_ker
#align equiv.perm.mem_alternating_group Equiv.Perm.mem_alternatingGroup

theorem prod_list_swap_mem_alternatingGroup_iff_even_length {l : List (Perm α)}
    (hl : ∀ g ∈ l, IsSwap g) : l.prod ∈ alternatingGroup α ↔ Even l.length := by
  rw [mem_alternatingGroup, sign_prod_list_swap hl, neg_one_pow_eq_one_iff_even]
  decide
#align equiv.perm.prod_list_swap_mem_alternating_group_iff_even_length Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length

theorem IsThreeCycle.mem_alternatingGroup {f : Perm α} (h : IsThreeCycle f) :
    f ∈ alternatingGroup α :=
  Perm.mem_alternatingGroup.mpr h.sign
#align equiv.perm.is_three_cycle.mem_alternating_group Equiv.Perm.IsThreeCycle.mem_alternatingGroup

set_option linter.deprecated false in
theorem finRotate_bit1_mem_alternatingGroup {n : ℕ} :
    finRotate (2 * n + 1) ∈ alternatingGroup (Fin (2 * n + 1)) := by
  rw [mem_alternatingGroup, sign_finRotate, pow_mul, pow_two, Int.units_mul_self, one_pow]
#align equiv.perm.fin_rotate_bit1_mem_alternating_group Equiv.Perm.finRotate_bit1_mem_alternatingGroup

end Equiv.Perm

theorem two_mul_card_alternatingGroup [Nontrivial α] :
    2 * card (alternatingGroup α) = card (Perm α) := by
  let this := (QuotientGroup.quotientKerEquivOfSurjective _ (sign_surjective α)).toEquiv
  rw [← Fintype.card_units_int, ← Fintype.card_congr this]
  simp only [← Nat.card_eq_fintype_card]
  apply (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
#align two_mul_card_alternating_group two_mul_card_alternatingGroup

namespace alternatingGroup

open Equiv.Perm

instance normal : (alternatingGroup α).Normal :=
  sign.normal_ker
#align alternating_group.normal alternatingGroup.normal

theorem isConj_of {σ τ : alternatingGroup α} (hc : IsConj (σ : Perm α) (τ : Perm α))
    (hσ : (σ : Perm α).support.card + 2 ≤ Fintype.card α) : IsConj σ τ := by
  obtain ⟨σ, hσ⟩ := σ
  obtain ⟨τ, hτ⟩ := τ
  obtain ⟨π, hπ⟩ := isConj_iff.1 hc
  rw [Subtype.coe_mk, Subtype.coe_mk] at hπ
  cases' Int.units_eq_one_or (Perm.sign π) with h h
  · rw [isConj_iff]
    refine ⟨⟨π, mem_alternatingGroup.mp h⟩, Subtype.val_injective ?_⟩
    simpa only [Subtype.val, Subgroup.coe_mul, coe_inv, coe_mk] using hπ
  · have h2 : 2 ≤ σ.supportᶜ.card := by
      rw [Finset.card_compl, le_tsub_iff_left σ.support.card_le_univ]
      exact hσ
    obtain ⟨a, ha, b, hb, ab⟩ := Finset.one_lt_card.1 h2
    refine isConj_iff.2 ⟨⟨π * swap a b, ?_⟩, Subtype.val_injective ?_⟩
    · rw [mem_alternatingGroup, MonoidHom.map_mul, h, sign_swap ab, Int.units_mul_self]
    · simp only [← hπ, coe_mk, Subgroup.coe_mul, Subtype.val]
      have hd : Disjoint (swap a b) σ := by
        rw [disjoint_iff_disjoint_support, support_swap ab, Finset.disjoint_insert_left,
          Finset.disjoint_singleton_left]
        exact ⟨Finset.mem_compl.1 ha, Finset.mem_compl.1 hb⟩
      rw [mul_assoc π _ σ, hd.commute.eq, coe_inv, coe_mk]
      simp [mul_assoc]
#align alternating_group.is_conj_of alternatingGroup.isConj_of

theorem isThreeCycle_isConj (h5 : 5 ≤ Fintype.card α) {σ τ : alternatingGroup α}
    (hσ : IsThreeCycle (σ : Perm α)) (hτ : IsThreeCycle (τ : Perm α)) : IsConj σ τ :=
  alternatingGroup.isConj_of (isConj_iff_cycleType_eq.2 (hσ.trans hτ.symm))
    (by rwa [hσ.card_support])
#align alternating_group.is_three_cycle_is_conj alternatingGroup.isThreeCycle_isConj

end alternatingGroup

namespace Equiv.Perm

open alternatingGroup

@[simp]
theorem closure_three_cycles_eq_alternating :
    closure { σ : Perm α | IsThreeCycle σ } = alternatingGroup α :=
  closure_eq_of_le _ (fun σ hσ => mem_alternatingGroup.2 hσ.sign) fun σ hσ => by
    suffices hind :
      ∀ (n : ℕ) (l : List (Perm α)) (_ : ∀ g, g ∈ l → IsSwap g) (_ : l.length = 2 * n),
        l.prod ∈ closure { σ : Perm α | IsThreeCycle σ } by
      obtain ⟨l, rfl, hl⟩ := truncSwapFactors σ
      obtain ⟨n, hn⟩ := (prod_list_swap_mem_alternatingGroup_iff_even_length hl).1 hσ
      rw [← two_mul] at hn
      exact hind n l hl hn
    intro n
    induction' n with n ih <;> intro l hl hn
    · simp [List.length_eq_zero.1 hn, one_mem]
    rw [Nat.mul_succ] at hn
    obtain ⟨a, l, rfl⟩ := l.exists_of_length_succ hn
    rw [List.length_cons, Nat.succ_inj'] at hn
    obtain ⟨b, l, rfl⟩ := l.exists_of_length_succ hn
    rw [List.prod_cons, List.prod_cons, ← mul_assoc]
    rw [List.length_cons, Nat.succ_inj'] at hn
    exact
      mul_mem
        (IsSwap.mul_mem_closure_three_cycles (hl a (List.mem_cons_self a _))
          (hl b (List.mem_cons_of_mem a (l.mem_cons_self b))))
        (ih _ (fun g hg => hl g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))) hn)
#align equiv.perm.closure_three_cycles_eq_alternating Equiv.Perm.closure_three_cycles_eq_alternating

/-- A key lemma to prove $A_5$ is simple. Shows that any normal subgroup of an alternating group on
  at least 5 elements is the entire alternating group if it contains a 3-cycle. -/
theorem IsThreeCycle.alternating_normalClosure (h5 : 5 ≤ Fintype.card α) {f : Perm α}
    (hf : IsThreeCycle f) :
    normalClosure ({⟨f, hf.mem_alternatingGroup⟩} : Set (alternatingGroup α)) = ⊤ :=
  eq_top_iff.2
    (by
      have hi : Function.Injective (alternatingGroup α).subtype := Subtype.coe_injective
      refine eq_top_iff.1 (map_injective hi (le_antisymm (map_mono le_top) ?_))
      rw [← MonoidHom.range_eq_map, subtype_range, normalClosure, MonoidHom.map_closure]
      refine (le_of_eq closure_three_cycles_eq_alternating.symm).trans (closure_mono ?_)
      intro g h
      obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (hf.trans h.symm))
      refine ⟨⟨c * f * c⁻¹, h.mem_alternatingGroup⟩, ?_, rfl⟩
      rw [Group.mem_conjugatesOfSet_iff]
      exact ⟨⟨f, hf.mem_alternatingGroup⟩, Set.mem_singleton _, isThreeCycle_isConj h5 hf h⟩)
#align equiv.perm.is_three_cycle.alternating_normal_closure Equiv.Perm.IsThreeCycle.alternating_normalClosure

/-- Part of proving $A_5$ is simple. Shows that the square of any element of $A_5$ with a 3-cycle in
  its cycle decomposition is a 3-cycle, so the normal closure of the original element must be
  $A_5$. -/
theorem isThreeCycle_sq_of_three_mem_cycleType_five {g : Perm (Fin 5)} (h : 3 ∈ cycleType g) :
    IsThreeCycle (g * g) := by
  obtain ⟨c, g', rfl, hd, _, h3⟩ := mem_cycleType_iff.1 h
  simp only [mul_assoc]
  rw [hd.commute.eq, ← mul_assoc g']
  suffices hg' : orderOf g' ∣ 2 by
    rw [← pow_two, orderOf_dvd_iff_pow_eq_one.1 hg', one_mul]
    exact (card_support_eq_three_iff.1 h3).isThreeCycle_sq
  rw [← lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  rw [le_antisymm (two_le_of_mem_cycleType hn) (le_trans (le_card_support_of_mem_cycleType hn) _)]
  apply le_of_add_le_add_left
  rw [← hd.card_support_mul, h3]
  exact (c * g').support.card_le_univ
#align equiv.perm.is_three_cycle_sq_of_three_mem_cycle_type_five Equiv.Perm.isThreeCycle_sq_of_three_mem_cycleType_five

end Equiv.Perm

namespace alternatingGroup

open Equiv.Perm

theorem nontrivial_of_three_le_card (h3 : 3 ≤ card α) : Nontrivial (alternatingGroup α) := by
  haveI := Fintype.one_lt_card_iff_nontrivial.1 (lt_trans (by decide) h3)
  rw [← Fintype.one_lt_card_iff_nontrivial]
  refine lt_of_mul_lt_mul_left ?_ (le_of_lt Nat.prime_two.pos)
  rw [two_mul_card_alternatingGroup, card_perm, ← Nat.succ_le_iff]
  exact le_trans h3 (card α).self_le_factorial
#align alternating_group.nontrivial_of_three_le_card alternatingGroup.nontrivial_of_three_le_card

instance {n : ℕ} : Nontrivial (alternatingGroup (Fin (n + 3))) :=
  nontrivial_of_three_le_card
    (by
      rw [card_fin]
      exact le_add_left (le_refl 3))

/-- The normal closure of the 5-cycle `finRotate 5` within $A_5$ is the whole group. This will be
  used to show that the normal closure of any 5-cycle within $A_5$ is the whole group. -/
theorem normalClosure_finRotate_five : normalClosure ({⟨finRotate 5,
    finRotate_bit1_mem_alternatingGroup (n := 2)⟩} : Set (alternatingGroup (Fin 5))) = ⊤ :=
  eq_top_iff.2
    (by
      have h3 :
        IsThreeCycle (Fin.cycleRange 2 * finRotate 5 * (Fin.cycleRange 2)⁻¹ * (finRotate 5)⁻¹) :=
        card_support_eq_three_iff.1 (by decide)
      rw [← h3.alternating_normalClosure (by rw [card_fin])]
      refine normalClosure_le_normal ?_
      rw [Set.singleton_subset_iff, SetLike.mem_coe]
      have h :
        (⟨finRotate 5, finRotate_bit1_mem_alternatingGroup (n := 2)⟩ : alternatingGroup (Fin 5)) ∈
          normalClosure _ :=
        SetLike.mem_coe.1 (subset_normalClosure (Set.mem_singleton _))
      exact (mul_mem (Subgroup.normalClosure_normal.conj_mem _ h
        -- Porting note: added `: _`
        ⟨Fin.cycleRange 2, Fin.isThreeCycle_cycleRange_two.mem_alternatingGroup⟩) (inv_mem h) : _))
#align alternating_group.normal_closure_fin_rotate_five alternatingGroup.normalClosure_finRotate_five

/-- The normal closure of $(04)(13)$ within $A_5$ is the whole group. This will be
  used to show that the normal closure of any permutation of cycle type $(2,2)$ is the whole group.
  -/
theorem normalClosure_swap_mul_swap_five :
    normalClosure
        ({⟨swap 0 4 * swap 1 3, mem_alternatingGroup.2 (by decide)⟩} :
          Set (alternatingGroup (Fin 5))) =
      ⊤ := by
  let g1 := (⟨swap 0 2 * swap 0 1, mem_alternatingGroup.2 (by decide)⟩ : alternatingGroup (Fin 5))
  let g2 := (⟨swap 0 4 * swap 1 3, mem_alternatingGroup.2 (by decide)⟩ : alternatingGroup (Fin 5))
  have h5 : g1 * g2 * g1⁻¹ * g2⁻¹ =
      ⟨finRotate 5, finRotate_bit1_mem_alternatingGroup (n := 2)⟩ := by
    rw [Subtype.ext_iff]
    simp only [Fin.val_mk, Subgroup.coe_mul, Subgroup.coe_inv, Fin.val_mk]
    decide
  rw [eq_top_iff, ← normalClosure_finRotate_five]
  refine normalClosure_le_normal ?_
  rw [Set.singleton_subset_iff, SetLike.mem_coe, ← h5]
  have h : g2 ∈ normalClosure {g2} :=
    SetLike.mem_coe.1 (subset_normalClosure (Set.mem_singleton _))
  exact mul_mem (Subgroup.normalClosure_normal.conj_mem _ h g1) (inv_mem h)
#align alternating_group.normal_closure_swap_mul_swap_five alternatingGroup.normalClosure_swap_mul_swap_five

/-- Shows that any non-identity element of $A_5$ whose cycle decomposition consists only of swaps
  is conjugate to $(04)(13)$. This is used to show that the normal closure of such a permutation
  in $A_5$ is $A_5$. -/
theorem isConj_swap_mul_swap_of_cycleType_two {g : Perm (Fin 5)} (ha : g ∈ alternatingGroup (Fin 5))
    (h1 : g ≠ 1) (h2 : ∀ n, n ∈ cycleType (g : Perm (Fin 5)) → n = 2) :
    IsConj (swap 0 4 * swap 1 3) g := by
  have h := g.support.card_le_univ
  rw [← Multiset.eq_replicate_card] at h2
  rw [← sum_cycleType, h2, Multiset.sum_replicate, smul_eq_mul] at h
  have h : Multiset.card g.cycleType ≤ 3 :=
    le_of_mul_le_mul_right (le_trans h (by simp only [card_fin]; ring_nf; decide)) (by simp)
  rw [mem_alternatingGroup, sign_of_cycleType, h2] at ha
  norm_num at ha
  rw [pow_add, pow_mul, Int.units_pow_two, one_mul, neg_one_pow_eq_one_iff_even] at ha
  swap; · decide
  rw [isConj_iff_cycleType_eq, h2]
  interval_cases h_1 : Multiset.card g.cycleType
  · exact (h1 (card_cycleType_eq_zero.1 h_1)).elim
  · simp at ha
  · have h04 : (0 : Fin 5) ≠ 4 := by decide
    have h13 : (1 : Fin 5) ≠ 3 := by decide
    rw [Disjoint.cycleType, (isCycle_swap h04).cycleType, (isCycle_swap h13).cycleType,
      card_support_swap h04, card_support_swap h13]
    · rfl
    · rw [disjoint_iff_disjoint_support, support_swap h04, support_swap h13]
      decide
  · contradiction
#align alternating_group.is_conj_swap_mul_swap_of_cycle_type_two alternatingGroup.isConj_swap_mul_swap_of_cycleType_two

/-- Shows that $A_5$ is simple by taking an arbitrary non-identity element and showing by casework
  on its cycle type that its normal closure is all of $A_5$. -/
instance isSimpleGroup_five : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  ⟨fun H => by
    intro Hn
    refine or_not.imp id fun Hb => ?_
    rw [eq_bot_iff_forall] at Hb
    push_neg at Hb
    obtain ⟨⟨g, gA⟩, gH, g1⟩ : ∃ x : ↥(alternatingGroup (Fin 5)), x ∈ H ∧ x ≠ 1 := Hb
    -- `g` is a non-identity alternating permutation in a normal subgroup `H` of $A_5$.
    rw [← SetLike.mem_coe, ← Set.singleton_subset_iff] at gH
    refine eq_top_iff.2 (le_trans (ge_of_eq ?_) (normalClosure_le_normal gH))
    -- It suffices to show that the normal closure of `g` in $A_5$ is $A_5$.
    by_cases h2 : ∀ n ∈ g.cycleType, n = 2
    -- If the cycle decomposition of `g` consists entirely of swaps, then the cycle type is $(2,2)$.
    -- This means that it is conjugate to $(04)(13)$, whose normal closure is $A_5$.
    · rw [Ne, Subtype.ext_iff] at g1
      exact
        (isConj_swap_mul_swap_of_cycleType_two gA g1 h2).normalClosure_eq_top_of
          normalClosure_swap_mul_swap_five
    push_neg at h2
    obtain ⟨n, ng, n2⟩ : ∃ n : ℕ, n ∈ g.cycleType ∧ n ≠ 2 := h2
    -- `n` is the size of a non-swap cycle in the decomposition of `g`.
    have n2' : 2 < n := lt_of_le_of_ne (two_le_of_mem_cycleType ng) n2.symm
    have n5 : n ≤ 5 := le_trans ?_ g.support.card_le_univ
    -- We check that `2 < n ≤ 5`, so that `interval_cases` has a precise range to check.
    swap
    · obtain ⟨m, hm⟩ := Multiset.exists_cons_of_mem ng
      rw [← sum_cycleType, hm, Multiset.sum_cons]
      exact le_add_right le_rfl
    interval_cases n
    -- This breaks into cases `n = 3`, `n = 4`, `n = 5`.
    -- If `n = 3`, then `g` has a 3-cycle in its decomposition, so `g^2` is a 3-cycle.
    -- `g^2` is in the normal closure of `g`, so that normal closure must be $A_5$.
    · rw [eq_top_iff, ← (isThreeCycle_sq_of_three_mem_cycleType_five ng).alternating_normalClosure
        (by rw [card_fin])]
      refine normalClosure_le_normal ?_
      rw [Set.singleton_subset_iff, SetLike.mem_coe]
      have h := SetLike.mem_coe.1 (subset_normalClosure
        (G := alternatingGroup (Fin 5)) (Set.mem_singleton ⟨g, gA⟩))
      exact mul_mem h h
    · -- The case `n = 4` leads to contradiction, as no element of $A_5$ includes a 4-cycle.
      have con := mem_alternatingGroup.1 gA
      rw [sign_of_cycleType, cycleType_of_card_le_mem_cycleType_add_two (by decide) ng] at con
      have : Odd 5 := by decide
      simp [this] at con
    · -- If `n = 5`, then `g` is itself a 5-cycle, conjugate to `finRotate 5`.
      refine (isConj_iff_cycleType_eq.2 ?_).normalClosure_eq_top_of normalClosure_finRotate_five
      rw [cycleType_of_card_le_mem_cycleType_add_two (by decide) ng, cycleType_finRotate]⟩
#align alternating_group.is_simple_group_five alternatingGroup.isSimpleGroup_five

end alternatingGroup
