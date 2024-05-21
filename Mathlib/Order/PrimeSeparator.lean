/-
Copyright (c) 2024 Sam van Gool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam van Gool
-/

import Mathlib.Order.PrimeIdeal
import Mathlib.Order.Zorn


/-!
# Separating prime filters and ideals

In a bounded distributive lattice, if $F$ is a filter, $I$ is an ideal, and $F$ and $I$ are
disjoint, then there exists a prime ideal $J$ containing $I$ with $J$ still disjoint from $F$.
This theorem is a crucial ingredient to [Stone's][Sto1938] duality for bounded distributive
lattices. The construction of the separator relies on Zorn's lemma.

## Tags

ideal, filter, prime, distributive lattice

## References

* [M. H. Stone, Topological representations of distributive lattices and Brouwerian logics
(1938)][Sto1938]
-/


universe u
variable {α : Type*}

open Order Ideal Set

variable [DistribLattice α] [BoundedOrder α]

variable {F : PFilter α} {I : Ideal α}

namespace DistribLattice


lemma mem_ideal_sup_principal (a b : α) (J : Ideal α) : b ∈ J ⊔ principal a ↔ ∃ j ∈ J, b ≤ j ⊔ a :=
  ⟨fun ⟨j, ⟨jJ, _, ha', bja'⟩⟩ => ⟨j, jJ, le_trans bja' (sup_le_sup_left ha' j)⟩,
    fun ⟨j, hj, hbja⟩ => ⟨j, hj, a, le_refl a, hbja⟩⟩

theorem prime_ideal_of_disjoint_filter_ideal (hFI : Disjoint (F : Set α) (I : Set α)) :
    ∃ J : Ideal α, (IsPrime J) ∧ I ≤ J ∧ Disjoint (F : Set α) J := by

  -- Let S be the set of ideals containing I and disjoint from F.
  set S : Set (Set α) := { J : Set α | IsIdeal J ∧ I ≤ J ∧ Disjoint (F : Set α) J }

  -- Then I is in S...
  have IinS : ↑I ∈ S := by
    refine ⟨Order.Ideal.isIdeal I, by trivial⟩

  -- ...and S contains upper bounds for any non-empty chains.
  have chainub : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →  ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intros c hcS hcC hcNe
    use sUnion c
    refine ⟨?_, fun s hs ↦ le_sSup hs⟩
    simp only [le_eq_subset, mem_setOf_eq, disjoint_sUnion_right, S]
    let ⟨J, hJ⟩ := hcNe
    refine ⟨Order.isIdeal_sUnion_of_isChain (fun _ hJ ↦ (hcS hJ).1) hcC hcNe,
            ⟨le_trans (hcS hJ).2.1 (le_sSup hJ), fun J hJ ↦ (hcS hJ).2.2⟩⟩

  -- Thus, by Zorn's lemma, we can pick a maximal ideal J in S.
  obtain ⟨Jset, ⟨Jidl, IJ, JF⟩, ⟨_, Jmax⟩⟩ := zorn_subset_nonempty S chainub I IinS
  set J := IsIdeal.toIdeal Jidl
  use J
  have IJ' : I ≤ J := IJ

  clear chainub IinS

  -- By construction, J contains I and is disjoint from F. It remains to prove that J is prime.
  refine ⟨?_, ⟨IJ, JF⟩⟩

  -- First note that J is proper: ⊤ ∈ F so ⊤ ∉ J because F and J are disjoint.
  have Jpr : IsProper J := isProper_of_not_mem (Set.disjoint_left.1 JF F.top_mem)

  -- Suppose that a₁ ∉ J, a₂ ∉ J. We need to prove that a₁ ⊔ a₂ ∉ J.
  rw [isPrime_iff_mem_or_mem]
  intros a₁ a₂
  contrapose!
  intro ⟨ha₁, ha₂⟩

  -- Consider the ideals J₁, J₂ generated by J ∪ {a₁} and J ∪ {a₂}, respectively.
  let J₁ := J ⊔ principal a₁
  let J₂ := J ⊔ principal a₂

  -- For each i, Jᵢ is an ideal that contains aᵢ, and is not equal to J.

  have a₁J₁ : a₁ ∈ J₁ := mem_of_subset_of_mem (le_sup_right : _ ≤ J ⊔ _) mem_principal_self
  have a₂J₂ : a₂ ∈ J₂ := mem_of_subset_of_mem (le_sup_right : _ ≤ J ⊔ _) mem_principal_self
  have J₁J : ↑J₁ ≠ Jset := ne_of_mem_of_not_mem' a₁J₁ ha₁
  have J₂J : ↑J₂ ≠ Jset := ne_of_mem_of_not_mem' a₂J₂ ha₂

  -- Therefore, since J is maximal, we must have Jᵢ ∉ S.
  have J₁S : ↑J₁ ∉ S := fun h => J₁J (Jmax J₁ h (le_sup_left : J ≤ J₁))
  have J₂S : ↑J₂ ∉ S := fun h => J₂J (Jmax J₂ h (le_sup_left : J ≤ J₂))

  -- Since Jᵢ is an ideal that contains I, we have that Jᵢ is not disjoint from F.
  have J₁F : ¬ (Disjoint (F : Set α) J₁) := by
    intro hdis
    apply J₁S
    simp only [le_eq_subset, mem_setOf_eq, SetLike.coe_subset_coe, S]
    exact ⟨J₁.isIdeal, le_trans IJ' le_sup_left, hdis⟩

  have J₂F : ¬ (Disjoint (F : Set α) J₂) := by
    intro hdis
    apply J₂S
    simp only [le_eq_subset, mem_setOf_eq, SetLike.coe_subset_coe, S]
    exact ⟨J₂.isIdeal, le_trans IJ' le_sup_left, hdis⟩

  -- Thus, pick cᵢ ∈ F ∩ Jᵢ.
  let ⟨c₁, ⟨c₁F, c₁J₁⟩⟩ := Set.not_disjoint_iff.1 J₁F
  let ⟨c₂, ⟨c₂F, c₂J₂⟩⟩ := Set.not_disjoint_iff.1 J₂F

  -- Using the definition of Jᵢ, we can pick bᵢ ∈ J such that cᵢ ≤ bᵢ ⊔ aᵢ.
  let ⟨b₁, ⟨b₁J, cba₁⟩⟩ := (mem_ideal_sup_principal a₁ c₁ J).1 c₁J₁
  let ⟨b₂, ⟨b₂J, cba₂⟩⟩ := (mem_ideal_sup_principal a₂ c₂ J).1 c₂J₂

  -- Since J is an ideal, we have b := b₁ ⊔ b₂ ∈ J.
  let b := b₁ ⊔ b₂
  have bJ : b ∈ J := sup_mem b₁J b₂J

  -- We now prove a key inequality, using crucially that the lattice is distributive.
  have ineq : c₁ ⊓ c₂ ≤ b ⊔ (a₁ ⊓ a₂) :=
  calc
    c₁ ⊓ c₂ ≤ (b₁ ⊔ a₁) ⊓ (b₂ ⊔ a₂) := inf_le_inf cba₁ cba₂
    _       ≤ (b  ⊔ a₁) ⊓ (b  ⊔ a₂) := by
      apply inf_le_inf <;> apply sup_le_sup_right; exact le_sup_left; exact le_sup_right
    _       = b ⊔ (a₁ ⊓ a₂) := (sup_inf_left b a₁ a₂).symm

  -- Note that c₁ ⊓ c₂ ∈ F, since c₁ and c₂ are both in F and F is a filter.
  -- Since F is an upper set, it now follows that b ⊔ (a₁ ⊓ a₂) ∈ F.
  have ba₁a₂F : b ⊔ (a₁ ⊓ a₂) ∈ F := PFilter.mem_of_le ineq (PFilter.inf_mem c₁F c₂F)

  -- Now, if we would have a₁ ⊓ a₂ ∈ J, then, since J is an ideal and b ∈ J, we would also get
  -- b ⊔ (a₁ ⊓ a₂) ∈ J. But this contradicts that J is disjoint from F.
  contrapose! JF with ha₁a₂
  rw [Set.not_disjoint_iff]
  use b ⊔ (a₁ ⊓ a₂)
  exact ⟨ba₁a₂F, sup_mem bJ ha₁a₂⟩

-- TODO: Define prime filters in Mathlib so that the following corollary can be stated and proved.
-- theorem prime_filter_of_disjoint_filter_ideal (hFI : Disjoint (F : Set α) (I : Set α)) :
--     ∃ G : PFilter α, (IsPrime G) ∧ F ≤ G ∧ Disjoint (G : Set α) I := by sorry
