/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Subsingleton
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Subgroups generated by an element

## Tags
subgroup, subgroups

-/


variable {G : Type*} [Group G]
variable {A : Type*} [AddGroup A]
variable {N : Type*} [Group N]

namespace Subgroup

/-- The subgroup generated by an element. -/
def zpowers (g : G) : Subgroup G :=
  Subgroup.copy (zpowersHom G g).range (Set.range (g ^ · : ℤ → G)) rfl

theorem mem_zpowers (g : G) : g ∈ zpowers g :=
  ⟨1, zpow_one _⟩

theorem coe_zpowers (g : G) : ↑(zpowers g) = Set.range (g ^ · : ℤ → G) :=
  rfl

noncomputable instance decidableMemZPowers {a : G} : DecidablePred (· ∈ Subgroup.zpowers a) :=
  Classical.decPred _

theorem zpowers_eq_closure (g : G) : zpowers g = closure {g} := by
  ext
  exact mem_closure_singleton.symm

theorem range_zpowersHom (g : G) : (zpowersHom G g).range = zpowers g :=
  rfl

theorem mem_zpowers_iff {g h : G} : h ∈ zpowers g ↔ ∃ k : ℤ, g ^ k = h :=
  Iff.rfl

theorem zpow_mem_zpowers (g : G) (k : ℤ) : g ^ k ∈ zpowers g :=
  mem_zpowers_iff.mpr ⟨k, rfl⟩

theorem npow_mem_zpowers (g : G) (k : ℕ) : g ^ k ∈ zpowers g :=
  zpow_natCast g k ▸ zpow_mem_zpowers g k

theorem forall_zpowers {x : G} {p : zpowers x → Prop} : (∀ g, p g) ↔ ∀ m : ℤ, p ⟨x ^ m, m, rfl⟩ :=
  Set.forall_subtype_range_iff

theorem exists_zpowers {x : G} {p : zpowers x → Prop} : (∃ g, p g) ↔ ∃ m : ℤ, p ⟨x ^ m, m, rfl⟩ :=
  Set.exists_subtype_range_iff

theorem forall_mem_zpowers {x : G} {p : G → Prop} : (∀ g ∈ zpowers x, p g) ↔ ∀ m : ℤ, p (x ^ m) :=
  Set.forall_mem_range

theorem exists_mem_zpowers {x : G} {p : G → Prop} : (∃ g ∈ zpowers x, p g) ↔ ∃ m : ℤ, p (x ^ m) :=
  Set.exists_range_iff

instance (a : G) : Countable (zpowers a) :=
  ((zpowersHom G a).rangeRestrict_surjective.comp Multiplicative.ofAdd.surjective).countable

end Subgroup

namespace AddSubgroup

/-- The subgroup generated by an element. -/
def zmultiples (a : A) : AddSubgroup A :=
  AddSubgroup.copy (zmultiplesHom A a).range (Set.range ((· • a) : ℤ → A)) rfl

@[simp]
theorem range_zmultiplesHom (a : A) : (zmultiplesHom A a).range = zmultiples a :=
  rfl

attribute [to_additive existing] Subgroup.zpowers

attribute [to_additive (attr := simp)] Subgroup.mem_zpowers

attribute [to_additive (attr := norm_cast)] Subgroup.coe_zpowers

attribute [to_additive] Subgroup.decidableMemZPowers

attribute [to_additive] Subgroup.zpowers_eq_closure

attribute [to_additive existing (attr := simp)]
  Subgroup.range_zpowersHom

attribute [to_additive] Subgroup.mem_zpowers_iff

attribute [to_additive (attr := simp)] Subgroup.zpow_mem_zpowers

attribute [to_additive (attr := simp)] Subgroup.npow_mem_zpowers

-- Porting note: increasing simp priority. Better lemma than `Subtype.forall`
attribute [to_additive (attr := simp 1100)] Subgroup.forall_zpowers

attribute [to_additive] Subgroup.forall_mem_zpowers

-- Porting note: increasing simp priority. Better lemma than `Subtype.exists`
attribute [to_additive (attr := simp 1100)] Subgroup.exists_zpowers

attribute [to_additive] Subgroup.exists_mem_zpowers

instance (a : A) : Countable (zmultiples a) :=
  (zmultiplesHom A a).rangeRestrict_surjective.countable

section Ring

variable {R : Type*} [Ring R] (r : R) (k : ℤ)

@[simp]
theorem intCast_mul_mem_zmultiples : ↑(k : ℤ) * r ∈ zmultiples r := by
  simpa only [← zsmul_eq_mul] using zsmul_mem_zmultiples r k

@[deprecated (since := "2024-04-17")]
alias int_cast_mul_mem_zmultiples := intCast_mul_mem_zmultiples

@[simp]
theorem intCast_mem_zmultiples_one : ↑(k : ℤ) ∈ zmultiples (1 : R) :=
  mem_zmultiples_iff.mp ⟨k, by simp⟩

@[deprecated (since := "2024-04-17")]
alias int_cast_mem_zmultiples_one := intCast_mem_zmultiples_one

end Ring

end AddSubgroup

@[simp] lemma Int.range_castAddHom {A : Type*} [AddGroupWithOne A] :
    (Int.castAddHom A).range = AddSubgroup.zmultiples 1 := by
  ext a
  simp_rw [AddMonoidHom.mem_range, Int.coe_castAddHom, AddSubgroup.mem_zmultiples_iff, zsmul_one]

@[to_additive (attr := simp)]
theorem MonoidHom.map_zpowers (f : G →* N) (x : G) :
    (Subgroup.zpowers x).map f = Subgroup.zpowers (f x) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, f.map_closure, Set.image_singleton]

theorem Int.mem_zmultiples_iff {a b : ℤ} : b ∈ AddSubgroup.zmultiples a ↔ a ∣ b :=
  exists_congr fun k => by rw [mul_comm, eq_comm, ← smul_eq_mul]

@[simp]
lemma Int.zmultiples_one : AddSubgroup.zmultiples (1 : ℤ) = ⊤ := by
  ext z
  simpa only [AddSubgroup.mem_top, iff_true] using ⟨z, zsmul_int_one z⟩

theorem ofMul_image_zpowers_eq_zmultiples_ofMul {x : G} :
    Additive.ofMul '' (Subgroup.zpowers x : Set G) = AddSubgroup.zmultiples (Additive.ofMul x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨m, hm⟩, hz2⟩
    use m
    simp only at *
    rwa [← ofMul_zpow, hm]
  · rintro ⟨n, hn⟩
    refine ⟨x ^ n, ⟨n, rfl⟩, ?_⟩
    rwa [ofMul_zpow]

theorem ofAdd_image_zmultiples_eq_zpowers_ofAdd {x : A} :
    Multiplicative.ofAdd '' (AddSubgroup.zmultiples x : Set A) =
      Subgroup.zpowers (Multiplicative.ofAdd x) := by
  symm
  rw [Equiv.eq_image_iff_symm_image_eq]
  exact ofMul_image_zpowers_eq_zmultiples_ofMul

namespace Subgroup

variable {s : Set G} {g : G}

@[to_additive]
instance zpowers_isCommutative (g : G) : (zpowers g).IsCommutative :=
  ⟨⟨fun ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ => by
      rw [Subtype.ext_iff, coe_mul, coe_mul, Subtype.coe_mk, Subtype.coe_mk, ← h₁, ← h₂,
        zpow_mul_comm]⟩⟩

@[to_additive (attr := simp)]
theorem zpowers_le {g : G} {H : Subgroup G} : zpowers g ≤ H ↔ g ∈ H := by
  rw [zpowers_eq_closure, closure_le, Set.singleton_subset_iff, SetLike.mem_coe]

alias ⟨_, zpowers_le_of_mem⟩ := zpowers_le

alias ⟨_, _root_.AddSubgroup.zmultiples_le_of_mem⟩ := AddSubgroup.zmultiples_le

attribute [to_additive existing] zpowers_le_of_mem

@[to_additive (attr := simp)]
theorem zpowers_eq_bot {g : G} : zpowers g = ⊥ ↔ g = 1 := by rw [eq_bot_iff, zpowers_le, mem_bot]

@[to_additive]
theorem zpowers_ne_bot : zpowers g ≠ ⊥ ↔ g ≠ 1 :=
  zpowers_eq_bot.not

@[to_additive (attr := simp)]
theorem zpowers_one_eq_bot : Subgroup.zpowers (1 : G) = ⊥ :=
  Subgroup.zpowers_eq_bot.mpr rfl

@[to_additive (attr := simp)]
theorem zpowers_inv : zpowers g⁻¹ = zpowers g :=
  eq_of_forall_ge_iff fun _ ↦ by simp only [zpowers_le, inv_mem_iff]

@[to_additive]
theorem centralizer_closure (S : Set G) :
    centralizer (closure S : Set G) = ⨅ g ∈ S, centralizer (zpowers g : Set G) :=
  le_antisymm
      (le_iInf fun _ => le_iInf fun hg => centralizer_le <| zpowers_le.2 <| subset_closure hg) <|
    le_centralizer_iff.1 <|
      (closure_le _).2 fun g =>
        SetLike.mem_coe.2 ∘ zpowers_le.1 ∘ le_centralizer_iff.1 ∘ iInf_le_of_le g ∘ iInf_le _

@[to_additive]
theorem center_eq_iInf (S : Set G) (hS : closure S = ⊤) :
    center G = ⨅ g ∈ S, centralizer (zpowers g) := by
  rw [← centralizer_univ, ← coe_top, ← hS, centralizer_closure]

@[to_additive]
theorem center_eq_infi' (S : Set G) (hS : closure S = ⊤) :
    center G = ⨅ g : S, centralizer (zpowers (g : G)) := by
  rw [center_eq_iInf S hS, ← iInf_subtype'']

end Subgroup
