/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Subgroup.MulOpposite
import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.GroupTheory.GroupAction.ConjAct

#align_import group_theory.subgroup.pointwise from "leanprover-community/mathlib"@"e655e4ea5c6d02854696f97494997ba4c31be802"

/-! # Pointwise instances on `Subgroup` and `AddSubgroup`s

This file provides the actions

* `Subgroup.pointwiseMulAction`
* `AddSubgroup.pointwiseMulAction`

which matches the action of `Set.mulActionSet`.

These actions are available in the `Pointwise` locale.

## Implementation notes

The pointwise section of this file is almost identical to `GroupTheory/Submonoid/Pointwise.lean`.
Where possible, try to keep them in sync.
-/


open Set

open Pointwise

variable {α G A S : Type*}

@[to_additive (attr := simp, norm_cast)]
lemma inv_coe_set [InvolutiveInv G] [SetLike S G] [InvMemClass S G] {H : S} : (H : Set G)⁻¹ = H :=
  Set.ext fun _ => inv_mem_iff
#align inv_coe_set inv_coe_set
#align neg_coe_set neg_coe_set

@[to_additive (attr := simp)]
lemma smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G} (ha : a ∈ s) :
    a • (s : Set G) = s := by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_left, ha]

@[to_additive (attr := simp)]
lemma op_smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G} (ha : a ∈ s) :
    MulOpposite.op a • (s : Set G) = s := by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_right, ha]

@[to_additive (attr := simp, norm_cast)]
lemma coe_mul_coe [SetLike S G] [DivInvMonoid G] [SubgroupClass S G] (H : S) :
    H * H = (H : Set G) := by aesop (add simp mem_mul)

@[to_additive (attr := simp, norm_cast)]
lemma coe_div_coe [SetLike S G] [DivisionMonoid G] [SubgroupClass S G] (H : S) :
    H / H = (H : Set G) := by simp [div_eq_mul_inv]

variable [Group G] [AddGroup A] {s : Set G}

namespace Subgroup

@[to_additive (attr := simp)]
lemma inv_subset_closure (S : Set G) : S⁻¹ ⊆ closure S := fun s hs => by
  rw [SetLike.mem_coe, ← Subgroup.inv_mem_iff]
  exact subset_closure (mem_inv.mp hs)
#align subgroup.inv_subset_closure Subgroup.inv_subset_closure
#align add_subgroup.neg_subset_closure AddSubgroup.neg_subset_closure

@[to_additive]
lemma closure_toSubmonoid (S : Set G) :
    (closure S).toSubmonoid = Submonoid.closure (S ∪ S⁻¹) := by
  refine le_antisymm (fun x hx => ?_) (Submonoid.closure_le.2 ?_)
  · refine'
      closure_induction hx
        (fun x hx => Submonoid.closure_mono (subset_union_left S S⁻¹) (Submonoid.subset_closure hx))
        (Submonoid.one_mem _) (fun x y hx hy => Submonoid.mul_mem _ hx hy) fun x hx => _
    rwa [← Submonoid.mem_closure_inv, Set.union_inv, inv_inv, Set.union_comm]
  · simp only [true_and_iff, coe_toSubmonoid, union_subset_iff, subset_closure, inv_subset_closure]
#align subgroup.closure_to_submonoid Subgroup.closure_toSubmonoid
#align add_subgroup.closure_to_add_submonoid AddSubgroup.closure_toAddSubmonoid

/-- For subgroups generated by a single element, see the simpler `zpow_induction_left`. -/
@[to_additive (attr := elab_as_elim)
  "For additive subgroups generated by a single element, see the simpler
  `zsmul_induction_left`."]
theorem closure_induction_left {p : (x : G) → x ∈ closure s → Prop} (one : p 1 (one_mem _))
    (mul_left : ∀ x (hx : x ∈ s), ∀ (y) hy, p y hy → p (x * y) (mul_mem (subset_closure hx) hy))
    (mul_left_inv : ∀ x (hx : x ∈ s), ∀ (y) hy, p y hy →
      p (x⁻¹ * y) (mul_mem (inv_mem (subset_closure hx)) hy))
    {x : G} (h : x ∈ closure s) : p x h := by
  revert h
  simp_rw [← mem_toSubmonoid, closure_toSubmonoid] at *
  intro h
  induction h using Submonoid.closure_induction_left with
  | one => exact one
  | mul_left x hx y hy ih =>
    cases hx with
    | inl hx => exact mul_left _ hx _ hy ih
    | inr hx => simpa only [inv_inv] using mul_left_inv _ hx _ hy ih
#align subgroup.closure_induction_left Subgroup.closure_induction_left
#align add_subgroup.closure_induction_left AddSubgroup.closure_induction_left

/-- For subgroups generated by a single element, see the simpler `zpow_induction_right`. -/
@[to_additive (attr := elab_as_elim)
  "For additive subgroups generated by a single element, see the simpler
  `zsmul_induction_right`."]
theorem closure_induction_right {p : (x : G) → x ∈ closure s → Prop} (one : p 1 (one_mem _))
    (mul_right : ∀ (x) hx, ∀ y (hy : y ∈ s), p x hx → p (x * y) (mul_mem hx (subset_closure hy)))
    (mul_right_inv : ∀ (x) hx, ∀ y (hy : y ∈ s), p x hx →
      p (x * y⁻¹) (mul_mem hx (inv_mem (subset_closure hy))))
    {x : G} (h : x ∈ closure s) : p x h :=
  closure_induction_left (s := MulOpposite.unop ⁻¹' s)
    (p := fun m hm => p m.unop <| by rwa [← op_closure] at hm)
    one
    (fun _x hx _y hy => mul_right _ _ _ hx)
    (fun _x hx _y hy => mul_right_inv _ _ _ hx)
    (by rwa [← op_closure])
#align subgroup.closure_induction_right Subgroup.closure_induction_right
#align add_subgroup.closure_induction_right AddSubgroup.closure_induction_right

@[to_additive (attr := simp)]
lemma closure_inv (s : Set G) : closure s⁻¹ = closure s := by
  simp only [← toSubmonoid_eq, closure_toSubmonoid, inv_inv, union_comm]
#align subgroup.closure_inv Subgroup.closure_inv
#align add_subgroup.closure_neg AddSubgroup.closure_neg

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of
`k` and their inverse, and is preserved under multiplication, then `p` holds for all elements of
the closure of `k`. -/
@[to_additive (attr := elab_as_elim)
  "An induction principle for additive closure membership. If `p` holds for `0` and all
  elements of `k` and their negation, and is preserved under addition, then `p` holds for all
  elements of the additive closure of `k`."]
theorem closure_induction'' {p : (g : G) → g ∈ closure s → Prop}
    (mem : ∀ x (hx : x ∈ s), p x (subset_closure hx))
    (inv_mem : ∀ x (hx : x ∈ s), p x⁻¹ (inv_mem (subset_closure hx)))
    (one : p 1 (one_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (h : x ∈ closure s) : p x h :=
  closure_induction_left one (fun x hx y _ hy => mul x y _ _ (mem x hx) hy)
    (fun x hx y _ => mul x⁻¹ y _ _ <| inv_mem x hx) h
#align subgroup.closure_induction'' Subgroup.closure_induction''
#align add_subgroup.closure_induction'' AddSubgroup.closure_induction''

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `1` and all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[to_additive (attr := elab_as_elim) " An induction principle for elements of `⨆ i, S i`.
If `C` holds for `0` and all elements of `S i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `S`. "]
theorem iSup_induction {ι : Sort*} (S : ι → Subgroup G) {C : G → Prop} {x : G} (hx : x ∈ ⨆ i, S i)
    (mem : ∀ (i), ∀ x ∈ S i, C x) (one : C 1) (mul : ∀ x y, C x → C y → C (x * y)) : C x := by
  rw [iSup_eq_closure] at hx
  induction hx using closure_induction'' with
  | one => exact one
  | mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem _ _ hi
  | inv_mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem _ _ (inv_mem hi)
  | mul x y _ _ ihx ihy => exact mul x y ihx ihy
#align subgroup.supr_induction Subgroup.iSup_induction
#align add_subgroup.supr_induction AddSubgroup.iSup_induction

/-- A dependent version of `Subgroup.iSup_induction`. -/
@[to_additive (attr := elab_as_elim) "A dependent version of `AddSubgroup.iSup_induction`. "]
theorem iSup_induction' {ι : Sort*} (S : ι → Subgroup G) {C : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (hp : ∀ (i), ∀ x (hx : x ∈ S i), C x (mem_iSup_of_mem i hx)) (h1 : C 1 (one_mem _))
    (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›)) {x : G}
    (hx : x ∈ ⨆ i, S i) : C x hx := by
  suffices ∃ h, C x h from this.snd
  refine' iSup_induction S (C := fun x => ∃ h, C x h) hx (fun i x hx => _) _ fun x y => _
  · exact ⟨_, hp i _ hx⟩
  · exact ⟨_, h1⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, hmul _ _ _ _ Cx Cy⟩
#align subgroup.supr_induction' Subgroup.iSup_induction'
#align add_subgroup.supr_induction' AddSubgroup.iSup_induction'

@[to_additive]
lemma closure_mul_le (S T : Set G) : closure (S * T) ≤ closure S ⊔ closure T :=
  sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)
#align subgroup.closure_mul_le Subgroup.closure_mul_le
#align add_subgroup.closure_add_le AddSubgroup.closure_add_le

@[to_additive]
lemma sup_eq_closure_mul (H K : Subgroup G) : H ⊔ K = closure ((H : Set G) * (K : Set G)) :=
  le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])
#align subgroup.sup_eq_closure Subgroup.sup_eq_closure_mul
#align add_subgroup.sup_eq_closure AddSubgroup.sup_eq_closure_add

@[to_additive]
lemma set_mul_normal_comm (s : Set G) (N : Subgroup G) [hN : N.Normal] :
    s * (N : Set G) = (N : Set G) * s := by
  rw [← iUnion_mul_left_image, ← iUnion_mul_right_image]
  simp only [image_mul_left, image_mul_right, Set.preimage, SetLike.mem_coe, hN.mem_comm_iff]

/-- The carrier of `H ⊔ N` is just `↑H * ↑N` (pointwise set product) when `N` is normal. -/
@[to_additive "The carrier of `H ⊔ N` is just `↑H + ↑N` (pointwise set addition)
when `N` is normal."]
theorem mul_normal (H N : Subgroup G) [hN : N.Normal] : (↑(H ⊔ N) : Set G) = H * N := by
  rw [sup_eq_closure_mul]
  refine Set.Subset.antisymm (fun x hx => ?_) subset_closure
  induction hx using closure_induction'' with
  | one => exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  | mem _ hx => exact hx
  | inv_mem x hx =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    simpa only [mul_inv_rev, mul_assoc, inv_inv, inv_mul_cancel_left]
      using mul_mem_mul (inv_mem hx) (hN.conj_mem _ (inv_mem hy) x)
  | mul x' x' _ _ hx hx' =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    obtain ⟨x', hx', y', hy', rfl⟩ := hx'
    refine ⟨x * x', mul_mem hx hx', x'⁻¹ * y * x' * y', mul_mem ?_ hy', ?_⟩
    · simpa using hN.conj_mem _ hy x'⁻¹
    · simp only [mul_assoc, mul_inv_cancel_left]
#align subgroup.mul_normal Subgroup.mul_normal
#align add_subgroup.add_normal AddSubgroup.add_normal

/-- The carrier of `N ⊔ H` is just `↑N * ↑H` (pointwise set product) when `N` is normal. -/
@[to_additive "The carrier of `N ⊔ H` is just `↑N + ↑H` (pointwise set addition)
when `N` is normal."]
theorem normal_mul (N H : Subgroup G) [N.Normal] : (↑(N ⊔ H) : Set G) = N * H := by
  rw [← set_mul_normal_comm, sup_comm, mul_normal]
#align subgroup.normal_mul Subgroup.normal_mul
#align add_subgroup.normal_add AddSubgroup.normal_add

@[to_additive]
lemma mul_inf_assoc (A B C : Subgroup G) (h : A ≤ C) :
    (A : Set G) * ↑(B ⊓ C) = (A : Set G) * (B : Set G) ∩ C := by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, z, ⟨hzB, hzC⟩, rfl⟩
    refine' ⟨_, mul_mem (h hy) hzC⟩
    exact ⟨y, hy, z, hzB, rfl⟩
  rintro ⟨⟨y, hy, z, hz, rfl⟩, hyz⟩
  refine' ⟨y, hy, z, ⟨hz, _⟩, rfl⟩
  suffices y⁻¹ * (y * z) ∈ C by simpa
  exact mul_mem (inv_mem (h hy)) hyz
#align subgroup.mul_inf_assoc Subgroup.mul_inf_assoc
#align add_subgroup.add_inf_assoc AddSubgroup.add_inf_assoc

@[to_additive]
lemma inf_mul_assoc (A B C : Subgroup G) (h : C ≤ A) :
    ((A ⊓ B : Subgroup G) : Set G) * C = (A : Set G) ∩ (↑B * ↑C) := by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, z, hz, rfl⟩
    refine' ⟨A.mul_mem hyA (h hz), _⟩
    exact ⟨y, hyB, z, hz, rfl⟩
  rintro ⟨hyz, y, hy, z, hz, rfl⟩
  refine' ⟨y, ⟨_, hy⟩, z, hz, rfl⟩
  suffices y * z * z⁻¹ ∈ A by simpa
  exact mul_mem hyz (inv_mem (h hz))
#align subgroup.inf_mul_assoc Subgroup.inf_mul_assoc
#align add_subgroup.inf_add_assoc AddSubgroup.inf_add_assoc

@[to_additive]
instance sup_normal (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal] : (H ⊔ K).Normal where
  conj_mem n hmem g := by
    rw [← SetLike.mem_coe, normal_mul] at hmem ⊢
    rcases hmem with ⟨h, hh, k, hk, rfl⟩
    refine ⟨g * h * g⁻¹, hH.conj_mem h hh g, g * k * g⁻¹, hK.conj_mem k hk g, ?_⟩
    simp only [mul_assoc, inv_mul_cancel_left]
#align subgroup.sup_normal Subgroup.sup_normal

-- Porting note (#10756): new lemma
@[to_additive]
lemma smul_opposite_image_mul_preimage' (g : G) (h : Gᵐᵒᵖ) (s : Set G) :
    (fun y => h • y) '' ((g * ·) ⁻¹' s) = (g * ·) ⁻¹' ((fun y => h • y) '' s) := by
  simp [preimage_preimage, mul_assoc]

-- Porting note: deprecate?
@[to_additive]
lemma smul_opposite_image_mul_preimage {H : Subgroup G} (g : G) (h : H.op) (s : Set G) :
    (fun y => h • y) '' ((g * ·) ⁻¹' s) = (g * ·) ⁻¹' ((fun y => h • y) '' s) :=
  smul_opposite_image_mul_preimage' g h s
#align subgroup.smul_opposite_image_mul_preimage Subgroup.smul_opposite_image_mul_preimage
#align add_subgroup.vadd_opposite_image_add_preimage AddSubgroup.vadd_opposite_image_add_preimage

/-! ### Pointwise action -/


section Monoid

variable [Monoid α] [MulDistribMulAction α G]

/-- The action on a subgroup corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (Subgroup G) where
  smul a S := S.map (MulDistribMulAction.toMonoidEnd _ _ a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using S.map_id
  mul_smul a₁ a₂ S :=
    (congr_arg (fun f : Monoid.End G => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm
#align subgroup.pointwise_mul_action Subgroup.pointwiseMulAction

scoped[Pointwise] attribute [instance] Subgroup.pointwiseMulAction

lemma pointwise_smul_def {a : α} (S : Subgroup G) :
    a • S = S.map (MulDistribMulAction.toMonoidEnd _ _ a) :=
  rfl
#align subgroup.pointwise_smul_def Subgroup.pointwise_smul_def

@[simp]
lemma coe_pointwise_smul (a : α) (S : Subgroup G) : ↑(a • S) = a • (S : Set G) :=
  rfl
#align subgroup.coe_pointwise_smul Subgroup.coe_pointwise_smul

@[simp]
lemma pointwise_smul_toSubmonoid (a : α) (S : Subgroup G) :
    (a • S).toSubmonoid = a • S.toSubmonoid :=
  rfl
#align subgroup.pointwise_smul_to_submonoid Subgroup.pointwise_smul_toSubmonoid

lemma smul_mem_pointwise_smul (m : G) (a : α) (S : Subgroup G) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set G))
#align subgroup.smul_mem_pointwise_smul Subgroup.smul_mem_pointwise_smul

instance : CovariantClass α (Subgroup G) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_subset _⟩

lemma mem_smul_pointwise_iff_exists (m : G) (a : α) (S : Subgroup G) :
    m ∈ a • S ↔ ∃ s : G, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set G) ↔ _)
#align subgroup.mem_smul_pointwise_iff_exists Subgroup.mem_smul_pointwise_iff_exists

@[simp]
lemma smul_bot (a : α) : a • (⊥ : Subgroup G) = ⊥ :=
  map_bot _
#align subgroup.smul_bot Subgroup.smul_bot

lemma smul_sup (a : α) (S T : Subgroup G) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
#align subgroup.smul_sup Subgroup.smul_sup

lemma smul_closure (a : α) (s : Set G) : a • closure s = closure (a • s) :=
  MonoidHom.map_closure _ _
#align subgroup.smul_closure Subgroup.smul_closure

instance pointwise_isCentralScalar [MulDistribMulAction αᵐᵒᵖ G] [IsCentralScalar α G] :
    IsCentralScalar α (Subgroup G) :=
  ⟨fun _ S => (congr_arg fun f => S.map f) <| MonoidHom.ext <| op_smul_eq_smul _⟩
#align subgroup.pointwise_central_scalar Subgroup.pointwise_isCentralScalar

lemma conj_smul_le_of_le {P H : Subgroup G} (hP : P ≤ H) (h : H) :
    MulAut.conj (h : G) • P ≤ H := by
  rintro - ⟨g, hg, rfl⟩
  exact H.mul_mem (H.mul_mem h.2 (hP hg)) (H.inv_mem h.2)
#align subgroup.conj_smul_le_of_le Subgroup.conj_smul_le_of_le

lemma conj_smul_subgroupOf {P H : Subgroup G} (hP : P ≤ H) (h : H) :
    MulAut.conj h • P.subgroupOf H = (MulAut.conj (h : G) • P).subgroupOf H := by
  refine' le_antisymm _ _
  · rintro - ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro p ⟨g, hg, hp⟩
    exact ⟨⟨g, hP hg⟩, hg, Subtype.ext hp⟩
#align subgroup.conj_smul_subgroup_of Subgroup.conj_smul_subgroupOf

end Monoid

section Group

variable [Group α] [MulDistribMulAction α G]

@[simp]
lemma smul_mem_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
#align subgroup.smul_mem_pointwise_smul_iff Subgroup.smul_mem_pointwise_smul_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Subgroup G} {x : G} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
#align subgroup.mem_pointwise_smul_iff_inv_smul_mem Subgroup.mem_pointwise_smul_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff
#align subgroup.mem_inv_pointwise_smul_iff Subgroup.mem_inv_pointwise_smul_iff

@[simp]
lemma pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Subgroup G} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff
#align subgroup.pointwise_smul_le_pointwise_smul_iff Subgroup.pointwise_smul_le_pointwise_smul_iff

lemma pointwise_smul_subset_iff {a : α} {S T : Subgroup G} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff
#align subgroup.pointwise_smul_subset_iff Subgroup.pointwise_smul_subset_iff

lemma subset_pointwise_smul_iff {a : α} {S T : Subgroup G} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff
#align subgroup.subset_pointwise_smul_iff Subgroup.subset_pointwise_smul_iff

@[simp]
lemma smul_inf (a : α) (S T : Subgroup G) : a • (S ⊓ T) = a • S ⊓ a • T := by
  simp [SetLike.ext_iff, mem_pointwise_smul_iff_inv_smul_mem]
#align subgroup.smul_inf Subgroup.smul_inf

/-- Applying a `MulDistribMulAction` results in an isomorphic subgroup -/
@[simps!]
def equivSMul (a : α) (H : Subgroup G) : H ≃* (a • H : Subgroup G) :=
  (MulDistribMulAction.toMulEquiv G a).subgroupMap H
#align subgroup.equiv_smul Subgroup.equivSMul

lemma subgroup_mul_singleton {H : Subgroup G} {h : G} (hh : h ∈ H) : (H : Set G) * {h} = H :=
  suffices { x : G | x ∈ H } = ↑H by simpa [preimage, mul_mem_cancel_right (inv_mem hh)]
  rfl
#align subgroup.subgroup_mul_singleton Subgroup.subgroup_mul_singleton

lemma singleton_mul_subgroup {H : Subgroup G} {h : G} (hh : h ∈ H) : {h} * (H : Set G) = H :=
  suffices { x : G | x ∈ H } = ↑H by simpa [preimage, mul_mem_cancel_left (inv_mem hh)]
  rfl
#align subgroup.singleton_mul_subgroup Subgroup.singleton_mul_subgroup

lemma Normal.conjAct {G : Type*} [Group G] {H : Subgroup G} (hH : H.Normal) (g : ConjAct G) :
    g • H = H :=
  have : ∀ g : ConjAct G, g • H ≤ H :=
    fun _ => map_le_iff_le_comap.2 fun _ h => hH.conj_mem _ h _
  (this g).antisymm <| (smul_inv_smul g H).symm.trans_le (map_mono <| this _)
#align subgroup.normal.conj_act Subgroup.Normal.conjAct

@[simp]
lemma smul_normal (g : G) (H : Subgroup G) [h : Normal H] : MulAut.conj g • H = H :=
  h.conjAct g
#align subgroup.smul_normal Subgroup.smul_normal

end Group

section GroupWithZero

variable [GroupWithZero α] [MulDistribMulAction α G]

@[simp]
lemma smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set G) x
#align subgroup.smul_mem_pointwise_smul_iff₀ Subgroup.smul_mem_pointwise_smul_iff₀

lemma mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set G) x
#align subgroup.mem_pointwise_smul_iff_inv_smul_mem₀ Subgroup.mem_pointwise_smul_iff_inv_smul_mem₀

lemma mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set G) x
#align subgroup.mem_inv_pointwise_smul_iff₀ Subgroup.mem_inv_pointwise_smul_iff₀

@[simp]
lemma pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Subgroup G} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha
#align subgroup.pointwise_smul_le_pointwise_smul_iff₀ Subgroup.pointwise_smul_le_pointwise_smul_iff₀

lemma pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : Subgroup G} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha
#align subgroup.pointwise_smul_le_iff₀ Subgroup.pointwise_smul_le_iff₀

lemma le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Subgroup G} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha
#align subgroup.le_pointwise_smul_iff₀ Subgroup.le_pointwise_smul_iff₀

end GroupWithZero

end Subgroup

namespace AddSubgroup

section Monoid

variable [Monoid α] [DistribMulAction α A]

/-- The action on an additive subgroup corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (AddSubgroup A) where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ _ a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (MonoidHom.map_mul _ _ _)).trans
      (S.map_map _ _).symm
#align add_subgroup.pointwise_mul_action AddSubgroup.pointwiseMulAction

scoped[Pointwise] attribute [instance] AddSubgroup.pointwiseMulAction

@[simp]
lemma coe_pointwise_smul (a : α) (S : AddSubgroup A) : ↑(a • S) = a • (S : Set A) :=
  rfl
#align add_subgroup.coe_pointwise_smul AddSubgroup.coe_pointwise_smul

@[simp]
lemma pointwise_smul_toAddSubmonoid (a : α) (S : AddSubgroup A) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl
#align add_subgroup.pointwise_smul_to_add_submonoid AddSubgroup.pointwise_smul_toAddSubmonoid

lemma smul_mem_pointwise_smul (m : A) (a : α) (S : AddSubgroup A) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set A))
#align add_subgroup.smul_mem_pointwise_smul AddSubgroup.smul_mem_pointwise_smul

lemma mem_smul_pointwise_iff_exists (m : A) (a : α) (S : AddSubgroup A) :
    m ∈ a • S ↔ ∃ s : A, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set A) ↔ _)
#align add_subgroup.mem_smul_pointwise_iff_exists AddSubgroup.mem_smul_pointwise_iff_exists

instance pointwise_isCentralScalar [DistribMulAction αᵐᵒᵖ A] [IsCentralScalar α A] :
    IsCentralScalar α (AddSubgroup A) :=
  ⟨fun _ S => (congr_arg fun f => S.map f) <| AddMonoidHom.ext <| op_smul_eq_smul _⟩
#align add_subgroup.pointwise_central_scalar AddSubgroup.pointwise_isCentralScalar

end Monoid

section Group

variable [Group α] [DistribMulAction α A]

open Pointwise

@[simp]
lemma smul_mem_pointwise_smul_iff {a : α} {S : AddSubgroup A} {x : A} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
#align add_subgroup.smul_mem_pointwise_smul_iff AddSubgroup.smul_mem_pointwise_smul_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : AddSubgroup A} {x : A} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
#align add_subgroup.mem_pointwise_smul_iff_inv_smul_mem AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : α} {S : AddSubgroup A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff
#align add_subgroup.mem_inv_pointwise_smul_iff AddSubgroup.mem_inv_pointwise_smul_iff

@[simp]
lemma pointwise_smul_le_pointwise_smul_iff {a : α} {S T : AddSubgroup A} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff
#align add_subgroup.pointwise_smul_le_pointwise_smul_iff AddSubgroup.pointwise_smul_le_pointwise_smul_iff

lemma pointwise_smul_le_iff {a : α} {S T : AddSubgroup A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff
#align add_subgroup.pointwise_smul_le_iff AddSubgroup.pointwise_smul_le_iff

lemma le_pointwise_smul_iff {a : α} {S T : AddSubgroup A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff
#align add_subgroup.le_pointwise_smul_iff AddSubgroup.le_pointwise_smul_iff

end Group

section GroupWithZero

variable [GroupWithZero α] [DistribMulAction α A]

open Pointwise

@[simp]
lemma smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x
#align add_subgroup.smul_mem_pointwise_smul_iff₀ AddSubgroup.smul_mem_pointwise_smul_iff₀

lemma mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x
#align add_subgroup.mem_pointwise_smul_iff_inv_smul_mem₀ AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem₀

lemma mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set A) x
#align add_subgroup.mem_inv_pointwise_smul_iff₀ AddSubgroup.mem_inv_pointwise_smul_iff₀

@[simp]
lemma pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubgroup A} :
    a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha
#align add_subgroup.pointwise_smul_le_pointwise_smul_iff₀ AddSubgroup.pointwise_smul_le_pointwise_smul_iff₀

lemma pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubgroup A} :
    a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha
#align add_subgroup.pointwise_smul_le_iff₀ AddSubgroup.pointwise_smul_le_iff₀

lemma le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubgroup A} :
    S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha
#align add_subgroup.le_pointwise_smul_iff₀ AddSubgroup.le_pointwise_smul_iff₀

end GroupWithZero

end AddSubgroup
