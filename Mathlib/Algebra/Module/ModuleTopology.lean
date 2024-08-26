import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Finite.Card
import Mathlib.RingTheory.Finiteness
import Mathlib.Topology.Algebra.Module.Basic

/-!
# The module topology

If `R` is a topological ring and `M` is an `R`-module, the *module topology* on `M` is
the finest topology making all `R`-linear maps `Rⁿ → M` continuous. Here `n` runs through
the naturals and `Rⁿ` has the product topology. This topology has some nice properties.
For example if `D` is an `R`-algebra which is finite as an `R`-module, then `D` is
automatically a topological ring for the module topology.

## Details

If `R` is a topological ring and `A` is an `R`-module, then there are several ways in which
`A` can inherit a topology from `R` via the action (indeed, this is the 4th one which
the author has tried). We make one such definition here, which we call the *module* topology,
or the `R`-module topology if there is an ambiguity.

The module topology has some nice properties: for example all `R`-linear maps between modules
are automatically continuous for the module topology. On the category of finite `R`-modules
things are even better. Given any `R`-linear surjection `Rⁿ → A` for `n` a natural (or a
finite type), the topology on `A` is the pushforward (i.e. `TopologicalSpace.coinduced`)
of the product topology on `Rⁿ`. If furthermore `R` is commutative and `A` is an `R`-algebra
which is finite as an `R`-module, then `A` automatically becomes a topological ring for the
module topology (i.e., multiplication is continuous). This can be very convenient (for example
it can be used to topologise finite-dimensional central simple algebras over the reals
or $p$-adics).

## Main definitions

Let `R` be a topological ring and `A` an `R`-module.

* `moduleTopology R A : TopologicalSpace A` : The `R`-module topology on an `R`-module `A`.
* `IsModuleTopology T A : Prop` : Typeclass asserting that the topology on `A` is the
    module topology.
* `instPiFinite R ι` : a proof that if `ι` is finite then the product topology on `ι → R`
  is the module topology.

## TODO

(All these are proved in the FLT project, in FLT/ForMathlib/module_topology.lean)

* Addition is continuous for finite R-modules with the module topology
* Product of two finite modules with topologies is module topology
* Bilinear map from product of two finite modules is continuous when `R` is commutative.
* If `R` is commutative then an `R`-algebra finite as an `R`-module is automatically
  a topological ring with the module topology.

-/

section basics

variable (R : Type*) [TopologicalSpace R] [Ring R]
variable (A : Type*) [AddCommMonoid A] [Module R A]

/- The module topology on an `R`-module `M` is the finest topology
which makes all `R`-linear maps `Rⁿ →ₗ[R] M` continuous.
-/
abbrev moduleTopology : TopologicalSpace A :=
  ⨆ (n : ℕ), ⨆ (φ : (Fin n → R) →ₗ[R] A), .coinduced φ inferInstance

/-
`IsModuleTopology R A` is a propositional typclass carrying around a proof that the topology
on `A` is the `R`-module topology.-/
class IsModuleTopology [τA : TopologicalSpace A] : Prop where
  isModuleTopology' : τA = moduleTopology R A

-- because default binders for isModuleTopology' are wrong and currently
-- there is no way to change this. There's a Lean 4 issue for this IIRC **TODO** where?
lemma isModuleTopology [τA : TopologicalSpace A] [IsModuleTopology R A] :
    τA = moduleTopology R A :=
  IsModuleTopology.isModuleTopology' (R := R) (A := A)

end basics

namespace ModuleTopology

section one

variable (R : Type*) [Ring R] [τ : TopologicalSpace R] [TopologicalRing R]

instance instId : IsModuleTopology R R where
  isModuleTopology' := le_antisymm (le_iSup_of_le 1 <| le_iSup_of_le (LinearMap.proj 0)
    (fun U hU ↦ Continuous.isOpen_preimage (f := fun r ↦ fun _ ↦ r) (by fun_prop) _
      (isOpen_coinduced.1 hU))) <|
    iSup_le fun _ ↦ iSup_le fun φ ↦ continuous_iff_coinduced_le.1 <| LinearMap.continuous_on_pi φ

instance instPiNat (n : ℕ) : IsModuleTopology R (Fin n → R) where
  isModuleTopology' :=
    le_antisymm (le_iSup_of_le n <| le_iSup_of_le (LinearMap.id) <| by rfl) <|
      iSup_le fun _ ↦ iSup_le fun φ ↦ (LinearMap.continuous_on_pi φ).coinduced_le

instance instPiFinite (ι : Type*) [Finite ι] : IsModuleTopology R (ι → R) where
  isModuleTopology' :=
    le_antisymm (le_iSup_of_le (Nat.card ι) <| le_iSup_of_le
      (LinearMap.funLeft _ _ ((Finite.equivFin ι))) <| ge_of_eq <| Homeomorph.coinduced_eq
      (Homeomorph.piCongrLeft (Y := fun _ ↦ R) (Finite.equivFin ι)).symm) <|
      iSup_le fun _ ↦ iSup_le fun φ ↦ (LinearMap.continuous_on_pi φ).coinduced_le

end one

section function

variable {R : Type*} [τR : TopologicalSpace R] [Ring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]

/-- Every `A`-linear map between two `A`-modules with the module topology is
automatically continuous. -/
@[continuity, fun_prop]
lemma continuous_of_linearMap (f : A →ₗ[R] B) : Continuous f := by
  rw [isModuleTopology R A, isModuleTopology R B, continuous_iff_le_induced]
  apply iSup_le <| fun n ↦ iSup_le <| fun φ ↦ ?_
  rw [← coinduced_le_iff_le_induced, coinduced_compose]
  exact le_iSup_of_le n <| le_iSup_of_le (f.comp φ) le_rfl

/-- Two R-isomorphic R-modules are homeomorphic when equipped with the module topology. -/
def homeo_of_linearEquiv [IsModuleTopology R A] [IsModuleTopology R B] (f : A ≃ₗ[R] B) :
    A ≃ₜ B where
  toFun := f
  invFun := f.symm
  left_inv := LinearEquiv.symm_apply_apply f
  right_inv := LinearEquiv.apply_symm_apply f
  continuous_toFun := continuous_of_linearMap f.toLinearMap
  continuous_invFun := continuous_of_linearMap f.symm.toLinearMap

variable (R)

lemma continuous_neg (A : Type*) [AddCommGroup A] [Module R A] [TopologicalSpace A]
    [IsModuleTopology R A] : Continuous (-· : A → A) :=
  continuous_of_linearMap (LinearEquiv.neg R).toLinearMap

end function

section surj

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]

lemma coinduced_of_surjectivePi {n : ℕ} {φ : ((Fin n) → R) →ₗ[R] A} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ Pi.topologicalSpace = moduleTopology R A := by
  apply le_antisymm
  · rw [← continuous_iff_coinduced_le]
    rw [← isModuleTopology R A]
    fun_prop
  · apply iSup_le fun m ↦ iSup_le fun ψ ↦ ?_
    obtain ⟨α, rfl⟩ : ∃ α : (Fin m → R) →ₗ[R] (Fin n → R), φ.comp α = ψ :=
      Module.projective_lifting_property _ _ hφ
    push_cast
    rw [← coinduced_compose]
    apply coinduced_mono
    rw [← continuous_iff_coinduced_le]
    fun_prop

/-- Any surjection between finite R-modules is coinducing for the R-module topology. -/
lemma coinduced_of_surjective {B : Type*} [AddCommMonoid B] [aB : TopologicalSpace B] [Module R B]
    [Module.Finite R A] [IsModuleTopology R B] {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ aA = aB := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R A
  rw [isModuleTopology R A, isModuleTopology R B,
    ← coinduced_of_surjectivePi <| show Function.Surjective (φ ∘ₗ f) by aesop]
  push_cast
  rw [← coinduced_compose, coinduced_of_surjectivePi hf]

end surj

end ModuleTopology
