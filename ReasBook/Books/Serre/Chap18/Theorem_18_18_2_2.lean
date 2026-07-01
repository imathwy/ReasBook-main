import Mathlib
import Serre.Chap15.Exercise_15_15_1_2.Index
import Serre.Chap18.Remark_18_18_1_3
import Serre.Chap18.Theorem_18_18_2_1

open scoped TensorProduct

noncomputable section

universe u v

namespace Representation

section PRegularConjClassFunctions

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [AddCommGroup A]
variable {G : Type u} [Group G] [Finite G]

private abbrev virtualModularCharacterOnPRegularConjClassLift
    (lift : PrimeToPRoot p k → A) :
    FreeAbelianGroup (FDRep k G) →+ (PRegularConjClass G p → A) :=
  FreeAbelianGroup.lift fun E ↦
    FDRep.modularCharacterOnPRegularConjClass (p := p) (G := G) (A := A) E lift

private theorem
    finiteRepGrothendieckRelations_le_virtualModularCharacterOnPRegularConjClassLift_ker
    (lift : PrimeToPRoot p k → A) :
    finiteRepGrothendieckRelations k G ≤
      (virtualModularCharacterOnPRegularConjClassLift lift).ker := sorry

variable (p)

/-
Domain-style sampling:
* primary domain: Brauer/modular characters descended from `FDRep k G` to Serre's Grothendieck
  group and then restricted to the owner `PRegularConjClass G p`;
* inspected owner declarations in this domain:
  `FDRep.modularCharacterOnPRegularConjClass`,
  `virtualModularCharacter`,
  `modularCharacter_one_eq_finrank`,
  and `modularCharacter_tensor`;
* best owner abstraction: the additive Grothendieck descent of the canonical owner
  `FDRep.modularCharacterOnPRegularConjClass`, followed by scalar extension;
* primitive data: a lift `PrimeToPRoot p k → A`, the finite-representation Grothendieck relations,
  and the additive owner `virtualModularCharacter`;
* derived API: descent to `PRegularConjClass G p`, then multiplicativity and scalar extension.

Characteristic `p` is not primitive data for this descent layer. It first becomes essential only in
the later bijectivity/equivalence layer via Theorem `18-18.2-1`.
-/
/-- Bridge/view: the virtual modular character on Serre's Grothendieck group, descended from the
canonical `FDRep.modularCharacterOnPRegularConjClass` owner. -/
def virtualModularCharacterOnPRegularConjClass
    (lift : PrimeToPRoot p k → A) :
    R₀[k](G) →+ (PRegularConjClass G p → A) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (virtualModularCharacterOnPRegularConjClassLift lift)
    (finiteRepGrothendieckRelations_le_virtualModularCharacterOnPRegularConjClassLift_ker lift)

@[simp] theorem virtualModularCharacterOnPRegularConjClass_class
    (lift : PrimeToPRoot p k → A) (E : FDRep k G) :
    virtualModularCharacterOnPRegularConjClass p lift [E]₀ =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (G := G) (A := A) E lift := sorry

@[simp] theorem virtualModularCharacterOnPRegularConjClass_ofSubtype
    (lift : PrimeToPRoot p k → A) (x : R₀[k](G))
    (s : { x : G // IsPRegular p x }) :
    virtualModularCharacterOnPRegularConjClass p lift x (PRegularConjClass.ofSubtype p s) =
      virtualModularCharacter lift x s := sorry

@[simp] theorem virtualModularCharacterOnPRegularConjClass_class_ofSubtype
    (lift : PrimeToPRoot p k → A) (E : FDRep k G)
    (s : { x : G // IsPRegular p x }) :
    virtualModularCharacterOnPRegularConjClass p lift [E]₀ (PRegularConjClass.ofSubtype p s) =
      modularCharacter lift E.ρ s := by
  rw [virtualModularCharacterOnPRegularConjClass_ofSubtype]
  exact congrFun (virtualModularCharacter_class lift E) s

section Multiplicative

variable [CommRing A]

-- Proof sketch: on the unit class this is Proposition `18-18.1-2 (1)` after descending from the
-- `p`-regular locus to `PRegularConjClass G p`.
/-- On Serre's representation ring, the descended virtual modular character sends `1` to the
constant function `1`. -/
@[simp] theorem virtualModularCharacterOnPRegularConjClass_one
    (lift : PrimeToPRoot p k →* A) :
    virtualModularCharacterOnPRegularConjClass p lift (1 : R₀[k](G)) = 1 := by
  sorry

-- Proof sketch: compare both sides on actual classes using Proposition `18-18.1-2 (4)` and
-- `finiteRepGrothendieckClass_mul`, then extend the identity from generators to `R₀[k](G)`.
/-- On Serre's representation ring, the descended virtual modular character is multiplicative. -/
@[simp] theorem virtualModularCharacterOnPRegularConjClass_mul
    (lift : PrimeToPRoot p k →* A) (x y : R₀[k](G)) :
    virtualModularCharacterOnPRegularConjClass p lift (x * y) =
      virtualModularCharacterOnPRegularConjClass p lift x *
        virtualModularCharacterOnPRegularConjClass p lift y := by
  sorry

end Multiplicative

end PRegularConjClassFunctions

section ScalarExtension

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Type v} [Field K]
variable {G : Type u} [Group G] [Finite G]

-- source-facing: Serre's theorem identifies the scalar extension of `R₀[k](G)` with the full
-- function space on `PRegularConjClass G p`.
-- core/canonical: `virtualModularCharacter` from Remark `18-18.1-3`.
-- bridge/view: `virtualModularCharacterOnPRegularConjClass` descends that owner to regular
-- conjugacy classes, and `scalarExtensionVirtualModularCharacterOnPRegularConjClass` is its
-- canonical scalar extension to a `K`-linear map.
-- Proof sketch: extend `x ↦ φ_x` `K`-linearly from `R_k(G)` to `K ⊗[ℤ] R_k(G)`, then use
-- Theorem `18-18.2-1` together with the `ℤ`-basis theorem for `R_k(G)` to show that the resulting
-- map sends a scalar-extended simple-class basis to a basis of the full function space on
-- `PRegularConjClass G p`.
private def scalarExtensionVirtualModularCharacterOnPRegularConjClassLift
    (lift : PrimeToPRoot p k →* Kˣ) :
    K →ₗ[K] R₀[k](G) →ₗ[ℤ] (PRegularConjClass G p → K) where
  toFun := fun a ↦
    let φ : R₀[k](G) →+ (PRegularConjClass G p → K) :=
      (virtualModularCharacterOnPRegularConjClass
        (k := k) (A := K) (G := G) p (PrimeToPRoot.toFieldLift lift) :
        R₀[k](G) →+ (PRegularConjClass G p → K))
    { toFun := fun x ↦ a • φ x
      map_add' := by
        intro x y
        ext c
        rw [map_add]
        simp [Pi.smul_apply, mul_add]
      map_smul' := by
        sorry }
  map_add' a b := by
    sorry
  map_smul' a b := by
    sorry

/-- Bridge/view: the canonical `K`-linear scalar extension of the virtual modular character map on
`PRegularConjClass G p`. -/
def scalarExtensionVirtualModularCharacterOnPRegularConjClass
    (lift : PrimeToPRoot p k →* Kˣ) :
    K ⊗[ℤ] R₀[k](G) →ₗ[K] (PRegularConjClass G p → K) :=
  TensorProduct.AlgebraTensorModule.lift <|
    scalarExtensionVirtualModularCharacterOnPRegularConjClassLift lift

@[simp] theorem scalarExtensionVirtualModularCharacterOnPRegularConjClass_tmul
    (lift : PrimeToPRoot p k →* Kˣ) (a : K) (x : R₀[k](G)) :
    scalarExtensionVirtualModularCharacterOnPRegularConjClass lift (a ⊗ₜ[ℤ] x) =
      a •
        (virtualModularCharacterOnPRegularConjClass
          (k := k) (A := K) (G := G) p (PrimeToPRoot.toFieldLift lift) :
          R₀[k](G) →+ (PRegularConjClass G p → K)) x := by
  simp [scalarExtensionVirtualModularCharacterOnPRegularConjClass,
    scalarExtensionVirtualModularCharacterOnPRegularConjClassLift]

/-- Core/canonical multiplicative refinement of Theorem `18-18.2-2`: the scalar-extension
Brauer-character map is a `K`-algebra homomorphism to the function ring on
`PRegularConjClass G p`. -/
def scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom
    (lift : PrimeToPRoot p k →* Kˣ) :
    K ⊗[ℤ] R₀[k](G) →ₐ[K] (PRegularConjClass G p → K) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (scalarExtensionVirtualModularCharacterOnPRegularConjClass lift)
    (by
      sorry)
    (by
      sorry)

/-
The remaining statements use Theorem `18-18.2-1`, whose basis theorem genuinely requires
characteristic `p`. That hypothesis is therefore confined to this equivalence layer rather than the
owner declarations above.
-/
section Equivalence

variable [CharP k p]

/-- Theorem 18-18.2-2: the canonical `K`-linear scalar extension of the virtual modular character
map is a linear isomorphism from `K ⊗[ℤ] R_k(G)` onto the `K`-algebra of `K`-valued functions on
the `p`-regular conjugacy classes of `G`. -/
noncomputable def scalarExtensionVirtualModularCharacterOnPRegularConjClassLinearEquiv
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    K ⊗[ℤ] R₀[k](G) ≃ₗ[K] (PRegularConjClass G p → K) :=
  LinearEquiv.ofBijective
    (scalarExtensionVirtualModularCharacterOnPRegularConjClass lift)
    (by
      sorry)

/-- Companion: the underlying linear map of
`scalarExtensionVirtualModularCharacterOnPRegularConjClassLinearEquiv` is bijective. -/
theorem bijective_scalarExtensionVirtualModularCharacterOnPRegularConjClass
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    Function.Bijective
      (scalarExtensionVirtualModularCharacterOnPRegularConjClass lift :
        K ⊗[ℤ] R₀[k](G) →ₗ[K] (PRegularConjClass G p → K)) := by
  simpa [scalarExtensionVirtualModularCharacterOnPRegularConjClassLinearEquiv] using
    (scalarExtensionVirtualModularCharacterOnPRegularConjClassLinearEquiv lift hlift).bijective

/-- Theorem 18-18.2-2, canonical multiplicative form: the scalar-extension Brauer-character map is
a `K`-algebra isomorphism from `K ⊗[ℤ] R_k(G)` onto the function ring on the `p`-regular
conjugacy classes of `G`. -/
noncomputable def scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgEquiv
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    K ⊗[ℤ] R₀[k](G) ≃ₐ[K] (PRegularConjClass G p → K) :=
  AlgEquiv.ofBijective
    (scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom lift)
    (by
      let h :=
        bijective_scalarExtensionVirtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (K := K) (G := G) lift hlift
      exact ⟨h.1, h.2⟩)

end Equivalence

end ScalarExtension

end Representation
