import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.Prod
import stacks_proof.stacks_project.Chap15.Lemma_15_91_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ModuleCat
open MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

/- 
Domain-style sampling:
- primary domain: the Beauville-Laszlo module Cech sequence, obtained from the ring-level Cech
  sequence by tensoring with `M` and distributing tensor product over products;
- sampled owner API:
  `beauvilleLaszloCechSequence`,
  `ShortComplex.map`,
  `TensorProduct.prodRight`,
  `ShortComplex.moduleCatMk`;
- best owner abstraction: the source-facing owner is the module Beauville-Laszlo Cech sequence,
  and its primitive maps should be derived from the upstream ring-level owner
  `beauvilleLaszloCechSequence (algebraMap R R') f` by tensoring and transporting along the
  canonical
  unit and product-distribution equivalences;
- source/core/bridge triage:
  `source-facing`: the displayed module Cech sequence for an `R`-module `M`;
  `core/canonical`: `beauvilleLaszloCechSequence`, `ShortComplex.map`,
  `TensorProduct.prodRight`, and `ShortComplex.moduleCatMk`;
  `bridge/view`: the internal unit and product-distribution identifications relating the displayed
  module sequence to the tensor image of the ring-level owner.

Primitive data are the ring-level Cech maps together with the tensor/product-distribution bridge to
the module sequence. The short complex is the owner; its component maps are derived projections and
should not be reintroduced as parallel primitive owners.
-/

section

variable {R : Type u} [CommRing R]
variable (R' : Type u) [CommRing R'] [Algebra R R']
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Helper for 15.91.9.1: the tensor image of the ring-level Beauville-Laszlo Cech sequence. -/
noncomputable abbrev beauvilleLaszloModuleCechTensorImage
    (f : R) :
    ShortComplex (ModuleCat R) :=
  (beauvilleLaszloCechSequence (algebraMap R R') f).map (tensorLeft (of R M))

/-- Helper for 15.91.9.1: the tensor-image middle object is definitionally the `tensorLeft` image
of the product ring term. -/
theorem beauvilleLaszloModuleCechMiddleTensor_eq
    (f : R) :
    let _ : Algebra R R' := (algebraMap R R').toAlgebra
    (beauvilleLaszloModuleCechTensorImage R' M f).X₂ =
      (tensorLeft (of R M)).obj (of R (R' × Localization.Away f)) := by
  let _ : Algebra R R' := (algebraMap R R').toAlgebra
  -- First identify the middle object of the ring-level owner, then map that equality through
  -- `tensorLeft`.
  change (tensorLeft (of R M)).obj ((beauvilleLaszloCechSequence (algebraMap R R') f).X₂) =
      (tensorLeft (of R M)).obj (of R (R' × Localization.Away f))
  have hX₂ :
      (beauvilleLaszloCechSequence (algebraMap R R') f).X₂ = of R (R' × Localization.Away f) := by
    -- Unfold the packaged ring-level owner down to its chosen middle object.
    simp
    rfl
  exact congrArg (fun X ↦ (tensorLeft (of R M)).obj X) hX₂

/-- Helper for 15.91.9.1: the tensor-image middle object is canonically the `tensorLeft` image of
the product ring term. -/
noncomputable abbrev beauvilleLaszloModuleCechMiddleTensorIso
    (f : R) :
    let _ : Algebra R R' := (algebraMap R R').toAlgebra
    (beauvilleLaszloModuleCechTensorImage R' M f).X₂ ≅
      (tensorLeft (of R M)).obj (of R (R' × Localization.Away f)) :=
  eqToIso (beauvilleLaszloModuleCechMiddleTensor_eq R' M f)

/-- Helper for 15.91.9.1: tensoring `of R N` on the left by `M` identifies with the module
object attached to the raw tensor product `M ⊗[R] N`. -/
noncomputable def tensorLeft_obj_tensorProductIso
    (N : Type u) [AddCommGroup N] [Module R N] :
    (tensorLeft (of R M)).obj (of R N) ≅ of R (M ⊗[R] N) := by
  -- The `ModuleCat` tensor object and the raw tensor-product module have the same underlying
  -- linear object; this bridge only packages that identification as an isomorphism.
  simpa [CategoryTheory.MonoidalCategory.tensorLeft] using
    (LinearEquiv.refl R (M ⊗[R] N)).toModuleIso

/-- Helper for 15.91.9.1: the tensor image middle object first identifies with the product term
built using the canonical scalar structure coming from `algebraMap R R'`. -/
noncomputable def beauvilleLaszloModuleCechCanonicalMiddleIso
    (f : R) :
    let _ : Algebra R R' := (algebraMap R R').toAlgebra
    (beauvilleLaszloModuleCechTensorImage R' M f).X₂ ≅
      of R ((M ⊗[R] R') × (M ⊗[R] Localization.Away f)) := by
  let _ : Algebra R R' := (algebraMap R R').toAlgebra
  exact
    (beauvilleLaszloModuleCechMiddleTensorIso R' M f) ≪≫
      (tensorLeft_obj_tensorProductIso (R := R) (M := M) (N := R' × Localization.Away f)) ≪≫
      (TensorProduct.prodRight R R M R' (Localization.Away f)).toModuleIso

/-- Helper for 15.91.9.1: the displayed middle module, using the canonical scalar structure on
`R'` induced by `algebraMap R R'`. -/
abbrev beauvilleLaszloModuleCechMiddleModule
    (f : R) : Type u :=
  let _ : Algebra R R' := (algebraMap R R').toAlgebra
  (M ⊗[R] R') × (M ⊗[R] Localization.Away f)

/-- Helper for 15.91.9.1: the tensor image middle object identifies with the product of the two
base-changed module terms. -/
noncomputable abbrev beauvilleLaszloModuleCechMiddleIso
    (f : R) :
    (beauvilleLaszloModuleCechTensorImage R' M f).X₂ ≅
      of R (beauvilleLaszloModuleCechMiddleModule R' M f) :=
  let _ : Algebra R R' := (algebraMap R R').toAlgebra
  beauvilleLaszloModuleCechCanonicalMiddleIso (R := R) (R' := R') (M := M) f

/-- Helper for 15.91.9.1: the tensor-image left object is identified with `M` by the right
unitor. -/
noncomputable abbrev beauvilleLaszloModuleCechLeftIso
    (f : R) :
    (beauvilleLaszloModuleCechTensorImage R' M f).X₁ ≅ of R M :=
  ρ_ (of R M)

/-- Helper for 15.91.9.1: the transported left map into the displayed middle module. -/
noncomputable abbrev beauvilleLaszloModuleCechAlpha
    (f : R) :
    M →ₗ[R] beauvilleLaszloModuleCechMiddleModule R' M f :=
  let tensorImage := beauvilleLaszloModuleCechTensorImage R' M f
  let leftIso : tensorImage.X₁ ≅ of R M := beauvilleLaszloModuleCechLeftIso R' M f
  let middleIso : tensorImage.X₂ ≅ of R (beauvilleLaszloModuleCechMiddleModule R' M f) :=
    beauvilleLaszloModuleCechMiddleIso R' M f
  (leftIso.inv ≫ tensorImage.f ≫ middleIso.hom).hom

/-- Helper for 15.91.9.1: the transported right map out of the displayed middle module. -/
noncomputable abbrev beauvilleLaszloModuleCechBeta
    (f : R) :
    beauvilleLaszloModuleCechMiddleModule R' M f →ₗ[R]
      (beauvilleLaszloModuleCechTensorImage R' M f).X₃ :=
  let tensorImage := beauvilleLaszloModuleCechTensorImage R' M f
  let middleIso : tensorImage.X₂ ≅ of R (beauvilleLaszloModuleCechMiddleModule R' M f) :=
    beauvilleLaszloModuleCechMiddleIso R' M f
  (middleIso.inv ≫ tensorImage.g).hom

/-- Helper for 15.91.9.1: the transported module Beauville-Laszlo Cech maps still form a complex. -/
theorem beauvilleLaszloModuleCech_comp_eq_zero
    (f : R) :
    (beauvilleLaszloModuleCechBeta R' M f).comp (beauvilleLaszloModuleCechAlpha R' M f) =
      (0 : M →ₗ[R] (beauvilleLaszloModuleCechTensorImage R' M f).X₃) := by
  let tensorImage := beauvilleLaszloModuleCechTensorImage R' M f
  let leftIso : tensorImage.X₁ ≅ of R M := beauvilleLaszloModuleCechLeftIso R' M f
  let middleIso : tensorImage.X₂ ≅
      of R (beauvilleLaszloModuleCechMiddleModule R' M f) :=
    beauvilleLaszloModuleCechMiddleIso R' M f
  let α : M →ₗ[R] beauvilleLaszloModuleCechMiddleModule R' M f :=
    beauvilleLaszloModuleCechAlpha R' M f
  let β : beauvilleLaszloModuleCechMiddleModule R' M f →ₗ[R] tensorImage.X₃ :=
    beauvilleLaszloModuleCechBeta R' M f
  -- Route correction: first transport the zero-composition identity in `ModuleCat R`, and only
  -- then read it as an equality of underlying linear maps.
  have hcomp :
      (leftIso.inv ≫ tensorImage.f ≫ middleIso.hom) ≫ (middleIso.inv ≫ tensorImage.g) = 0 := by
    -- Cancel the middle isomorphism and reuse the zero relation in the tensor-image complex.
    calc
      (leftIso.inv ≫ tensorImage.f ≫ middleIso.hom) ≫ (middleIso.inv ≫ tensorImage.g)
          = leftIso.inv ≫ (tensorImage.f ≫ tensorImage.g) := by
              simp [Category.assoc]
      _ = 0 := by
        simpa [Category.assoc] using congrArg (fun k ↦ leftIso.inv ≫ k) tensorImage.zero
  -- Evaluate the underlying linear-map identity pointwise to match the packaged `LinearMap.comp`.
  apply LinearMap.ext
  intro x
  change
      (ConcreteCategory.hom (middleIso.inv ≫ tensorImage.g))
          ((ConcreteCategory.hom (leftIso.inv ≫ tensorImage.f ≫ middleIso.hom)) x) = 0
  -- Evaluate the transported categorical zero-composition on `x`.
  exact congrArg (fun ζ : of R M ⟶ tensorImage.X₃ ↦ (ConcreteCategory.hom ζ) x) hcomp

/-- 15.91.9.1: the displayed sequence `0 → M → (M ⊗_R R') ⊕ (M ⊗_R R_f) → M ⊗_R R'_f → 0`,
represented in Lean by the `ShortComplex` in `ModuleCat R` built from the canonical
Beauville-Laszlo module Cech maps. Lean models the direct sum by the product
`(M ⊗[R] R') × (M ⊗[R] Localization.Away f)`. -/
@[stacks 0F1R]
abbrev beauvilleLaszloModuleCechSequence
    (f : R) :
    ShortComplex (ModuleCat R) :=
  -- Package the transported tensor-image maps as the displayed short complex.
  ShortComplex.moduleCatMk
    (beauvilleLaszloModuleCechAlpha R' M f)
    (beauvilleLaszloModuleCechBeta R' M f)
    (beauvilleLaszloModuleCech_comp_eq_zero R' M f)

end
