import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.Prod
import StacksProject_2024.Chap15.Lemma_15_91_6

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

/- 
15.91.9.1: the displayed sequence `0 → M → (M ⊗_R R') ⊕ (M ⊗_R R_f) → M ⊗_R R'_f → 0`,
represented in Lean by the `ShortComplex` in `ModuleCat R` built from the canonical
Beauville-Laszlo module Cech maps. Lean models the direct sum by the product
`(M ⊗[R] R') × (M ⊗[R] Localization.Away f)`.
-/
abbrev beauvilleLaszloModuleCechSequence
    (f : R) :
    ShortComplex (ModuleCat R) :=
  let _ : Algebra R R' := (algebraMap R R').toAlgebra
  let tensorImage :=
    (beauvilleLaszloCechSequence (algebraMap R R') f).map (tensorLeft (of R M))
  let X₂ := (M ⊗[R] R') × (M ⊗[R] Localization.Away f)
  let leftIso : tensorImage.X₁ ≅ of R M := ρ_ (of R M)
  let middleTensorIso :
      tensorImage.X₂ ≅ (of R M ⊗ of R (R' × Localization.Away f)) := by
    change ((tensorLeft (of R M)).obj (of R (R' × Localization.Away f))) ≅
        (of R M ⊗ of R (R' × Localization.Away f))
    rfl
  let middleIso : tensorImage.X₂ ≅ of R X₂ :=
    middleTensorIso ≪≫ (TensorProduct.prodRight R R M R' (Localization.Away f)).toModuleIso
  let X₃ := tensorImage.X₃
  let α : M →ₗ[R] X₂ :=
    (leftIso.inv ≫ tensorImage.f ≫ middleIso.hom).hom
  let β : X₂ →ₗ[R] X₃ :=
    (middleIso.inv ≫ tensorImage.g).hom
  ShortComplex.moduleCatMk α β <| by
    apply LinearMap.ext
    intro x
    simpa [α, β] using tensorImage.moduleCat_zero_apply (leftIso.inv.hom x)

end
