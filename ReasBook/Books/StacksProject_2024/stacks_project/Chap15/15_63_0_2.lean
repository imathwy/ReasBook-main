import Mathlib
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Lemma_15_60_1

-- Auxiliary bridge owner recalls for `Lemma_15_63_1`.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorChangeOfRings DerivedTensorProduct DerivedTensorWithAlgebra TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (K L : DerivedCategory (ModuleCat R))

/- Domain-style sampling for 15.63.0.2:
- primary domain: monoidality of derived scalar extension and its compatibility with the chapter
  derived tensor product notation;
- sampled owner declarations:
  `ModuleCat.extendScalarsTensorLeftNatIso`,
  `derivedTensorWithAlgebra`,
  `derivedCategory_tensorObj_iso_derivedTensorProduct`;
- best owner abstraction: this item is a `bridge/view`; its source-facing content is the canonical
  derived comparison
  `(K ⊗[R]^L[A]) ⊗[A]^L (L ⊗[R]^L[A]) ≅ ((K ⊗[R]^L L) ⊗[R]^L[A])`,
  while the owner-level ingredients are the monoidal comparison for
  `derivedTensorWithAlgebra (algebraMap R A)` and the chapter bridge
  `derivedCategory_tensorObj_iso_derivedTensorProduct`;
- primitive data: the algebra `R → A`, the derived scalar-extension owner
  `derivedTensorWithAlgebra (algebraMap R A)`, and the two derived objects `K` and `L`;
- derived API: the displayed source-facing comparison is obtained by transporting the owner-level
  monoidal comparison through `derivedCategory_tensorObj_iso_derivedTensorProduct` on `D(R)` and
  `D(A)`, so the file should expose that derived bridge directly rather than the underived
  `ModuleCat.extendScalarsTensorLeftNatIso`.

Source/core/bridge triage:
- `source-facing`: the tensor/base-change identification in `D(A)` between base change of a
  derived tensor product and the derived tensor product of the two base-changed factors;
- `core/canonical`: `derivedTensorWithAlgebra (algebraMap R A)` together with
  `derivedCategory_tensorObj_iso_derivedTensorProduct`;
- `bridge/view`: the source-facing comparison type below, written directly in the chapter
  notation for the two derived tensor constructions. -/

/- 15.63.0.2: the source-facing derived comparison is the canonical isomorphism type
`(K ⊗[R]^L[A]) ⊗[A]^L (L ⊗[R]^L[A]) ≅ ((K ⊗[R]^L L) ⊗[R]^L[A])`. Its construction uses the
owner-level scalar-extension functor `derivedTensorWithAlgebra (algebraMap R A)` together with the
chapter tensor bridge `derivedCategory_tensorObj_iso_derivedTensorProduct`; the file should record
this derived comparison surface rather than the underived module-category precursor. -/
#check
  (((K ⊗[R]^L[A]) ⊗[A]^L (L ⊗[R]^L[A])) ≅
    ((K ⊗[R]^L L) ⊗[R]^L[A]))

end

end CategoryTheory
