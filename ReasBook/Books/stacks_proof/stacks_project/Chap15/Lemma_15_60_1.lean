import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Definition_15_59_13
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A]

/- Domain-style sampling for Lemma 15.60.1:
- primary domain: derived change of rings for module categories over a commutative ring map and a
  fixed derived target complex over the target ring;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `derivedTensorProduct`,
  `Functor.totalLeftDerived`,
  `Functor.totalLeftDerivedCounit`;
- best owner abstraction: the source-facing owner is the general change-of-rings functor
  `derivedTensorChangeOfRings σ N : D(R) ⥤ D(A)` for an explicit ring map `σ : R →+* A`, built
  from the canonical derived scalar-extension owner `derivedTensorWithAlgebra σ` and the derived
  tensor-product owner `derivedTensorProduct N` on `D(A)`;
- primitive vs. derived:
  primitive data are the explicit ring map `σ`, the fixed object `N : D(A)`, and the two owner
  functors `derivedTensorWithAlgebra σ` and `derivedTensorProduct N`;
  the change-of-rings functor and its notation are derived API over those owners;
- source/core/bridge triage:
  `source-facing`: `derivedTensorChangeOfRings σ N`;
  `core/canonical`: `derivedTensorWithAlgebra σ` and `derivedTensorProduct N`;
  `bridge/view`: the textbook object notation `K ⊗[R]^L[A] N`. -/

local notation "DModA" => DerivedCategory (ModuleCat A)

local instance :
    ∀ (K₁ K₂ : CochainComplex (ModuleCat A) ℤ),
      CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat A)) :=
  inferInstance

/-- Lemma 15.60.1: for a fixed derived `A`-complex `N^•`, the change-of-rings derived tensor
functor `- \otimes_R^{\mathbf L} N^• : D(R) ⟶ D(A)` is defined as the composite of derived
scalar extension `- \otimes_R^{\mathbf L} A` with the derived tensor product functor
`- \otimes_A^{\mathbf L} N^•` on `D(A)`. -/
@[stacks 06Y6]
noncomputable def derivedTensorChangeOfRings
    (σ : R →+* A) (N : DModA) :
    DerivedCategory (ModuleCat R) ⥤ DModA :=
  derivedTensorWithAlgebra σ ⋙ derivedTensorProduct N

namespace DerivedTensorChangeOfRings

/- Textbook notation for the derived change-of-rings object
`K \otimes_R^{\mathbf L} N` in `D(A)`. -/
scoped notation:70 K:70 " ⊗[" R:70 "]^L[" A:70 "] " N:71 =>
  Functor.obj (CategoryTheory.derivedTensorChangeOfRings (algebraMap R A) N) K

end DerivedTensorChangeOfRings

open scoped DerivedTensorChangeOfRings

/-- The change-of-rings derived tensor functor commutes with the triangulated shift. -/
noncomputable instance derivedTensorChangeOfRings_commShift (σ : R →+* A) (N : DModA) :
    (derivedTensorChangeOfRings σ N).CommShift ℤ := by
  dsimp [derivedTensorChangeOfRings]
  infer_instance

-- Proof sketch: this is the composition of the exact functors `- \otimes_R^{\mathbf L} A` and
-- `- \otimes_A^{\mathbf L} N^•`, so the result is exact by functoriality of triangulated
-- structure under composition.
/-- The change-of-rings derived tensor functor is exact in the triangulated sense. -/
theorem derivedTensorChangeOfRings_isTriangulated (σ : R →+* A) (N : DModA) :
    (derivedTensorChangeOfRings σ N).IsTriangulated := by
  let F := derivedTensorWithAlgebra σ
  let G := derivedTensorProduct N
  letI : F.CommShift ℤ := by
    simpa [F] using (inferInstance : (derivedTensorWithAlgebra σ).CommShift ℤ)
  letI : G.CommShift ℤ := by
    simpa [G] using (derivedTensorProduct_commShift N)
  letI : F.IsTriangulated := by
    simpa [F] using derivedTensorWithAlgebra_isTriangulated σ
  letI : G.IsTriangulated := by
    simpa [G] using derivedTensorProduct_isTriangulated N
  change (F ⋙ G).IsTriangulated
  exact
    { map_distinguished := fun T hT ↦
        Pretriangulated.isomorphic_distinguished _
          (G.map_distinguished _ (F.map_distinguished T hT)) _
          ((Functor.mapTriangleCompIso F G).app T) }

end

end CategoryTheory
