import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_60_1
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorChangeOfRings
open scoped DerivedTensorProduct
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "σ" => (algebraMap R A)

local instance :
    ∀ (K₁ K₂ : CpxA), CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat A)) :=
  inferInstance

/- Domain-style sampling for Lemma 15.60.2:
- primary domain: derived change of rings `D(R) ⥤ D(A)` together with the right-variable
  functoriality of the derived tensor product on `D(A)`;
- sampled owner declarations:
  `derivedTensorChangeOfRings`,
  `derivedTensorWithAlgebra`,
  `derivedTensorProduct`,
  `tensoringRight`,
  `DerivedCategory.Q`;
- best owner abstraction: the source-facing owner is the chapter-local change-of-rings functor
  `derivedTensorChangeOfRings σ N : D(R) ⥤ D(A)`, while right-variable functoriality in `N`
  is implemented by the tensoring-right owner `(tensoringRight DModA).obj N` on `D(A)`;
- primitive vs. derived:
  primitive data are the complex map `f : L ⟶ N` and its image `DerivedCategory.Q.map f` in
  `D(A)`;
  the induced natural transformation between change-of-rings functors is derived API;
- source/core/bridge triage:
  `source-facing`: the map `1 \otimes f` on change-of-rings derived tensor functors;
  `core/canonical`: `derivedTensorChangeOfRings` together with the tensoring-right owner on
    `D(A)`;
  `bridge/view`: passing from a cochain complex to a derived object via `Q.obj`.
- layer: this file is a `bridge/view`, so its public entry should live over
  `derivedTensorChangeOfRings`, with the cochain-level map kept as a thin bridge via `Q.map`. -/

variable (R)

private noncomputable def derivedTensorChangeOfRingsIso
    (N : DModA) :
    derivedTensorWithAlgebra σ ⋙ (tensoringRight DModA).obj N ≅
      derivedTensorChangeOfRings σ N :=
  Functor.isoWhiskerLeft (derivedTensorWithAlgebra σ)
    (tensoringRightIsoDerivedTensorProduct N)

/-- Lemma 15.60.2: a morphism `f : L^• ⟶ N^•` of complexes of `A`-modules induces the natural
transformation `1 \otimes f` between the change-of-rings derived tensor functors
`- \otimes_R^{\mathbf L} L^•` and `- \otimes_R^{\mathbf L} N^•`; the quasi-isomorphism case is
recorded separately by `derivedTensorChangeOfRingsMap_isIso_of_quasiIso`. -/
@[stacks 0BYK]
noncomputable def derivedTensorChangeOfRingsMap
    {L N : DModA} (f : L ⟶ N) :
    derivedTensorChangeOfRings σ L ⟶ derivedTensorChangeOfRings σ N :=
  let eL := derivedTensorChangeOfRingsIso R L
  let eN := derivedTensorChangeOfRingsIso R N
  eL.inv ≫ Functor.whiskerLeft (derivedTensorWithAlgebra σ) ((tensoringRight DModA).map f) ≫ eN.hom

/-- The component of the map induced by `f : L ⟶ N` on change-of-rings derived tensor functors is
obtained by tensoring with `f` over `A`, transported through the canonical comparison between the
owner tensor and the source-facing derived tensor product. -/
@[simp]
theorem derivedTensorChangeOfRingsMap_app
    {L N : DModA} (f : L ⟶ N) (K : DModR) :
    (derivedTensorChangeOfRingsMap R f).app K =
      ((derivedCategory_tensorObj_iso_derivedTensorProduct
            (K ⊗[R]^L[A]) L).inv ≫
        ((K ⊗[R]^L[A]) ◁ f) ≫
        (derivedCategory_tensorObj_iso_derivedTensorProduct
            (K ⊗[R]^L[A]) N).hom :
          K ⊗[R]^L[A] L ⟶ K ⊗[R]^L[A] N) := by
  simp [derivedTensorChangeOfRingsMap, derivedTensorChangeOfRingsIso, derivedTensorChangeOfRings]

/-- The component of `1 \otimes f` at `K : D(R)` is obtained by tensoring the scalar-extended
object `K \otimes_R^{\mathbf L} A` with `Q.map f` over `A`, transported through the canonical
identifications with the right tensor functors on `D(A)`. -/
@[simp]
theorem derivedTensorChangeOfRingsMap_app_of_complexMap
    {L N : CpxA} (f : L ⟶ N) (K : DModR) :
    (derivedTensorChangeOfRingsMap R (DerivedCategory.Q.map f)).app K =
      ((derivedCategory_tensorObj_iso_derivedTensorProduct
            (K ⊗[R]^L[A]) (DerivedCategory.Q.obj L)).inv ≫
        ((K ⊗[R]^L[A]) ◁ DerivedCategory.Q.map f) ≫
        (derivedCategory_tensorObj_iso_derivedTensorProduct
            (K ⊗[R]^L[A]) (DerivedCategory.Q.obj N)).hom :
          K ⊗[R]^L[A] (DerivedCategory.Q.obj L) ⟶
            K ⊗[R]^L[A] (DerivedCategory.Q.obj N)) := by
  simpa using
    derivedTensorChangeOfRingsMap_app R (DerivedCategory.Q.map f) K

/-- If a morphism `f` in `D(A)` is an isomorphism, then the induced change-of-rings tensor map is
an isomorphism of functors `D(R) ⥤ D(A)`. -/
theorem derivedTensorChangeOfRingsMap_isIso
    {L N : DModA} (f : L ⟶ N) [IsIso f] :
    IsIso (derivedTensorChangeOfRingsMap R f) := by
  let eL := derivedTensorChangeOfRingsIso R L
  let eN := derivedTensorChangeOfRingsIso R N
  letI : IsIso ((tensoringRight DModA).map f) := by
    infer_instance
  letI (K : DModR) :
      IsIso
        ((Functor.whiskerLeft (derivedTensorWithAlgebra σ) ((tensoringRight DModA).map f)).app
          K) := by
    change IsIso (((tensoringRight DModA).map f).app ((derivedTensorWithAlgebra σ).obj K))
    infer_instance
  letI :
      IsIso (Functor.whiskerLeft (derivedTensorWithAlgebra σ) ((tensoringRight DModA).map f)) :=
    NatIso.isIso_of_isIso_app _
  letI : IsIso eL.inv := by
    infer_instance
  letI : IsIso eN.hom := by
    infer_instance
  change
    IsIso
      (eL.inv ≫
        Functor.whiskerLeft (derivedTensorWithAlgebra σ) ((tensoringRight DModA).map f) ≫
        eN.hom)
  infer_instance

/-- If `f` is a quasi-isomorphism, then the induced change-of-rings tensor transformation
`1 \otimes f` is an isomorphism of functors `D(R) ⥤ D(A)`. -/
theorem derivedTensorChangeOfRingsMap_isIso_of_quasiIso
    {L N : CpxA} (f : L ⟶ N) [QuasiIso f] :
    IsIso (derivedTensorChangeOfRingsMap R (DerivedCategory.Q.map f)) := by
  letI : IsIso (DerivedCategory.Q.map f) := by
    infer_instance
  simpa using
    derivedTensorChangeOfRingsMap_isIso R (DerivedCategory.Q.map f)

end

end CategoryTheory
