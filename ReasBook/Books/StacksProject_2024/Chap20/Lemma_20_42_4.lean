import Mathlib
import StacksProject_2024.Chap20.Definition_20_26_14

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.Pretriangulated.Opposite
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.42.4:
- primary domain: triangulatedness of derived internal-Hom functors on `D(\mathcal O_X)`;
- sampled owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct_isTriangulated`,
  `CategoryTheory.ihom`,
  `CategoryTheory.MonoidalClosed.internalHom`,
  `CategoryTheory.Adjunction.isTriangulated_rightAdjoint`;
- best owner abstraction:
  `ihom K` for the second-variable functor `R\mathcal H\!\mathit{om}(K,-)`, whose left adjoint is
  the chapter owner `derivedTensorProduct K = tensorLeft K`, and
  `MonoidalClosed.internalHom.flip.obj L` for the first-variable contravariant functor
  `R\mathcal H\!\mathit{om}(-,L)`;
- primitive data:
  a ringed space `X`, the owner category `DerivedCategory (RingedSpace.Modules X)`, and a fixed object of
  that category;
- derived API:
  the exactness of `tensorLeft K` from `derivedTensorProduct_isTriangulated`, the induced
  `Functor.CommShift` on `ihom K`, and the resulting `Functor.IsTriangulated` statements.

Source/core/bridge triage:
- `source-facing`: Lemma 20.42.4, asserting exactness of derived internal Hom in each variable;
- `core/canonical`: `derivedTensorProduct`, `ihom`, `MonoidalClosed.internalHom`, and
  `Adjunction.isTriangulated_rightAdjoint`;
- `bridge/view`: the specialization from the canonical owner category `DerivedCategory
  (RingedSpace.Modules X)` to the ringed-space language of the lemma.
-/

section

variable {X : RingedSpace.{u}}
local notation "ModX" => (RingedSpace.Modules X)
local notation "DModX" => DerivedCategory ModX

local instance : Abelian ModX := inferInstance

-- Proof sketch: `ihom K` is the right adjoint of `tensorLeft K`, and on `D(\mathcal O_X)` the
-- left adjoint is exactly the chapter owner `derivedTensorProduct K`. Definition `20.26.14`
-- gives that this left adjoint is triangulated, so the canonical adjunction theorem
-- `Adjunction.isTriangulated_rightAdjoint` yields exactness of `R\mathcal H\!\mathit{om}(K,-)`.
/-- Lemma 20.42.4 (1): for a ringed space `(X, \mathcal O_X)` and a fixed object
`K ∈ D(\mathcal O_X)`, the functor `R\mathcal H\!\mathit{om}(K, -)` sends distinguished triangles
in `D(\mathcal O_X)` to distinguished triangles. -/
theorem ringedSpaceDerivedInternalHom_isTriangulated_in_second_variable
    (K : DModX)
    [CategoryWithHomology ModX] [HasCountableCoproducts ModX]
    [MonoidalCategory ModX] [MonoidalPreadditive ModX] [HasColimits ModX]
    [(curriedTensor ModX).Additive]
    [∀ F : ModX, ((curriedTensor ModX).obj F).Additive]
    [∀ (F G : CochainComplex ModX ℤ), CochainComplex.HasMapBifunctor F G (curriedTensor ModX)]
    [MonoidalCategory DModX] [MonoidalClosed DModX]
    [HasZeroObject DModX] [Preadditive DModX]
    [HasShift DModX ℤ] [∀ n : ℤ, (shiftFunctor DModX n).Additive]
    [Pretriangulated DModX] [Functor.CommShift (ihom K) ℤ] :
    (ihom K).IsTriangulated := sorry

-- Proof sketch: the contravariant owner `MonoidalClosed.internalHom.flip.obj L` becomes
-- `ihom (op L)` after passing to the opposite category. Part (1) applied on `D(\mathcal O_X)ᵒᵖ`
-- shows that this opposite functor is triangulated, and `Functor.isTriangulated_of_op` transports
-- the result back to the contravariant source-variable functor.
/-- Lemma 20.42.4 (2): for a ringed space `(X, \mathcal O_X)` and a fixed object
`L ∈ D(\mathcal O_X)`, the contravariant functor `R\mathcal H\!\mathit{om}(-, L)` from
`D(\mathcal O_X)ᵒᵖ` to `D(\mathcal O_X)` sends distinguished triangles to distinguished
triangles. -/
theorem ringedSpaceDerivedInternalHom_isTriangulated_in_first_variable
    (L : DModX)
    [CategoryWithHomology ModX] [HasCountableCoproducts ModX]
    [MonoidalCategory ModX] [MonoidalPreadditive ModX] [HasColimits ModX]
    [(curriedTensor ModX).Additive]
    [∀ F : ModX, ((curriedTensor ModX).obj F).Additive]
    [∀ (F G : CochainComplex ModX ℤ), CochainComplex.HasMapBifunctor F G (curriedTensor ModX)]
    [MonoidalCategory DModX] [MonoidalClosed DModX]
    [HasZeroObject DModX] [Preadditive DModX]
    [HasShift DModX ℤ] [∀ n : ℤ, (shiftFunctor DModX n).Additive]
    [Pretriangulated DModX]
    [Functor.CommShift (MonoidalClosed.internalHom.flip.obj L) ℤ] :
    (MonoidalClosed.internalHom.flip.obj L).IsTriangulated := sorry

end

end AlgebraicGeometry.RingedSpace
