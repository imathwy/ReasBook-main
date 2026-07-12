import StacksProject_2024.Chap20.Lemma_20_55_6
import StacksProject_2024.Chap20.RingedSpaceModuleHasDerivedCategory

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open scoped IdealEtaComplex

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "CpxX" => CochainComplex ModX ℤ
local notation "DModX" => DerivedCategory ModX
local notation "QX" => (DerivedCategory.Q : CpxX ⥤ DModX)
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
variable {I : Subobject 𝒪X}
local notation "Pη[" I "]" => IsIdealTorsionFreeComplex I

section

variable (I : Subobject 𝒪X)
variable [SatisfiesLocallyPrincipalRegularIdealCondition I]

/-
Domain-style sampling for 20.55.7:
- primary domain: additive endofunctors on `D(𝒪_X)` realizing the Berthelot-Ogus
  construction on `𝓘`-torsion free complexes;
- sampled owner declarations:
  `IdealEtaComplex.map`,
  `IdealEtaComplex.torsionFreeFunctor`,
  `DerivedCategory.Q`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction:
  `source-facing`: existence of a derived Berthelot-Ogus endofunctor together with its
    computation rule on `𝓘`-torsion free representatives;
  `core/canonical`: a functor `F : D(𝒪_X) ⥤ D(𝒪_X)` plus the Prop-level owner
    `CategoryTheory.IsIsomorphic`;
  `bridge/view`: the objectwise comparison
    `F.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj (η[I] K hK)` for torsion-free
    complexes `K`.

Primitive data here are the underived Berthelot-Ogus complexes `η[I] K hK`. Because the
localization/equivalence proof producing a total endofunctor still depends on an unresolved
existence theorem, the public API in REFINE stays at the source-faithful existential/specification
layer instead of choosing a sorry-backed endofunctor witness.
-/

namespace Functor

/-- A functor `F : D(𝒪_X) ⥤ D(𝒪_X)` satisfies the Berthelot-Ogus derived
specification for `𝓘` if it is additive and, on each `𝓘`-torsion free complex
`K`, it is equipped with the canonical comparison isomorphism
`F.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj (η[I] K hK)`. -/
class IsIdealEtaDerived (I : Subobject 𝒪X)
    [SatisfiesLocallyPrincipalRegularIdealCondition I] (F : DModX ⥤ DModX) where
  additive : F.Additive
  objIso (K : CpxX) (hK : Pη[I] K) :
    F.obj ((QX).obj K) ≅ (QX).obj (η[I] K hK)

attribute [instance] IsIdealEtaDerived.additive

end Functor

/-- Helper for Lemma 20.55.7: any Berthelot-Ogus derived endofunctor computes on an
`𝓘`-torsion free complex `K` by the underived Berthelot-Ogus complex `η[I] K hK`, in the
Prop-level owner `CategoryTheory.IsIsomorphic`. -/
theorem idealEtaDerivedFunctor_obj_isomorphic
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I]
    (F : DModX ⥤ DModX) [Functor.IsIdealEtaDerived I F]
    (K : CpxX) (hK : Pη[I] K) :
    IsIsomorphic (F.obj ((QX).obj K)) ((QX).obj (η[I] K hK)) :=
  ⟨Functor.IsIdealEtaDerived.objIso K hK⟩

-- Proof sketch: localize the Berthelot-Ogus functor on the full subcategory of
-- `𝓘`-torsion free complexes and use the source theorem that every derived object is
-- represented up to quasi-isomorphism by such a complex. The resulting endofunctor is additive,
-- and its value on a torsion-free representative `K` is computed by `η[I] K hK`.
/-- Lemma 20.55.7: there exists an additive endofunctor on `D(𝒪_X)` whose value on each
`𝓘`-torsion free representative `K` is isomorphic to `DerivedCategory.Q.obj (η[I] K hK)`.
-/
@[stacks 0F8Q]
theorem exists_idealEtaDerivedFunctor
    (I : Subobject 𝒪X) [SatisfiesLocallyPrincipalRegularIdealCondition I] :
    Nonempty (Σ F : DModX ⥤ DModX, Functor.IsIdealEtaDerived I F) := by
  sorry

end

end AlgebraicGeometry.RingedSpace
