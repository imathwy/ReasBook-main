import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The unbounded derived category `D(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
abbrev RingedSpaceDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Tensoring on the left by `K ⊗ L` is naturally isomorphic to first tensoring on the left by
`K` and then by `L`, using the braiding to put the tensor factors in the Stacks Project order. -/
noncomputable abbrev ringedSpaceDerivedTensorLeftTensorIso
    (K L : RingedSpaceDerived X) :
    tensorLeft (K ⊗ L) ≅ tensorLeft K ⋙ tensorLeft L :=
  ((MonoidalCategory.tensoringLeft (RingedSpaceDerived X)).mapIso (β_ K L)) ≪≫
    MonoidalCategory.tensorLeftTensor L K

/-- The functorial tensor-internal-Hom currying isomorphism on `D(\mathcal O_X)`. -/
noncomputable def ringedSpaceDerivedInternalHomTensorNatIso
    (K L : RingedSpaceDerived X) :
    ihom L ⋙ ihom K ≅ ihom (K ⊗ L) :=
  (Adjunction.rightAdjointUniq
      (ihom.adjunction (K ⊗ L))
      (((ihom.adjunction K).comp (ihom.adjunction L)).ofNatIsoLeft
        (ringedSpaceDerivedTensorLeftTensorIso K L).symm)).symm

/-- Lemma 20.42.2: for a ringed space `(X, \mathcal O_X)` and objects
`K, L, M ∈ D(\mathcal O_X)`, there is a canonical isomorphism
`R\mathcal H\!\mathit{om}(K, R\mathcal H\!\mathit{om}(L, M)) \cong
R\mathcal H\!\mathit{om}(K \otimes_{\mathcal O_X}^{\mathbf L} L, M)`,
functorial in `K`, `L`, and `M`. Taking `H^0(X, -)` recovers `20.42.0.1`. -/
noncomputable def ringedSpaceDerivedInternalHomTensorIso
    (K L M : RingedSpaceDerived X) :
    (ihom K).obj ((ihom L).obj M) ≅ (ihom (K ⊗ L)).obj M :=
  (ringedSpaceDerivedInternalHomTensorNatIso K L).app M

-- Proof sketch: both sides are definitionally the component at `M` of the functorial
-- isomorphism `ringedSpaceDerivedInternalHomTensorNatIso K L`.
/-- The textbook isomorphism is the component at `M` of the functorial currying isomorphism. -/
theorem ringedSpaceDerivedInternalHomTensorIso_eq_app
    (K L M : RingedSpaceDerived X) :
    ringedSpaceDerivedInternalHomTensorIso K L M =
      (ringedSpaceDerivedInternalHomTensorNatIso K L).app M := sorry

end

end AlgebraicGeometry.RingedSpace
