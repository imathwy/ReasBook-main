import StacksProject_2024.Chap17.Definition_17_25_1
import StacksProject_2024.Chap17.SheafOfModulesTensorUnit

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.RingedSpace

variable {X : Scheme.{u}}
variable [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
variable [SymmetricCategory (SheafOfModules X.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules X.ringCatSheaf)]

local notation "ModX" => SheafOfModules X.ringCatSheaf
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)
local notation "EffectiveCartierIdeal" =>
  (fun I : Subobject 𝒪X ↦
    Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))
local notation "IdealModule" => (fun I : Subobject 𝒪X ↦ Subobject.underlying.obj I)

-- Semantic recall: `lean_leansearch` surfaced only the ideal-sheaf side of the ambient scheme
-- API, so the owner choice below was checked against local precedents
-- `Definition_17_25_1`, `Definition_31_13_1`, and `Definition_31_14_6`: in this chapter an
-- effective Cartier divisor is represented by an ideal sheaf that is invertible as an
-- `𝒪_X`-module, the associated invertible sheaf is the internal-Hom inverse sheaf, and the
-- canonical section is packaged via `unitHomEquiv` after currying the ideal inclusion. This
-- file has a legacy filename, but its source-facing content is Stacks Definition 31.15.1
-- (tag `01WX`).

/-- Definition 31.15.1 (1): if `I` is the ideal sheaf of an effective Cartier divisor on a
scheme `X`, then the associated invertible sheaf `\mathcal O_X(D)` is
`\mathcal H\!\mathit{om}_{\mathcal O_X}(I, \mathcal O_X)`. -/
@[stacks 01WX]
abbrev effectiveCartierDivisorAssociatedSheaf
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] : ModX :=
  (ihom (IdealModule I)).obj 𝒪X

/-- The evaluation morphism exhibiting `\mathcal O_X(D)` as an inverse to `I`. -/
noncomputable abbrev effectiveCartierDivisorEvaluationHom
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    (IdealModule I ⊗ₘ effectiveCartierDivisorAssociatedSheaf I : ModX) ⟶ 𝒪X :=
  (ihom.ev (IdealModule I)).app 𝒪X

/-- Companion to `effectiveCartierDivisorAssociatedSheaf`: the associated invertible sheaf is the
inverse of the ideal sheaf, exhibited by the evaluation isomorphism
`I \otimes_{\mathcal O_X} \mathcal O_X(D) \cong \mathcal O_X`. -/
theorem effectiveCartierDivisorAssociatedSheaf_evaluationIso
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    IsIso (effectiveCartierDivisorEvaluationHom (X := X) I) := sorry

/-- The canonical morphism `\mathcal O_X ⟶ \mathcal O_X(D)` attached to the ideal inclusion. -/
noncomputable abbrev effectiveCartierDivisorCanonicalSectionHom
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    𝒪X ⟶ effectiveCartierDivisorAssociatedSheaf I :=
  let η : 𝒪X ≅ 𝟙_ ModX := SheafOfModules.unitIsoTensorUnit
  η.hom ≫ MonoidalClosed.curry ((ρ_ (IdealModule I)).hom ≫ I.arrow)

/-- Definition 31.15.1 (2): the canonical section `1_D` of `\mathcal O_X(D)` is the global
section corresponding to the inclusion `I \hookrightarrow \mathcal O_X`. -/
@[stacks 01WX]
abbrev effectiveCartierDivisorCanonicalSection
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    (effectiveCartierDivisorAssociatedSheaf I).sections :=
  (effectiveCartierDivisorAssociatedSheaf I).unitHomEquiv
    (effectiveCartierDivisorCanonicalSectionHom I)

/-- Definition 31.15.1 (3): for an effective Cartier divisor with ideal sheaf `I`, the notation
`\mathcal O_X(-D)` is the ideal sheaf itself. -/
@[stacks 01WX]
abbrev effectiveCartierDivisorNegSheaf
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] : ModX :=
  IdealModule I

/-- Definition 31.15.1 (4): for effective Cartier divisors with ideal sheaves `I` and `I'`, the
sheaf `\mathcal O_X(D - D')` is
`\mathcal O_X(D) \otimes_{\mathcal O_X} \mathcal O_X(-D')`. -/
@[stacks 01WX]
abbrev effectiveCartierDivisorDifferenceSheaf
    (I I' : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] [Fact (EffectiveCartierIdeal I')] :
    ModX :=
  effectiveCartierDivisorAssociatedSheaf I ⊗ₘ effectiveCartierDivisorNegSheaf I'

/-- Companion to `effectiveCartierDivisorDifferenceSheaf`: it is exactly the tensor product of
the positive and negative divisor sheaves appearing in the source formula. -/
theorem effectiveCartierDivisorDifferenceSheaf_def
    (I I' : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] [Fact (EffectiveCartierIdeal I')] :
    effectiveCartierDivisorDifferenceSheaf I I' =
      effectiveCartierDivisorAssociatedSheaf I ⊗ₘ effectiveCartierDivisorNegSheaf I' :=
  rfl

end AlgebraicGeometry.Scheme
