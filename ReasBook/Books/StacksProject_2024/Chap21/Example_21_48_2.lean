import Mathlib
import StacksProject_2024.Chap21.Definition_21_44_1
import StacksProject_2024.Chap21.Lemma_21_20_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ
local notation "ModLoc" U => LocalizedRingedSiteModules J 𝒪 U

/-- Restriction to a localized ringed site preserves zero morphisms. -/
private instance localizedRestriction_preservesZeroMorphisms
    (U : C) :
    (RingedSite.Hom.localizedRestriction X U).PreservesZeroMorphisms where
  map_zero _ _ := by
    rfl

/-- Restriction of cochain complexes of `\mathcal O`-modules to the localized ringed site over
`U`. -/
private abbrev localizedRestrictionComplex (U : C) :
    Cpx ⥤ CochainComplex (ModLoc U) ℤ :=
  (RingedSite.Hom.localizedRestriction X U).mapHomologicalComplex (ComplexShape.up ℤ)

namespace CochainComplex

/-- A complex of `\mathcal O`-modules on a ringed site is locally strictly perfect if every object
`U` admits a covering on whose members the restricted complex is strictly perfect. -/
def IsLocallyStrictlyPerfect (E : Cpx) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    IsStrictlyPerfect ((localizedRestrictionComplex I.Y).obj E)

end CochainComplex

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

namespace CochainComplex

/-- Unfolding `IsLocallyStrictlyPerfect` gives the explicit covering criterion by strictly perfect
restrictions. -/
theorem cochainComplex_isLocallyStrictlyPerfect_iff
    (E : Cpx) :
    IsLocallyStrictlyPerfect E ↔
      ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
        IsStrictlyPerfect ((localizedRestrictionComplex I.Y).obj E) :=
  Iff.rfl

end CochainComplex

end

section DualitySetup

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

open SheafOfModules.RingedSite.CochainComplex

section Duality

variable [MonoidalCategory (CochainComplex (RingedSiteModules J 𝒪) ℤ)]
variable [BraidedCategory (CochainComplex (RingedSiteModules J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (RingedSiteModules J 𝒪) ℤ)]

/-- The internal-Hom dual complex of `F^\bullet`, namely the canonical internal-Hom object from
`F^\bullet` to the tensor unit. -/
abbrev ringedSiteModuleComplexDual (F : Cpx) : Cpx :=
  (ihom F).obj (𝟙_ Cpx)

/-- The canonical morphism
`K^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O) \to
\mathcal H\!\mathit{om}^\bullet(F^\bullet, K^\bullet)`. -/
noncomputable def ringedSiteModuleComplexEvaluationHom
    (F K : Cpx) :
    K ⊗ ringedSiteModuleComplexDual F ⟶ (ihom F).obj K :=
  (β_ K (ringedSiteModuleComplexDual F)).hom ≫
    (ringedSiteModuleComplexDual F ◁ (unitIsoSelf K).symm.hom) ≫
    comp F (𝟙_ Cpx) K

/-- The canonical tensor-to-endomorphism morphism
`F^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O) \to
\mathcal H\!\mathit{om}^\bullet(F^\bullet, F^\bullet)`. -/
noncomputable abbrev ringedSiteModuleComplexDualTensorToEnd
    (F : Cpx) :
    F ⊗ ringedSiteModuleComplexDual F ⟶ (ihom F).obj F :=
  ringedSiteModuleComplexEvaluationHom F F

-- Proof sketch: work locally on an arbitrary object `U` of the site. On a covering where the
-- restricted complex is strictly perfect, the degreewise finite projective duality from More on
-- Algebra, Lemma `15.73.2`, gives the tensor-to-endomorphism isomorphism on each localized ringed
-- site; then glue these local isomorphisms.
/-- The canonical tensor-to-endomorphism map is an isomorphism for a complex that is locally
strictly perfect on a ringed site. -/
theorem ringedSiteModuleComplexDualTensorToEnd_isIso_of_isLocallyStrictlyPerfect
    {F : Cpx}
    (hF : IsLocallyStrictlyPerfect F) :
    IsIso (ringedSiteModuleComplexDualTensorToEnd F) := sorry

/-- The source-facing evaluation morphism
`\mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O) \otimes F^\bullet \to \mathcal O`
for the internal-Hom dual complex. -/
noncomputable def ringedSiteModuleComplexDualEvaluation
    (F : Cpx) :
    ringedSiteModuleComplexDual F ⊗ F ⟶ 𝟙_ Cpx :=
  (β_ (ringedSiteModuleComplexDual F) F).hom ≫
    (ihom.ev F).app (𝟙_ Cpx)

/-- The source-facing coevaluation morphism
`\mathcal O \to F^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O)`
obtained from the identity of `F^\bullet` via the tensor-to-endomorphism isomorphism. -/
noncomputable def ringedSiteModuleComplexDualCoevaluation
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    𝟙_ Cpx ⟶ F ⊗ ringedSiteModuleComplexDual F :=
  MonoidalClosed.curry' (𝟙 F) ≫
    inv (ringedSiteModuleComplexDualTensorToEnd F)

-- Proof sketch: transport the identity endomorphism of the dual complex across the
-- tensor-to-endomorphism isomorphism. Under the closed monoidal adjunction this becomes exactly
-- the first triangle identity.
/-- The source-facing coevaluation and evaluation maps of the internal-Hom dual satisfy the first
triangle identity. -/
theorem ringedSiteModuleComplexDual_coevaluation_evaluation
    {F : Cpx}
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    ringedSiteModuleComplexDual F ◁ ringedSiteModuleComplexDualCoevaluation F ≫
        (α_ _ _ _).inv ≫
        ringedSiteModuleComplexDualEvaluation F ▷ ringedSiteModuleComplexDual F =
      (ρ_ (ringedSiteModuleComplexDual F)).hom ≫
        (λ_ (ringedSiteModuleComplexDual F)).inv := sorry

-- Proof sketch: transport the identity of `F^\bullet` across the same tensor-to-endomorphism
-- isomorphism. The defining property of the coevaluation map then yields the second triangle
-- identity.
/-- The source-facing coevaluation and evaluation maps of the internal-Hom dual satisfy the second
triangle identity. -/
theorem ringedSiteModuleComplexDual_evaluation_coevaluation
    {F : Cpx}
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
        (α_ _ _ _).hom ≫
        F ◁ ringedSiteModuleComplexDualEvaluation F =
      (λ_ F).hom ≫ (ρ_ F).inv := sorry

/-- The source-facing tensor/unit maps package `\mathcal H\!\mathit{om}^\bullet(F^\bullet,
\mathcal O)` as the right-dual-style bridge needed before passing to the canonical left-dual owner
surface. -/
@[reducible] private noncomputable def exactPairingOfIsIso
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    ExactPairing (ringedSiteModuleComplexDual F) F :=
  letI : ExactPairing F (ringedSiteModuleComplexDual F) :=
    { coevaluation' := ringedSiteModuleComplexDualCoevaluation F
      evaluation' := ringedSiteModuleComplexDualEvaluation F
      coevaluation_evaluation' := ringedSiteModuleComplexDual_coevaluation_evaluation
      evaluation_coevaluation' := ringedSiteModuleComplexDual_evaluation_coevaluation }
  BraidedCategory.exactPairing_swap F (ringedSiteModuleComplexDual F)

/-- Example 21.48.2: if a complex `\mathcal F^\bullet` of `\mathcal O`-modules on a ringed site
is locally strictly perfect, then the internal-Hom dual
`\mathcal G^\bullet = \mathcal H\!\mathit{om}^\bullet(\mathcal F^\bullet, \mathcal O)` is a left
dual of `\mathcal F^\bullet`. In Lean this left-duality datum is packaged by the canonical owner
`CategoryTheory.ExactPairing (ringedSiteModuleComplexDual F) (\mathcal F^\bullet)`. -/
noncomputable abbrev ringedSiteModuleComplexDualExactPairing
    {F : Cpx}
    (hF : IsLocallyStrictlyPerfect F) :
    ExactPairing (ringedSiteModuleComplexDual F) F := by
  letI : IsIso (ringedSiteModuleComplexDualTensorToEnd F) :=
    ringedSiteModuleComplexDualTensorToEnd_isIso_of_isLocallyStrictlyPerfect hF
  exact exactPairingOfIsIso F

end Duality

end DualitySetup

end SheafOfModules.RingedSite
