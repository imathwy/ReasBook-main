import Mathlib
import stacks_project.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ
local notation "OpenComplex" U => CochainComplex (openSubspaceModuleCategory X U) ℤ

/-- Restriction of cochain complexes of `\mathcal O_X`-modules to an open subspace. -/
private abbrev restrictionComplex (U : Opens X.carrier) :
    CpxX ⥤ OpenComplex U :=
  (moduleRestrictionToOpen X U).mapHomologicalComplex (ComplexShape.up ℤ)

/- 
Domain-style sampling for Example 20.50.2:
- primary domain: closed-monoidal duality for cochain complexes of `\mathcal O_X`-modules on a
  ringed space;
- inspected owner declarations:
  `CategoryTheory.ExactPairing`,
  `CategoryTheory.BraidedCategory.exactPairing_swap`,
  `unitInternalHomExactPairing`,
  `internalHomToUnit_exactPairing`,
  `ringedSiteModuleComplexDualExactPairing`;
- best owner abstraction: `CategoryTheory.ExactPairing` is the core owner for the left-dual datum,
  while `CochainComplex.IsLocallyStrictlyPerfect` is the source-facing local hypothesis;
- primitive data: the canonical internal-Hom object `(ihom F).obj (𝟙_ CpxX)`, the
  tensor-to-endomorphism comparison, and the canonical evaluation/coevaluation maps;
- derived API: the exact-pairing package and the downstream uniqueness isomorphism from an
  arbitrary chosen dual to the canonical internal-Hom dual.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.IsLocallyStrictlyPerfect`;
- `core/canonical`: `CategoryTheory.ExactPairing`;
- `bridge/view`: `ringedSpaceModuleComplexDualExactPairing`.
-/

/-- A complex of `\mathcal O_X`-modules is locally strictly perfect if some open covering of `X`
has strictly perfect restrictions of the complex. -/
def CochainComplex.IsLocallyStrictlyPerfect (E : CpxX) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X.carrier),
    IsOpenCover U ∧
      ∀ i : ι,
        CochainComplex.IsStrictlyPerfect ((restrictionComplex (U i)).obj E)

-- Proof sketch: unfold `CochainComplex.IsLocallyStrictlyPerfect`; this is exactly the chosen
-- open-cover formulation saying that the restriction of `E` to each member of the cover is
-- strictly perfect.
/-- Unfolding `IsLocallyStrictlyPerfect` gives the open-cover criterion by strictly perfect
restrictions. -/
theorem cochainComplex_isLocallyStrictlyPerfect_iff
    (E : CpxX) :
    CochainComplex.IsLocallyStrictlyPerfect E ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι,
            CochainComplex.IsStrictlyPerfect ((restrictionComplex (U i)).obj E) :=
  Iff.rfl

section Duality

variable [MonoidalCategory (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [BraidedCategory (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [MonoidalClosed (CochainComplex (RingedSpace.Modules X) ℤ)]

/-- The canonical morphism
`K^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O_X) \to
\mathcal H\!\mathit{om}^\bullet(F^\bullet, K^\bullet)`. -/
noncomputable def ringedSpaceModuleComplexEvaluationHom
    (F K : CpxX) :
    K ⊗ (ihom F).obj (𝟙_ CpxX) ⟶ (ihom F).obj K :=
  (β_ K ((ihom F).obj (𝟙_ CpxX))).hom ≫
    ((ihom F).obj (𝟙_ CpxX) ◁ (unitIsoSelf K).symm.hom) ≫
    comp F (𝟙_ CpxX) K

/-- The canonical tensor-to-endomorphism morphism
`F^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O_X) \to
\mathcal H\!\mathit{om}^\bullet(F^\bullet, F^\bullet)`. -/
noncomputable abbrev ringedSpaceModuleComplexDualTensorToEnd
    (F : CpxX) :
    F ⊗ (ihom F).obj (𝟙_ CpxX) ⟶ (ihom F).obj F :=
  ringedSpaceModuleComplexEvaluationHom F F

-- Proof sketch: the question is local on `X`. On each open of the chosen cover the restricted
-- complex is strictly perfect, so degreewise finite-free duality and Lemma `15.73.2` give the
-- tensor-to-endomorphism isomorphism for the restricted complex; then glue these local
-- isomorphisms back along the cover.
/-- The canonical tensor-to-endomorphism map is an isomorphism for a locally strictly perfect
complex. -/
theorem ringedSpaceModuleComplexDualTensorToEnd_isIso_of_isLocallyStrictlyPerfect
    {F : CpxX} (hF : CochainComplex.IsLocallyStrictlyPerfect F) :
    IsIso (ringedSpaceModuleComplexDualTensorToEnd F) := sorry

/-- The evaluation morphism
`\mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O_X) \otimes F^\bullet \to \mathcal O_X`
for the internal-Hom dual complex. -/
noncomputable def ringedSpaceModuleComplexDualEvaluation
    (F : CpxX) :
    ((ihom F).obj (𝟙_ CpxX)) ⊗ F ⟶ 𝟙_ CpxX :=
  (β_ ((ihom F).obj (𝟙_ CpxX)) F).hom ≫
    MonoidalClosed.uncurry (𝟙 ((ihom F).obj (𝟙_ CpxX)))

/-- The coevaluation morphism
`\mathcal O_X \to F^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O_X)`
obtained from the identity of `F^\bullet` via the tensor-to-endomorphism isomorphism. -/
noncomputable def ringedSpaceModuleComplexDualCoevaluation
    (F : CpxX)
    [IsIso (ringedSpaceModuleComplexDualTensorToEnd F)] :
    𝟙_ CpxX ⟶ F ⊗ (ihom F).obj (𝟙_ CpxX) :=
  MonoidalClosed.curry' (𝟙 F) ≫
    inv (ringedSpaceModuleComplexDualTensorToEnd F)

-- Proof sketch: transport the identity endomorphism of the dual complex across the adjunction
-- defining `ringedSpaceModuleComplexDualCoevaluation`. After applying the tensor-to-endomorphism
-- isomorphism, the composite becomes the identity, which is exactly the first triangle identity.
/-- The coevaluation and evaluation maps satisfy the first triangle identity. -/
theorem ringedSpaceModuleComplexDual_coevaluation_evaluation
    {F : CpxX}
    [IsIso (ringedSpaceModuleComplexDualTensorToEnd F)] :
    ((ihom F).obj (𝟙_ CpxX)) ◁ ringedSpaceModuleComplexDualCoevaluation F ≫
        (α_ _ _ _).inv ≫
        ringedSpaceModuleComplexDualEvaluation F ▷ (ihom F).obj (𝟙_ CpxX) =
      (ρ_ ((ihom F).obj (𝟙_ CpxX))).hom ≫
        (λ_ ((ihom F).obj (𝟙_ CpxX))).inv := sorry

-- Proof sketch: similarly, transport the identity of `F^\bullet` across the same
-- tensor-to-endomorphism isomorphism. The defining property of
-- `ringedSpaceModuleComplexDualCoevaluation` then yields the second triangle identity.
/-- The coevaluation and evaluation maps satisfy the second triangle identity. -/
theorem ringedSpaceModuleComplexDual_evaluation_coevaluation
    {F : CpxX}
    [IsIso (ringedSpaceModuleComplexDualTensorToEnd F)] :
    ringedSpaceModuleComplexDualCoevaluation F ▷ F ≫
        (α_ _ _ _).hom ≫
        F ◁ ringedSpaceModuleComplexDualEvaluation F =
      (λ_ F).hom ≫ (ρ_ F).inv := sorry

/-- The internal-Hom dual, together with the canonical coevaluation and evaluation maps, gives a
chosen left dual whenever the tensor-to-endomorphism comparison is an isomorphism. -/
@[reducible] private noncomputable def ringedSpaceModuleComplexDualExactPairingOfIsIso
    (F : CpxX)
    [IsIso (ringedSpaceModuleComplexDualTensorToEnd F)] :
    ExactPairing ((ihom F).obj (𝟙_ CpxX)) F :=
  letI : ExactPairing F ((ihom F).obj (𝟙_ CpxX)) :=
    { coevaluation' := ringedSpaceModuleComplexDualCoevaluation F
      evaluation' := ringedSpaceModuleComplexDualEvaluation F
      coevaluation_evaluation' := ringedSpaceModuleComplexDual_coevaluation_evaluation
      evaluation_coevaluation' := ringedSpaceModuleComplexDual_evaluation_coevaluation }
  BraidedCategory.exactPairing_swap F ((ihom F).obj (𝟙_ CpxX))

/-- Example 20.50.2: if `\mathcal F^\bullet` is locally strictly perfect on the ringed space
`(X, \mathcal O_X)`, then the internal-Hom dual
`\mathcal G^\bullet = \mathcal H\!\mathit{om}^\bullet(\mathcal F^\bullet, \mathcal O_X)`,
together with the canonical coevaluation and evaluation morphisms
`\eta : \mathcal O_X \to \mathrm{Tot}(\mathcal F^\bullet \otimes \mathcal G^\bullet)` and
`\epsilon : \mathrm{Tot}(\mathcal G^\bullet \otimes \mathcal F^\bullet) \to \mathcal O_X`,
forms a left dual of `\mathcal F^\bullet`. In Lean this left-dual datum is packaged by
`CategoryTheory.ExactPairing`. -/
noncomputable abbrev ringedSpaceModuleComplexDualExactPairing
    {F : CpxX} (hF : CochainComplex.IsLocallyStrictlyPerfect F) :
    ExactPairing ((ihom F).obj (𝟙_ CpxX)) F :=
  letI : IsIso (ringedSpaceModuleComplexDualTensorToEnd F) :=
    ringedSpaceModuleComplexDualTensorToEnd_isIso_of_isLocallyStrictlyPerfect hF
  ringedSpaceModuleComplexDualExactPairingOfIsIso F

end Duality

end AlgebraicGeometry.RingedSpace
