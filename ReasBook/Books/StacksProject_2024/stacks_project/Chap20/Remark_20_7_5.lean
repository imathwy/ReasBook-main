import StacksProject_2024.Chap20.Lemma_20_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Remark 20.7.5:
- primary domain: sheaf cohomology of `𝒪_X`-modules on the opens site of a ringed space,
  the sheafification of the resulting cohomology presheaves, and the identity-morphism higher
  direct image that canonically realizes that sheafification;
- sampled owner declarations:
  `Modules`,
  `moduleUnderlyingSheaf`,
  `Sheaf.cohomologyPresheaf`,
  `presheafToSheaf`,
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`;
- best owner abstraction: the ringed-space owner category `X.Modules`, together with the canonical
  Chapter 20 bridge `moduleUnderlyingSheaf X` to sheaves of abelian groups and the identity-case
  specialization of
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`;
- primitive data: the ringed space `X`, the module `F : X.Modules`, and the degree `p`;
- derived API: the underlying additive sheaf
  `((moduleUnderlyingSheaf X).obj F)`, its cohomology presheaf, and the identity higher direct
  image `R^{p}_[𝟙 X](F)`.

Source/core/bridge triage:
- `source-facing`: the vanishing of the sheafification of the positive cohomology presheaf
  `U ↦ H^p(U, 𝓕)`;
- `core/canonical`: `X.Modules`, `moduleUnderlyingSheaf`, and `R^{p}_[𝟙 X](F)`;
- `bridge/view`: the identity-morphism specialization of
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`.

This remark adds no new owner-level data, so its public statement should use the canonical
ringed-space bridge `moduleUnderlyingSheaf X` rather than bypassing it with the raw composite
`SheafOfModules.toSheaf X.ringCatSheaf`; the reusable companion API should also expose the
identity higher-direct-image owner that this sheafification computes. -/

section

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions X.Modules]

local notation "JX" => Opens.grothendieckTopology X.carrier
local notation "AbSheaf" => moduleUnderlyingSheaf X

omit [HasSheafify JX AddCommGrpCat.{u}] [HasExt (Sheaf JX AddCommGrpCat.{u})] in
/-- Canonical owner companion to Remark 20.7.5: the positive identity higher direct image of an
`𝒪_X`-module is zero. -/
theorem identityHigherDirectImageModule_isZero
    (F : X.Modules) {p : ℕ} (hp : 0 < p) :
    IsZero (R^{p}_[(𝟙 X)](F)) := by
  cases p with
  | zero =>
      cases Nat.lt_asymm hp hp
  | succ n =>
      let I : InjectiveResolution F := injectiveResolution F
      let K :=
        ((((𝟙 X) _*).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      let e :
          R^{n + 1}_[(𝟙 X)](F) ≅
            ((HomologicalComplex.homologyFunctor
              X.Modules (ComplexShape.up ℕ) (n + 1)).obj K) :=
        I.isoRightDerivedObj ((𝟙 X) _*) (n + 1)
      have hExactAt : K.ExactAt (n + 1) := by
        simpa [K, I, HomologicalComplex.exactAt_iff, HomologicalComplex.sc,
          HomologicalComplex.shortComplexFunctor] using I.exact_succ n
      have hHomology : IsZero (K.homology (n + 1)) := by
        rw [← HomologicalComplex.exactAt_iff_isZero_homology]
        exact hExactAt
      exact e.isZero_iff.2 <| by
        simpa [K] using hHomology

/-- Typeclass form of `identityHigherDirectImageModule_isZero`: positive identity higher direct
images vanish. -/
instance instIsZeroIdentityHigherDirectImageModule
    (F : X.Modules) (p : ℕ) [hp : Fact (0 < p)] :
    IsZero (R^{p}_[(𝟙 X)](F)) :=
  identityHigherDirectImageModule_isZero F hp.out

-- Proof sketch: the sheafification functor on presheaves of `𝒪_X`-modules is exact and
-- the derived-functor description from Lemma `20.11.4` identifies the higher right derived
-- functors of the inclusion with the cohomology presheaves. This yields the restatement of Lemma
-- `20.7.2` used in the remark: the sheafification of the positive cohomology presheaf is zero.
/-- Remark 20.7.5: for a ringed space `(X, 𝒪_X)`, the sheafification of the positive cohomology
presheaf `U ↦ H^p(U, 𝓕)` of an `𝒪_X`-module vanishes; this is
the derived-functor reformulation underlying the alternative proof of Lemma `20.7.2`. -/
@[stacks 03BA]
theorem positive_cohomologyPresheaf_sheafification_isZero
    (F : X.Modules) {p : ℕ} (hp : 0 < p) :
    IsZero
      ((presheafToSheaf JX AddCommGrpCat.{u}).obj
        (((AbSheaf).obj F).cohomologyPresheaf p)) := by
  rcases
      higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology
        (𝟙 X) F p with
    ⟨e⟩
  exact e.isZero_iff.1 <| (AbSheaf).map_isZero <| identityHigherDirectImageModule_isZero F hp

end

end AlgebraicGeometry.RingedSpace
