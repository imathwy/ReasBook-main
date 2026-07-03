import Mathlib
import stacks_project.Chap21.Lemma_21_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

set_option checkBinderAnnotations false

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type} [Category C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat}
variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [HasProducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]
variable [MonoidalClosed (DerivedCategory (ringedSiteModuleCategory J 𝒪))]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex Mod ℤ
local notation "DMod" => DerivedCategory Mod

local instance instPreadditiveMod : Preadditive Mod :=
  (inferInstance : Abelian Mod).toPreadditive

/- Domain-style sampling for Lemma 21.44.10:
- primary domain: derived internal Hom for complexes of `\mathcal O`-modules on a ringed site
  under boundedness and termwise finite-free-retract hypotheses;
- sampled owner declarations:
  `ringedSiteModuleComplexInternalHom`,
  `DerivedCategory.Q.obj`,
  `CochainComplex.IsStrictlyGE`,
  `CochainComplex.IsStrictlyLE`;
- best owner abstraction: the Chapter 21 internal-Hom owner
  `ringedSiteModuleComplexInternalHom`; the bounded-above variant here keeps the degreewise
  retract-of-finite-free hypothesis as primitive source data rather than repackaging it;
- primitive data: the complexes `E`, `F`, the bounded-below hypothesis on `F`, the bounded-above
  hypothesis on `E`, and the pointwise retract-of-finite-free hypothesis on each `E.X i`;
- derived API: the represented derived internal-Hom object in `DerivedCategory Mod`.

Source/core/bridge triage:
- `source-facing`: Lemma 21.44.10, whose bounded-below and bounded-above hypotheses are genuine
  source content;
- `core/canonical`: `ringedSiteModuleComplexInternalHom` and `DerivedCategory.Q.obj`;
- `bridge/view`: the explicit degreewise retract-of-finite-free hypothesis, kept source-facing
  instead of being repackaged through a local strict-perfect wrapper.

This file therefore keeps the source-facing boundedness statement, but reuses the owner property
for the internal-Hom complex instead of introducing a second local representation wrapper. -/

-- Proof sketch: boundedness of `F` from below and boundedness of `E` from above, together with
-- the termwise finite-free retract hypothesis, imply that `E` is locally represented by a bounded
-- complex of finite free modules in the range relevant for the internal-Hom total degree. This is
-- exactly the bounded-above variant of the strict-perfect argument from Lemma `21.44.9`, so the
-- canonical internal-Hom complex still computes the derived internal Hom.
/-- Lemma 21.44.10: for complexes `\mathcal E^\bullet` and `\mathcal F^\bullet` of
`\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, if
`\mathcal F^\bullet` is bounded below, `\mathcal E^\bullet` is bounded above, and each term of
`\mathcal E^\bullet` is a direct summand of a finite free `\mathcal O`-module, then the derived
internal Hom `R\mathcal H\!\mathit{om}(\mathcal E^\bullet, \mathcal F^\bullet)` is represented by
the canonical internal-Hom complex `ringedSiteModuleComplexInternalHom E F`. Under these
hypotheses, the degreewise products in this complex are finite and match the textbook direct-sum
formula `\bigoplus_{n = p + q}\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal E^{-q}, \mathcal F^p)`.
-/
theorem ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_boundedBelow_of_boundedAbove_of_termwise_finiteFreeRetract
    (E F : CpxO)
    (hF_boundedBelow : ∃ a : ℤ, F.IsStrictlyGE a)
    (hE_boundedAbove : ∃ b : ℤ, E.IsStrictlyLE b)
    (hE_termwise_finiteFreeRetract :
      ∀ i : ℤ, ∃ I : Type, Finite I ∧
        Nonempty (Retract (E.X i) (SheafOfModules.free I : Mod))) :
    IsIsomorphic
      ((((DerivedCategory.Q : CpxO ⥤ DMod)).obj
        (show CpxO from ringedSiteModuleComplexInternalHom E F)) : DMod)
      ((ihom (((DerivedCategory.Q : CpxO ⥤ DMod)).obj E)).obj
        (((DerivedCategory.Q : CpxO ⥤ DMod)).obj F)) := by
  sorry

end

end SheafOfModules.RingedSite
