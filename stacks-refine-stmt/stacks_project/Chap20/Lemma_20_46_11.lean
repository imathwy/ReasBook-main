import Mathlib
import stacks_project.Chap20.Lemma_20_41_8
import stacks_project.Chap21.Lemma_21_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

set_option checkBinderAnnotations false
set_option maxHeartbeats 1000000

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Abelian.toPreadditive

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.46.11:
- primary domain: derived internal Hom for complexes of `\mathcal O_X`-modules on a ringed space,
  computed by the canonical internal-Hom complex under boundedness and finite-free-retract
  hypotheses;
- sampled owner declarations:
  `(RingedSpace.Modules X)`,
  `moduleComplexInternalHom`,
  `moduleComplexInternalHom_isKInjective_of_isKFlat`,
  `finiteFreeRetractModuleProperty`;
- best owner abstraction: the Chapter 20 owner
  `AlgebraicGeometry.RingedSpace.moduleComplexInternalHom`, already introduced for the ringed-space
  internal-Hom complex in Lemma 20.41.8, together with the generic finite-free-retract owner
  `finiteFreeRetractModuleProperty X.sheaf` for the repeated source hypothesis on the terms of
  `E`;
- primitive data: the ringed space `X`, the complexes `E` and `F`, the bounded-below hypothesis on
  `F`, the bounded-above hypothesis on `E`, and the degreewise direct-summand-of-finite-free
  condition on the terms of `E`;
- derived API: the derived-category object represented by `moduleComplexInternalHom E F`.

Source/core/bridge triage:
- `source-facing`: Lemma 20.46.11 itself, whose extra boundedness hypotheses are genuine source
  content and are not already packaged by the strict-perfect owner;
- `core/canonical`: `(RingedSpace.Modules X)`, `moduleComplexInternalHom`, and
  `finiteFreeRetractModuleProperty`;
- `bridge/view`: the pointwise specialization of `finiteFreeRetractModuleProperty X.sheaf` to the
  terms `E.X n`, recovering the explicit retract-of-finite-free formulation from the owner
  property.

This file should therefore keep only the source-facing hypothesis layer and directly reuse the
existing internal-Hom owner, rather than redeclare the internal-Hom complex and its componentwise
machinery a second time. -/

section

variable {X : RingedSpace.{u}}
variable [Abelian (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasProducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ K L : CochainComplex (RingedSpace.Modules X) ℤ,
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSpace.Modules X))]
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "ModX" => (RingedSpace.Modules X)
local notation "CpxX" => CochainComplex ModX ℤ
local notation "DModX" => DerivedCategory ModX

-- Proof sketch: choose a bounded-below K-injective replacement `F ⟶ I`. Because `E` is bounded
-- above and each `E^n` is a retract of a finite free module sheaf, only finitely many terms
-- contribute in each total degree, so the canonical internal-Hom complex from Lemma `20.41.8`
-- reduces to the finite direct-sum formula from the text. The same strict-perfect argument used
-- degreewise then shows that `moduleComplexInternalHom E F ⟶ moduleComplexInternalHom E I` is a
-- quasi-isomorphism, hence this canonical internal-Hom complex already represents the derived
-- internal Hom.
/-- Lemma 20.46.11: if `\mathcal F^\bullet` is bounded below, `\mathcal E^\bullet` is bounded
above, and each term `\mathcal E^n` is a retract of a finite free `\mathcal O_X`-module, then the
derived internal Hom `R\mathcal H\!\mathit{om}(\mathcal E^\bullet, \mathcal F^\bullet)` is
represented by the canonical internal-Hom complex `moduleComplexInternalHom E F`. Under these
hypotheses, its degree-`n` term is the finite direct sum
`\bigoplus_{n = p + q}\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal E^{-q}, \mathcal F^p)`
described in Section 20.42. -/
theorem derivedInternalHom_iso_moduleComplexInternalHom_of_boundedBelow_of_boundedAbove_termwise_finiteFreeRetract
    (E F : CpxX)
    (hF_boundedBelow : ∃ a : ℤ, F.IsStrictlyGE a)
    (hE_boundedAbove : ∃ b : ℤ, E.IsStrictlyLE b)
    (hE_termwise_finiteFreeRetract :
      ∀ n : ℤ, ∃ I : Type u, Finite I ∧
        Nonempty (Retract (E.X n) (SheafOfModules.free I : ModX))) :
    IsIsomorphic
      ((((DerivedCategory.Q : CpxX ⥤ DModX)).obj
        ((moduleComplexInternalHom : CpxX → CpxX → CpxX) E F)) : DModX)
      ((ihom (((DerivedCategory.Q : CpxX ⥤ DModX)).obj E)).obj
        (((DerivedCategory.Q : CpxX ⥤ DModX)).obj F)) := sorry

end

end AlgebraicGeometry.RingedSpace
