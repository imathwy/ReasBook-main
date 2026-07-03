import Mathlib
import stacks_project.Chap18.Definition_18_31_1
import stacks_project.Chap18.Remark_18_27_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 18.31.4:
- primary domain: pullback of internal-Hom sheaves along a flat morphism of ringed sites;
- sampled owner declarations:
  `CategoryTheory.expComparison`,
  `RingedSite.Hom.pullbackInternalHomComparison`,
  `RingedSite.Hom.(^*)`,
  `RingedSite.Hom.IsFlat`,
  `SheafOfModules.IsFinitePresentation`;
- best owner abstraction: the ambient owner is the pullback functor `(f^*)`; when the stronger
  Cartesian-closed comparison owner `CategoryTheory.expComparison` is available, the comparison of
  Remark 18.27.3 is its ringed-site bridge component. The source-facing theorem remains stated for
  that bridge because the generic mathlib owner currently carries extra ambient assumptions not
  present in the textbook statement;
- primitive data: a morphism of ringed sites `f` and module sheaves `ℱ 𝒢`;
- derived API: the statement that the source-facing comparison morphism is an isomorphism when
  `ℱ` is finitely presented and `f` is flat.

Source/core/bridge triage:
- `source-facing`: the isomorphism statement for the comparison morphism;
- `core/canonical`: `RingedSite.Hom.(^*)`, `RingedSite.Hom.IsFlat`,
  `SheafOfModules.IsFinitePresentation`, and, under the stronger generic comparison hypotheses,
  `CategoryTheory.expComparison`;
- `bridge/view`: `RingedSite.Hom.pullbackInternalHomComparison`. -/

variable {X Y : RingedSite} (f : X ⟶ Y)
variable [MonoidalCategory (SheafOfModules Y.structureSheaf)]
variable [MonoidalClosed (SheafOfModules Y.structureSheaf)]
variable [MonoidalCategory (SheafOfModules X.structureSheaf)]
variable [MonoidalClosed (SheafOfModules X.structureSheaf)]
variable [(f^*).Monoidal]

-- Proof sketch: the statement is local on `X`, so after localizing one may choose a finite free
-- presentation of `ℱ`. Flatness makes pullback exact, internal Hom is left exact in the first
-- variable, and for finite free sources the comparison map is visibly an isomorphism. Applying
-- these facts to the presentation diagram and using the five lemma gives the result.
--
-- API note: `pullbackInternalHomComparison` is the source-facing bridge/view of the ambient
-- pullback comparison; the generic owner `CategoryTheory.expComparison` in mathlib currently
-- requires additional Cartesian-closed comparison data that is not part of this textbook-facing
-- statement.
/-- Lemma 18.31.4: for a flat morphism of ringed sites
`f : (\mathcal C, \mathcal O_\mathcal C) \to (\mathcal D, \mathcal O_\mathcal D)` and
`\mathcal O_\mathcal D`-modules `\mathcal F`, `\mathcal G`, if `\mathcal F` is finitely
presented, then the canonical map of Remark 18.27.3
`f^*\mathcal H\!\mathit{om}_{\mathcal O_\mathcal D}(\mathcal F, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_\mathcal C}(f^*\mathcal F, f^*\mathcal G)`
is an isomorphism. -/
theorem isIso_pullbackInternalHomComparison
    (ℱ 𝒢 : SheafOfModules Y.structureSheaf) [ℱ.IsFinitePresentation] [IsFlat f] :
    IsIso (pullbackInternalHomComparison f ℱ 𝒢) := sorry

end RingedSite.Hom
