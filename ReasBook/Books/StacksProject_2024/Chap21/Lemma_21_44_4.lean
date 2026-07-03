import Mathlib
import stacks_project.Chap21.Definition_21_44_1
import stacks_project.Chap21.Lemma_21_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

/-
Domain-style sampling for Lemma 21.44.4:
- primary domain: strictly perfect cochain complexes of module sheaves on ringed sites, and their
  inverse-image functors;
- inspected owner declarations:
  `SheafOfModules.RingedSite.RingedSiteModules`,
  `SheafOfModules.RingedSite.pullbackFunctor`,
  `CochainComplex.IsStrictlyPerfect`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullback_isFiniteFree`;
- best owner abstraction: the public owner layer is
  `RingedSiteModules`, `CochainComplex.IsStrictlyPerfect`, and the chapter owner
  `pullbackFunctor`; the pullback side should be expressed through that owner rather than through
  a parallel local structure-map wrapper;
- primitive data: the site-presented structure morphism of `RingCat`-valued sheaves induced by
  `φ`;
- derived API: the pullback preservation statement for strict perfectness.

Source/core/bridge triage:
- `source-facing`: pullback preserves strictly perfect complexes for the site-presented morphism;
- `core/canonical`: `RingedSiteModules`, `CochainComplex.IsStrictlyPerfect`,
  `ringedSiteUnderlyingStructureMap`, and `pullbackFunctor`;
- `bridge/view`: the induced `RingCat`-valued structure morphism attached to `φ`, used through
  `ringedSiteUnderlyingStructureMap`.
-/
variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify JC AddCommGrpCat]
variable [JC.WEqualsLocallyBijective AddCommGrpCat]
variable [HasWeakSheafify JD AddCommGrpCat]
variable [JD.WEqualsLocallyBijective AddCommGrpCat]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪D : Sheaf JC CommRingCat.{max u v}} {𝒪C : Sheaf JD CommRingCat.{max u v}}
variable (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} JC JD).obj 𝒪C)
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
variable [(pullbackFunctor F φ).Additive]

-- Proof sketch: unpack `CochainComplex.IsStrictlyPerfect`. The pullback functor on module sheaves
-- is additive, so the induced functor on cochain complexes preserves strict lower and upper
-- bounds. In each degree, Lemma `18.17.2` shows that pullback carries finite free modules to
-- finite free modules, and functoriality sends a retract presentation of `E.X i` to a retract
-- presentation of the pulled-back term.
/-- Lemma 21.44.4: for a site-presented morphism of ringed topoi determined by `φ`, if
`\mathcal F^\bullet` is a strictly perfect complex of `\mathcal O_\mathcal D`-modules, then the
pulled-back complex `f^*\mathcal F^\bullet` is a strictly perfect complex of
`\mathcal O_\mathcal C`-modules. -/
theorem cochainComplex_isStrictlyPerfect_pullback
    (E : CochainComplex (RingedSiteModules JC 𝒪D) ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    CochainComplex.IsStrictlyPerfect
      (((pullbackFunctor F φ).mapHomologicalComplex (up ℤ)).obj E) := sorry

end

end SheafOfModules.RingedSite
