import Mathlib
import Mathlib.CategoryTheory.Retract
import stacks_project.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Definition 21.44.1:
- primary domain: strictly perfect cochain complexes of sheaves of modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsStrictlyGE`,
  `CochainComplex.IsStrictlyLE`,
  `SheafOfModules.free`;
- best owner abstraction: the source-facing predicate
  `CochainComplex.IsStrictlyPerfect` on the chapter vocabulary
  `RingedSiteModules J 𝒪`;
- primitive data: the ambient module category on the ringed site and, in each degree, a retract
  presentation by a finite free module;
- derived API: localized specializations on `(J.over U, 𝒪.over U)` and later local/derived
  perfectness notions built from this owner.

Source/core/bridge triage:
- `source-facing`: strict perfectness of a cochain complex of `𝒪`-modules;
- `core/canonical`: the ambient module category owner from Chapter 18 together with the single
  predicate below;
- `bridge/view`: localized and derived variants in downstream files.

There is no earlier project owner for strict perfectness itself. The duplicate wheel to remove here
is the repeated local rebinding of the ambient module category, so this file exposes the stable
chapter vocabulary below for downstream reuse. -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on a ringed site. -/
abbrev RingedSiteModules (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  ringedSiteModuleCategory J 𝒪

/-- The category `\mathrm{Mod}(\mathcal O_U)` on the localized ringed site
`(\mathcal C/U, J.over U, \mathcal O_U)`. -/
abbrev LocalizedRingedSiteModules
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C) :=
  RingedSiteModules (J.over U) (𝒪.over U)

local notation "Mod" => RingedSiteModules J 𝒪

/-- Definition 21.44.1: a complex of `\mathcal O`-modules on a ringed site `(\mathcal C,
\mathcal O)` is strictly perfect if it is zero in all but finitely many degrees and each term is a
direct summand of a finite free `\mathcal O`-module. -/
def CochainComplex.IsStrictlyPerfect
    (E : CochainComplex Mod ℤ) : Prop :=
  (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
    ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
      Nonempty (Retract (E.X i) (SheafOfModules.free I : Mod))

-- Proof sketch: unfold `CochainComplex.IsStrictlyPerfect`; for cochain complexes indexed by `ℤ`,
-- vanishing outside finitely many degrees is equivalent to simultaneous lower and upper bounds,
-- and the second clause is exactly the termwise direct-summand condition from the definition.
/-- Unfolding `IsStrictlyPerfect` gives boundedness together with the requirement that each degree
term is a retract of a finite free `\mathcal O`-module. -/
theorem cochainComplex_isStrictlyPerfect_iff
    (E : CochainComplex Mod ℤ) :
    CochainComplex.IsStrictlyPerfect E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
          Nonempty (Retract (E.X i) (SheafOfModules.free I : Mod)) :=
  Iff.rfl

end

end SheafOfModules.RingedSite
