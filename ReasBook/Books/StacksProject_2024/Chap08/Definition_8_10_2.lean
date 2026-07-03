import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap08.Lemma_8_10_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/- Domain-style sampling for Definition 8.10.2:
- primary domain: site structures presented through `Precoverage` on the total category of a
  fibred category;
- sampled owner declarations:
  `CategoryTheory.Precoverage`,
  `CategoryTheory.Precoverage.HasIsos`,
  `CategoryTheory.Precoverage.HasPullbacks`,
  `CategoryTheory.Precoverage.IsStableUnderBaseChange`,
  `CategoryTheory.Precoverage.IsStableUnderComposition`,
  `stronglyCartesianLiftPrecoverage`,
  `CategoryTheory.Functor.IsFibered`;
- best owner abstraction: the source-facing item is the inherited `Precoverage` itself, while the
  site axioms remain derived instance-level API on that owner.

Source/core/bridge triage:
- `source-facing`: `stronglyCartesianLiftPrecoverage J p`;
- `core/canonical`: the `Precoverage` owner together with its site-axiom typeclasses;
- `bridge/view`: direct typeclass inference for the four site axioms on
  `stronglyCartesianLiftPrecoverage J p` under the hypotheses of Lemma 8.10.1.

Primitive-vs-derived split:
- primitive data: the inherited covering families owned by `stronglyCartesianLiftPrecoverage`;
- derived API: the four canonical site-axiom instances on the inherited precoverage once the base
  precoverage is a site and `p` is fibred. -/

/- Definition 8.10.2: for a site structure `J` on `C` and a fibred category `p : S ⥤ C`, the
site structure on `S` inherited from `C` is the precoverage
`stronglyCartesianLiftPrecoverage J p` constructed in Lemma 8.10.1. -/
recall stronglyCartesianLiftPrecoverage

variable (J : Precoverage C) (p : S ⥤ C)
variable [J.HasIsos] [J.HasPullbacks] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition]
variable [p.IsFibered]

/- Companion recall: under the hypotheses of Lemma 8.10.1, the inherited precoverage carries the
four canonical site axioms by direct instance inference. -/
#synth (stronglyCartesianLiftPrecoverage J p).HasIsos
#synth (stronglyCartesianLiftPrecoverage J p).HasPullbacks
#synth (stronglyCartesianLiftPrecoverage J p).IsStableUnderBaseChange
#synth (stronglyCartesianLiftPrecoverage J p).IsStableUnderComposition

end

end CategoryTheory
