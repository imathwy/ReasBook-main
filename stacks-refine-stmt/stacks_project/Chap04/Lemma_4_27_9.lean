import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

open MorphismProperty Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

/- Domain-style sampling for Lemma 4.27.9:
- primary domain: localization of morphism properties and finite-colimit preservation;
- inspected owner declarations:
  `Functor.IsLocalization`,
  `Functor.q_isLocalization`,
  `Functor.IsLocalization.pi`,
  `Localization.equivalenceFromModel`,
  `Localization.qCompEquivalenceFromModelFunctorIso`;
- best owner abstraction: `Functor.IsLocalization`, with `PreservesFiniteColimits L` as derived API
  for a localization functor `L`, transported from the canonical model `W.Q` along the owner
  equivalence `equivalenceFromModel`.

Primitive-vs-derived split:
- primitive data: the morphism property `W` and a localization functor `L`;
- derived API: the instance `PreservesFiniteColimits L`, transported from the canonical owner
  functor `W.Q`.

Source/core/bridge triage:
- source-facing: the instance `PreservesFiniteColimits W.Q`;
- core/canonical: `Functor.IsLocalization`;
- bridge/view: `Functor.IsLocalization.preservesFiniteColimits`, which transports the owner
  instance along `equivalenceFromModel` and `qCompEquivalenceFromModelFunctorIso`. -/

-- Proof sketch: for each object `Y`, represent `Hom_{W.Localization}(W.Q.obj -, W.Q.obj Y)` as a
-- filtered colimit of representable functors using `4.27.7.1`; then filtered colimits commute
-- with finite limits in `Type`, so these hom-functors send finite colimits in `C` to limits, which
-- is exactly the universal property that `W.Q` preserves finite colimits.
/-- Lemma 4.27.9: if `W` is a left multiplicative system in `C`, then the localization functor
`W.Q : C ⥤ W.Localization` commutes with finite colimits. -/
instance localization_Q_preservesFiniteColimits [W.HasLeftCalculusOfFractions] :
    PreservesFiniteColimits W.Q := sorry

namespace Functor.IsLocalization

-- Proof sketch: transport finite-colimit preservation from the canonical localization functor
-- `W.Q` across the equivalence `equivalenceFromModel L W`, using the natural isomorphism
-- `qCompEquivalenceFromModelFunctorIso L W`.
/-- Any localization functor of a left multiplicative system is canonically identified with
`W.Q`, so it also preserves finite colimits. -/
theorem preservesFiniteColimits
    {D : Type w} [Category.{v} D] (L : C ⥤ D) [W.HasLeftCalculusOfFractions]
    [L.IsLocalization W] : PreservesFiniteColimits L := sorry

end Functor.IsLocalization

end CategoryTheory
