import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.Lemma_20_17_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Remark 20.17.2:
- primary domain: bounded-below derived base change for sheaves of modules on ringed spaces in a
  flat cartesian square;
- sampled owner declarations:
  `RingedSpace.IsBoundedBelowDerivedBaseChangeMap`,
  `RingedSpace.IsBoundedBelowFlatBaseChangeMap`,
  `RingedSpace.existsUnique_boundedBelowDerivedBaseChangeMap`,
  `RingedSpace.existsUnique_boundedBelowFlatBaseChangeMap`,
  `CategoryTheory.CommSq`,
  `RingedSpace.Hom.IsFlat`;
- best owner abstraction:
  `source-facing`: the flat-target spelling of the defining comparison predicate and the
    corresponding existence-and-uniqueness theorem for a bounded-below base-change morphism
    `Lg^* Rf_* ℱ ⟶ R(f')_* (g')^* ℱ`;
  `core/canonical`: `RingedSpace.IsBoundedBelowDerivedBaseChangeMap`;
  `bridge/view`: the flat-target aliases
    `RingedSpace.IsBoundedBelowFlatBaseChangeMap` and
    `RingedSpace.existsUnique_boundedBelowFlatBaseChangeMap`.

This remark adds no new owner beyond Lemma `20.17.1`; the correct refined surface is therefore a
direct recall of the source-facing flat-target predicate together with its
existence-and-uniqueness theorem. -/

/- Remark 20.17.2: in the bounded-below flat base-change setting of Lemma 20.17.1, the defining
comparison equation is `RingedSpace.IsBoundedBelowFlatBaseChangeMap`, and the corresponding
existence-and-uniqueness statement is
`RingedSpace.existsUnique_boundedBelowFlatBaseChangeMap`. -/
recall RingedSpace.IsBoundedBelowFlatBaseChangeMap
recall RingedSpace.existsUnique_boundedBelowFlatBaseChangeMap

end AlgebraicGeometry.RingedSpace
