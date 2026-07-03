import Mathlib
import stacks_project.Chap12.Definition_12_31_2
import stacks_project.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

namespace SequentialInverseSystem

/- Domain-style sampling for Lemma 15.87.14:
- primary domain: sequential inverse systems of abelian groups, stagewise countable coproducts,
  and the degree-one derived inverse limit;
- sampled owner declarations:
  `SequentialInverseSystem`,
  `SequentialInverseSystem.IsMittagLeffler`,
  `SequentialInverseSystem.countableCoproduct`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.Functor.const`,
  `CategoryTheory.Limits.colim`;
- best owner abstraction: the stagewise countable-coproduct tower is the generic owner
  `SequentialInverseSystem.countableCoproduct` on inverse systems in a category with countable
  coproducts, while the degree-one obstruction is the chapter owner
  `SequentialInverseSystem.firstDerivedLimit`; the Emmanouil criterion is the source-facing
  specialization of those owners to `AddCommGrpCat`;
- primitive-vs-derived split: the primitive data are only an inverse system `A`; the
  countable-coproduct tower and the two `R^1 \!\varprojlim` objects are derived API on that
  owner.

Source/core/bridge triage:
- `source-facing`: Emmanouil's two-clause criterion for one inverse system `A`;
- `core/canonical`: the owners `SequentialInverseSystem`, `SequentialInverseSystem.countableCoproduct`,
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: the countable direct-sum wording in abelian groups for the generic stagewise
  countable-coproduct owner.
-/

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

-- Proof sketch: one direction uses Lemma `15.87.1` to deduce the vanishing of `R^1 lim` from the
-- Mittag-Leffler condition, both for `A` and for the countable direct-sum tower. For the converse,
-- Emmanouil's argument constructs from a failure of the Mittag-Leffler condition a nonzero class
-- in `R^1 lim` of the countable direct-sum tower, forcing the conjunction clause to fail.
/-- Lemma 15.87.14 (Emmanouil): for a sequential inverse system `A` of abelian groups, the
following are equivalent:
`A` is Mittag-Leffler, and both `R^1 \!\varprojlim A` and
`R^1 \!\varprojlim (A.countableCoproduct)` vanish, where `A.countableCoproduct` is the stagewise
countable direct-sum tower. -/
theorem isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
    (A : AbSeq) :
    A.IsMittagLeffler ↔ IsZero A.firstDerivedLimit ∧ IsZero A.countableCoproduct.firstDerivedLimit :=
  sorry

end SequentialInverseSystem

end CategoryTheory
