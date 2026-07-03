import Mathlib
import StacksProject_2024.Chap04.Remark_4_22_7
import StacksProject_2024.Chap15.Lemma_15_87_14_Emmanouil

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat
local instance : OfNat AddCommGrpCat 0 := ⟨⊥_ AddCommGrpCat⟩

namespace CategoryTheory

namespace SequentialInverseSystem

/- Domain-style sampling for Lemma 15.87.16:
- primary domain: sequential inverse systems of abelian groups, their vanishing as pro-objects,
  inverse limits, and the first derived inverse limit;
- sampled owner declarations:
  `CategoryTheory.HasProObjectValue`,
  `SequentialInverseSystem.IsMittagLeffler`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `countableCoproduct`,
  `isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero`,
  `CategoryTheory.limit`;
- best owner abstraction: the canonical owner for "the tower is zero as a pro-object" is
  `HasProObjectValue A (0 : AddCommGrpCat)`; the remaining owners are `limit A`,
  `firstDerivedLimit A`, and the stagewise countable coproduct tower `A.countableCoproduct`;
- primitive-vs-derived split:
  primitive data are only the inverse system `A`;
  `A.transitionMap`, the eventual-zero-image condition, `limit A`, `firstDerivedLimit A`, and the
  countable-coproduct tower are derived API, so the main theorem should use
  `HasProObjectValue A (0 : AddCommGrpCat)` directly and keep the eventual-zero-image formulation
  only as a bridge.

Source/core/bridge triage:
- `source-facing`: the eventual-zero-image criterion on transition maps;
- `core/canonical`: `HasProObjectValue`, `limit`, `firstDerivedLimit`,
  `countableCoproduct`, and `IsMittagLeffler`;
- `bridge/view`: the equivalence below between
  `HasProObjectValue A (0 : AddCommGrpCat)` and the eventual-zero-image condition, followed by the
  vanishing criterion for `A` and its stagewise countable coproduct tower. -/

-- Proof sketch: if the pro-object defined by `A` is corepresented by `0`, then every map from a
-- later stage to a fixed stage factors through the zero cone after passing far enough out, so the
-- image of a sufficiently late transition map is zero. Conversely, if all transition-map images
-- eventually vanish at each stage, then the associated pro-object is eventually zero and hence is
-- corepresented by the zero object.
/-- A sequential inverse system of abelian groups has pro-object value `0` if and only if, for
every fixed stage, the image of a sufficiently far transition map into that stage is zero. -/
theorem hasProObjectValue_zero_iff_eventually_zero_image
    (A : AbSeq) :
    HasProObjectValue A (0 : AddCommGrpCat) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m,
        imageSubobject (A.transitionMap hnm) = ⊥ := sorry

-- Proof sketch: if `A` is zero as a pro-object, then the eventual-zero-image condition forces
-- the stabilized images at every stage to be zero; this gives `lim A = 0`, and the stabilization
-- itself is exactly the Mittag-Leffler condition. Conversely, if `A` is Mittag-Leffler and
-- `lim A = 0`, then the stable images inside each stage are nonempty and have zero inverse limit,
-- hence are zero, which recovers the eventual-zero-image criterion.
/-- The zero pro-object criterion in owner form: a sequential inverse system of abelian groups is
zero as a pro-object exactly when `\varprojlim A` vanishes and `A` is Mittag-Leffler. -/
theorem hasProObjectValue_zero_iff_limit_isZero_and_isMittagLeffler
    (A : AbSeq) :
    HasProObjectValue A (0 : AddCommGrpCat) ↔
      IsZero (limit A) ∧ A.IsMittagLeffler := sorry

/-- Lemma 15.87.16: a sequential inverse system of abelian groups is zero as a pro-object if and
only if `\varprojlim A`, `R^1 \!\varprojlim A`, and
`R^1 \!\varprojlim (A.countableCoproduct)` vanish, where `A.countableCoproduct` is the inverse
system obtained by taking countable direct sums stagewise. -/
theorem hasProObjectValue_zero_iff_limit_and_firstDerivedLimit_isZero_and_countableCoproduct
    (A : AbSeq) :
    HasProObjectValue A (0 : AddCommGrpCat) ↔
      IsZero (limit A) ∧
        IsZero A.firstDerivedLimit ∧
          IsZero A.countableCoproduct.firstDerivedLimit := by
  constructor
  · intro hA
    have hlim_ml := (hasProObjectValue_zero_iff_limit_isZero_and_isMittagLeffler A).1 hA
    have hfirst :=
      (isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero A).1
        hlim_ml.2
    exact ⟨hlim_ml.1, hfirst.1, hfirst.2⟩
  · rintro ⟨hlim, hfirst, hcoprodfirst⟩
    exact
      (hasProObjectValue_zero_iff_limit_isZero_and_isMittagLeffler A).2
        ⟨hlim,
          (isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
            A).2 ⟨hfirst, hcoprodfirst⟩⟩

end SequentialInverseSystem

end CategoryTheory
