import Mathlib
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_87_15 (from Chap15) -/
open CategoryTheory
namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

/- Domain-style sampling for Lemma 15.87.15:
- primary domain: short exact sequences of sequential inverse systems of abelian groups, the
  first derived inverse limit, and the Emmanouil criterion for the Mittag-Leffler condition;
- sampled owner declarations:
  `SequentialInverseSystem.IsMittagLeffler`,
  `SequentialInverseSystem.countableCoproduct`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `sequentialAbelianGroupLimit_exact₅`,
  `ShortComplex.ShortExact.map_of_exact`;
- best owner abstraction: the tower owner is `SequentialInverseSystem AddCommGrpCat`, the
  vanishing obstruction is `firstDerivedLimit`, the countable direct-sum tower is the canonical
  derived owner `countableCoproduct`, and preservation of short exactness under stagewise countable
  coproducts should be expressed by mapping along the exact functor rather than by a parallel
  stagewise wrapper;
- primitive-vs-derived split:
  primitive data are only the short exact sequence `S` and the two source-facing
  hypotheses `S.X₁.IsMittagLeffler` and `S.X₃.IsMittagLeffler`;
  the vanishing of the two `R^1 lim` terms and the mapped short exact sequence on countable
  coproduct towers are derived API from the canonical owners above.

Source/core/bridge triage:
- `source-facing`: the middle-term Mittag-Leffler conclusion for a short exact sequence of towers;
- `core/canonical`: `IsMittagLeffler`, `countableCoproduct`, `firstDerivedLimit`, and the five-term
  exact sequence `sequentialAbelianGroupLimit_exact₅`;
- `bridge/view`: applying Emmanouil's criterion to the three towers and, proof-theoretically, the
  exact `R^1 lim` sequence and stagewise countable direct sums in abelian groups.
-/

/-- Lemma 15.87.15: for a short exact sequence `0 ⟶ (A_i) ⟶ (B_i) ⟶ (C_i) ⟶ 0` of inverse
systems of abelian groups, if `(A_i)` and `(C_i)` are Mittag-Leffler, then `(B_i)` is
Mittag-Leffler. -/
theorem isMittagLeffler_middle_of_shortExact
    (S : ShortComplex AbSeq)
    (hS : S.ShortExact)
    (hA : S.X₁.IsMittagLeffler)
    (hC : S.X₃.IsMittagLeffler) :
    S.X₂.IsMittagLeffler := by
  -- Apply Emmanouil's criterion to `S.X₂`. The proof uses the exact sequence for `R^1 lim`
  -- together with the same argument after taking stagewise countable direct sums.
  sorry

end SequentialInverseSystem

end CategoryTheory

/-! ### Lemma_15_87_16 (from Chap15) -/
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
