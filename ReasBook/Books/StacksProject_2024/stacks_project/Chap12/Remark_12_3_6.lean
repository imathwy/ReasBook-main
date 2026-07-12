import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Domain-style sampling for Remark 12.3.6:
- primary domain: binary biproducts/direct sums in a preadditive category;
- sampled canonical declarations:
  `BinaryBicone`,
  `inl_of_isLimit`,
  `fst_of_isColimit`,
  `IsBilimit.binary_total`,
  `isBinaryBilimitOfTotal`;
- owner abstraction: `BinaryBicone X Y`;
- primitive data: a binary bicone `b : BinaryBicone X Y`;
- derived API: the inclusions determined by `b.toCone`, the projections determined by
  `b.toCocone`, and the total relation characterizing `b.IsBilimit`.

Source/core/bridge triage for Remark 12.3.6:
- source-facing: the three-part characterization of a binary direct sum, namely uniqueness of the
  inclusions from the projections, uniqueness of the projections from the inclusions, and the
  total identity for any bilimit bicone together with its converse;
- core/canonical: the owner object `BinaryBicone X Y` and its bilimit predicate `b.IsBilimit`;
- bridge/view: none, since each source clause is already present upstream as owner-level API. -/
/- Remark 12.3.6 (1): for a binary direct-sum diagram, the inclusions are uniquely determined by
the projections. -/
recall inl_of_isLimit {X Y : C} {b : BinaryBicone X Y} (hb : IsLimit b.toCone) :
    b.inl = hb.lift (BinaryFan.mk (𝟙 X) 0)

recall inr_of_isLimit {X Y : C} {b : BinaryBicone X Y} (hb : IsLimit b.toCone) :
    b.inr = hb.lift (BinaryFan.mk 0 (𝟙 Y))

/- Remark 12.3.6 (2): dually, the projections are uniquely determined by the inclusions. -/
recall fst_of_isColimit {X Y : C} {b : BinaryBicone X Y} (hb : IsColimit b.toCocone) :
    b.fst = hb.desc (BinaryCofan.mk (𝟙 X) 0)

recall snd_of_isColimit {X Y : C} {b : BinaryBicone X Y} (hb : IsColimit b.toCocone) :
    b.snd = hb.desc (BinaryCofan.mk 0 (𝟙 Y))

/- Remark 12.3.6 (3): any binary biproduct satisfies the total relation, and conversely that
relation already forces the bicone to be a binary biproduct. -/
recall IsBilimit.binary_total {X Y : C} {b : BinaryBicone X Y} (hb : b.IsBilimit) :
    b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt

recall isBinaryBilimitOfTotal {X Y : C} (b : BinaryBicone X Y)
    (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) : b.IsBilimit

end

end CategoryTheory
