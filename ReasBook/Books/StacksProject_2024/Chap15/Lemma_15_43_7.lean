import Mathlib
import stacks_project.Chap10.Lemma_10_97_3
import stacks_project.Chap10.Lemma_10_164_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: local commutative algebra of normality and maximal-ideal adic completion;
- sampled owner declarations:
  `IsNormalRing`,
  `isNormalRing_of_faithfullyFlat`,
  `maximalIdeal_adicCompletion_algebraMap_faithfullyFlat`;
- `source-facing`: the source theorem that normality of the maximal-ideal completion descends to
  `A`;
- `core/canonical`: `IsNormalRing`;
- `bridge/view`: faithful flatness of the canonical completion map `A → ACompletion`;
- primitive data: the Noetherian local ring `A`.
-/

-- Proof sketch: the canonical map `A → AdicCompletion (maximalIdeal A) A` is faithfully flat by
-- `maximalIdeal_adicCompletion_algebraMap_faithfullyFlat`. Apply the faithfully flat descent
-- statement `isNormalRing_of_faithfullyFlat` to this map.
/-- Lemma 15.43.7: if the maximal-ideal adic completion of a Noetherian local ring `A` is normal,
then `A` is normal. -/
theorem isNormalRing_of_maximalIdealAdicCompletion_isNormal
    [IsNormalRing ACompletion] :
    IsNormalRing A :=
  isNormalRing_of_faithfullyFlat
    (algebraMap A ACompletion)
    (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A)

end
