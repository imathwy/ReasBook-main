import stacks_project.Chap15.Lemma_15_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace RingPairCat

/- Domain-style sampling for Lemma 15.12.5:
- primary domain: category theory of adjunctions and filtered-colimit preservation;
- sampled owner declarations:
  `RingPairCat.henselianPairInclusion_isRightAdjoint`,
  `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`,
  `CategoryTheory.Limits.PreservesFilteredColimits`,
  `RingPairCat.henselianPairInclusion.leftAdjoint`;
- best owner abstraction: the pair-henselization functor is the canonical left adjoint
  `henselianPairInclusion.leftAdjoint` coming from Lemma `15.12.1`, and filtered-colimit
  preservation is derived from the generic adjunction owner theorem;
- primitive data: the right-adjoint structure on `henselianPairInclusion`, supplied upstream by
  `henselianPairInclusion_isRightAdjoint`;
- derived API: the filtered-colimit preservation instance on the left adjoint.

Source/core/bridge triage:
- `source-facing`: pair henselization commutes with filtered colimits;
- `core/canonical`: `Adjunction.leftAdjoint_preservesColimits`;
- `bridge/view`: the specialization from the generic left-adjoint owner to
  `henselianPairInclusion.leftAdjoint`.
-/

section

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

-- Proof sketch: Lemma `15.12.1` identifies pair henselization with the left adjoint of the
-- inclusion `HenselianPairCat ⥤ RingPairCat`. Left adjoints preserve all small colimits, hence in
-- particular filtered colimits.
/-- Lemma 15.12.5: the pair-henselization functor from Lemma `15.12.1` preserves filtered
colimits. -/
theorem pairHenselization_preservesFilteredColimits :
    PreservesFilteredColimits henselianPairInclusion.leftAdjoint := by
  letI : PreservesColimits henselianPairInclusion.leftAdjoint :=
    (Adjunction.ofIsRightAdjoint henselianPairInclusion).leftAdjoint_preservesColimits
  infer_instance

end

end RingPairCat
