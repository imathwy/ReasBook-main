import Mathlib
import StacksProject_2024.Chap07.Definition_7_29_2
import StacksProject_2024.Chap34.Definition_34_7_8
import StacksProject_2024.Chap34.Lemma_34_7_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace Scheme

-- Semantic recall: `lean_leansearch` returned the dense-subsite/sheaf-equivalence owners
-- `Functor.IsDenseSubsite.sheafEquiv` and
-- `Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension`.
-- Local Chapter 34 precedent in the affine Zariski and affine étale comparison lemmas fixes the
-- source-facing surface as a dense-subsite statement for the inclusion, followed by the induced
-- equivalence on set-valued sheaves.

variable (S : Scheme.{u})

/-- Lemma 34.7.11 (1): the inclusion
`(\textit{Aff}/S)_{fppf} ⥤ (\mathit{Sch}/S)_{fppf}` is special cocontinuous; canonically, it is a
dense-subsite functor for the big affine fppf topology and the big fppf topology over `S`. -/
@[stacks 021V]
theorem bigAffineFppfInclusion_isDenseSubsite :
    (Scheme.AffineOver.forget S).IsDenseSubsite
      (Scheme.bigAffineFppfTopology S) (Scheme.fppfTopology.over S) := sorry

/-- The affine fppf inclusion carries the canonical dense-subsite instance from
`bigAffineFppfInclusion_isDenseSubsite`. -/
instance bigAffineFppfInclusionIsDenseSubsite :
    (Scheme.AffineOver.forget S).IsDenseSubsite
      (Scheme.bigAffineFppfTopology S) (Scheme.fppfTopology.over S) :=
  bigAffineFppfInclusion_isDenseSubsite S

/-- Lemma 34.7.11 (2): the special-cocontinuous affine inclusion induces an equivalence of topoi;
equivalently, the restriction/inverse-image functor on set-valued sheaves is an equivalence. -/
@[stacks 021V]
theorem bigAffineFppfSheafPushforwardContinuous_isEquivalence :
    ((Scheme.AffineOver.forget S).sheafPushforwardContinuous (Type v)
      (Scheme.bigAffineFppfTopology S) (Scheme.fppfTopology.over S)).IsEquivalence := sorry

end Scheme
end AlgebraicGeometry
