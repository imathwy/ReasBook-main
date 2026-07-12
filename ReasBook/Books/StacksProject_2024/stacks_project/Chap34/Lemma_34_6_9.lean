import Mathlib
import StacksProject_2024.Chap07.Definition_7_29_2
import StacksProject_2024.Chap34.Definition_34_6_8
import StacksProject_2024.Chap34.Lemma_34_6_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
noncomputable section

universe u v

namespace AlgebraicGeometry

/- Semantic recall / owner check:
- `lean_leansearch` returned the canonical dense-subsite/sheaf-equivalence owners
  `Functor.IsDenseSubsite.sheafEquiv` and `Functor.IsDenseSubsite.sheafEquiv_functor`.
- Local Chapter 34 precedent `Lemma_34_3_10` / `Lemma_34_4_11` fixes the public shape here: the
  affine inclusion is stated as a dense-subsite theorem, with the induced equivalence of sheaf
  categories recorded through `sheafPushforwardContinuous`.
- `Definition_34_6_8` now owns the affine syntomic site surface itself, while `Lemma_34_6_4` is
  the affine-refinement input behind the dense-subsite proof.
-/

variable (S : Scheme.{u})

/-- Lemma 34.6.9 (1): the inclusion `(Aff/S)_{syntomic} ⥤ (Sch/S)_{syntomic}` is special
cocontinuous; canonically, it is a dense-subsite functor for the affine syntomic topology and the
big syntomic topology over `S`. -/
@[stacks 06VD]
theorem bigAffineSyntomicSiteInclusion_isDenseSubsite :
    (bigAffineSyntomicForget S).IsDenseSubsite
      (bigAffineSyntomicTopology S) (bigSyntomicSite S) := sorry

/-- The affine syntomic inclusion carries the canonical dense-subsite instance from
`bigAffineSyntomicSiteInclusion_isDenseSubsite`. -/
instance bigAffineSyntomicSiteInclusionIsDenseSubsite :
    (bigAffineSyntomicForget S).IsDenseSubsite
      (bigAffineSyntomicTopology S) (bigSyntomicSite S) :=
  bigAffineSyntomicSiteInclusion_isDenseSubsite S

/-- Lemma 34.6.9 (2): the special-cocontinuous affine inclusion induces an equivalence of topoi;
equivalently, the restriction/inverse-image functor on set-valued sheaves is an equivalence. -/
@[stacks 06VD]
theorem bigAffineSyntomicSheafPushforwardContinuous_isEquivalence :
    ((bigAffineSyntomicForget S).sheafPushforwardContinuous (Type v)
      (bigAffineSyntomicTopology S) (bigSyntomicSite S)).IsEquivalence := sorry

end AlgebraicGeometry
