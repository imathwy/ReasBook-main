import Mathlib
import StacksProject_2024.Chap07.Definition_7_29_2
import StacksProject_2024.Chap34.Definition_34_5_8

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry

-- Declarations for this item are provided below.

/- Semantic recall / owner check:
- `lean_leansearch` recalled the canonical dense-subsite/sheaf-equivalence owners
  `Functor.IsDenseSubsite.sheafEquiv` and `Functor.sheafPushforwardContinuous`.
- Local Chapter 34 precedent in `Lemma_34_3_10`, `Lemma_34_4_11`, and `Lemma_34_6_9` fixes the
  public shape here: use the affine site topology from `Definition_34_5_8`, then state the affine
  inclusion as
  a dense-subsite theorem together with the induced equivalence on set-valued sheaves.
- `Lemma_34_5_4` is the affine-refinement input behind the dense-subsite proof for smooth
  coverings; this file only consumes the affine-site owner API from `Definition_34_5_8`.
-/

variable (S : Scheme.{u})

/-- The canonical inclusion functor from the big affine smooth site of `S` to the big smooth site
of `S`. -/
abbrev bigAffineSmoothSiteInclusion : bigAffineSmoothSite S ⥤ Over S :=
  (show ObjectProperty (Over S) from fun X ↦ IsAffine X.left).ι

/-- Lemma 34.5.9 (1): the functor `(Aff/S)_{smooth} ⥤ (Sch/S)_{smooth}` is special
cocontinuous; canonically, the affine inclusion is a dense-subsite functor for the affine smooth
topology and the big smooth topology over `S`. -/
@[stacks 06VC]
theorem bigAffineSmoothSiteInclusion_isDenseSubsite :
    (bigAffineSmoothSiteInclusion S).IsDenseSubsite
      (bigAffineSmoothTopology S) (bigSmoothSite S) := sorry

/-- The affine smooth inclusion carries the canonical dense-subsite instance from
`bigAffineSmoothSiteInclusion_isDenseSubsite`. -/
instance bigAffineSmoothSiteInclusionIsDenseSubsite :
    (bigAffineSmoothSiteInclusion S).IsDenseSubsite
      (bigAffineSmoothTopology S) (bigSmoothSite S) :=
  bigAffineSmoothSiteInclusion_isDenseSubsite S

/-- Lemma 34.5.9 (2): the special-cocontinuous affine inclusion induces an equivalence of topoi;
equivalently, the restriction/inverse-image functor on set-valued sheaves is an equivalence. -/
@[stacks 06VC]
theorem bigAffineSmoothSheafPushforwardContinuous_isEquivalence :
    ((bigAffineSmoothSiteInclusion S).sheafPushforwardContinuous (Type v)
      (bigAffineSmoothTopology S) (bigSmoothSite S)).IsEquivalence := sorry

end AlgebraicGeometry
