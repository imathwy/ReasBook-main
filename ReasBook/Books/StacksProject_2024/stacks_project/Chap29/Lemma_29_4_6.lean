import Mathlib
import StacksProject_2024.Chap29.Definition_29_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.subscheme` as the
-- closed-subscheme owner; local Definition 29.4.4 fixes union as `(I ⊓ J).subscheme` and
-- intersection as `(I ⊔ J).subscheme`.

variable {S : Scheme.{u}}

/-- The structure sheaf of a closed subscheme of `S`, regarded as an `\mathcal O_S`-module by
pushforward along its closed immersion into `S`. -/
abbrev closedSubschemeStructureSheafOn (I : S.IdealSheafData) : S.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj (SheafOfModules.unit I.subscheme.ringCatSheaf)

/-- The canonical map of pushed-forward structure sheaves induced by an inclusion of closed
subschemes coming from an inclusion of ideal sheaf data. -/
noncomputable def closedSubschemeStructureSheafMap {I J : S.IdealSheafData} (h : I ≤ J) :
    closedSubschemeStructureSheafOn I ⟶ closedSubschemeStructureSheafOn J :=
  (Scheme.Modules.pushforward I.subschemeι).map
      (SheafOfModules.unitToPushforwardObjUnit
        (Scheme.IdealSheafData.inclusion h).toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp (Scheme.IdealSheafData.inclusion h) I.subschemeι).hom.app
      (SheafOfModules.unit J.subscheme.ringCatSheaf) ≫
    (Scheme.Modules.pushforwardCongr (Scheme.IdealSheafData.inclusion_subschemeι h)).hom.app
      (SheafOfModules.unit J.subscheme.ringCatSheaf)

/-- The first map in the Mayer-Vietoris sequence for two closed subschemes: the pushed-forward
structure sheaf of the scheme-theoretic union maps to the product of those of the two
subschemes. -/
noncomputable abbrev schemeTheoreticUnionToProduct (I J : S.IdealSheafData) :
    closedSubschemeStructureSheafOn (I ⊓ J) ⟶
      Limits.prod (closedSubschemeStructureSheafOn I) (closedSubschemeStructureSheafOn J) :=
  Limits.prod.lift
    (closedSubschemeStructureSheafMap (inf_le_left : I ⊓ J ≤ I))
    (closedSubschemeStructureSheafMap (inf_le_right : I ⊓ J ≤ J))

/-- The second map in the Mayer-Vietoris sequence for two closed subschemes: the difference of the
two canonical maps from the product to the pushed-forward structure sheaf of the
scheme-theoretic intersection. -/
noncomputable abbrev schemeTheoreticProductToIntersection (I J : S.IdealSheafData) :
    Limits.prod (closedSubschemeStructureSheafOn I) (closedSubschemeStructureSheafOn J) ⟶
      closedSubschemeStructureSheafOn (I ⊔ J) :=
  Limits.prod.fst ≫ closedSubschemeStructureSheafMap (le_sup_left : I ≤ I ⊔ J) -
    Limits.prod.snd ≫ closedSubschemeStructureSheafMap (le_sup_right : J ≤ I ⊔ J)

/-- The two displayed maps in the Mayer-Vietoris sequence compose to zero. -/
theorem schemeTheoreticUnionToProduct_comp_schemeTheoreticProductToIntersection
    (I J : S.IdealSheafData) :
    schemeTheoreticUnionToProduct I J ≫ schemeTheoreticProductToIntersection I J = 0 := sorry

/-- Lemma 29.4.6 (1): the canonical morphism from `X` to the scheme-theoretic union `X \cup Y`
is a closed immersion. In the `IdealSheafData` owner, this is the inclusion
`I.subscheme \to (I \inf J).subscheme`. -/
@[stacks 0C4J]
theorem schemeTheoreticUnion_isClosedImmersion_left (I J : S.IdealSheafData) :
    IsClosedImmersion
      (Scheme.IdealSheafData.inclusion (inf_le_left : I ⊓ J ≤ I) :
        I.subscheme ⟶ Scheme.schemeTheoreticUnion I J) := sorry

/-- Lemma 29.4.6 (2): the canonical morphism from `Y` to the scheme-theoretic union `X \cup Y`
is a closed immersion. In the `IdealSheafData` owner, this is the inclusion
`J.subscheme \to (I \inf J).subscheme`. -/
@[stacks 0C4J]
theorem schemeTheoreticUnion_isClosedImmersion_right (I J : S.IdealSheafData) :
    IsClosedImmersion
      (Scheme.IdealSheafData.inclusion (inf_le_right : I ⊓ J ≤ J) :
        J.subscheme ⟶ Scheme.schemeTheoreticUnion I J) := sorry

/-- Lemma 29.4.6 (3): for closed subschemes cut out by ideal sheaf data `I` and `J`, the sequence
`0 \to \mathcal O_{X \cup Y} \to \mathcal O_X \times \mathcal O_Y
\to \mathcal O_{X \cap Y} \to 0`, viewed as a sequence of `\mathcal O_S`-modules by
pushforward to `S`, is short exact. -/
@[stacks 0C4J]
theorem schemeTheoreticUnion_structureSheaf_shortExact (I J : S.IdealSheafData) :
    (ShortComplex.mk (schemeTheoreticUnionToProduct I J)
      (schemeTheoreticProductToIntersection I J)
      (schemeTheoreticUnionToProduct_comp_schemeTheoreticProductToIntersection I J)).ShortExact := sorry

/-- Lemma 29.4.6 (4): the square
`X \cap Y \to X`, `X \cap Y \to Y`, `X \to X \cup Y`, `Y \to X \cup Y`
is cocartesian in schemes. -/
@[stacks 0C4J]
theorem schemeTheoreticUnion_isPushout (I J : S.IdealSheafData) :
    IsPushout
      (Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J) :
        Scheme.schemeTheoreticIntersection I J ⟶ I.subscheme)
      (Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J) :
        Scheme.schemeTheoreticIntersection I J ⟶ J.subscheme)
      (Scheme.IdealSheafData.inclusion (inf_le_left : I ⊓ J ≤ I) :
        I.subscheme ⟶ Scheme.schemeTheoreticUnion I J)
      (Scheme.IdealSheafData.inclusion (inf_le_right : I ⊓ J ≤ J) :
        J.subscheme ⟶ Scheme.schemeTheoreticUnion I J) := sorry

end AlgebraicGeometry
