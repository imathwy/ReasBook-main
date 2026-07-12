import Mathlib.Tactic.Recall
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical mathlib base-change stability owner
  `AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange`;
- `Definition_29_15_1.lean` records the source phrase “of finite type” for scheme morphisms by
  the local owner `Scheme.Hom.FiniteType`;
- the base-changed morphism is the canonical pullback projection `pullback.snd f g`.
-/

/- Lemma 29.15.4 (1): the base change of a morphism which is locally of finite type is locally of
finite type. This is exactly the canonical mathlib pullback-stability instance for
`LocallyOfFiniteType`. -/
recall AlgebraicGeometry.instLocallyOfFiniteTypeSndScheme

namespace AlgebraicGeometry.Scheme.Hom

section

variable {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/-- Lemma 29.15.4 (2): the base change of a morphism of finite type is of finite type. -/
@[stacks 01T4]
theorem finiteType_baseChange (hf : FiniteType f) :
    FiniteType (pullback.snd f g) := by
  have h_quasiCompact : QuasiCompact (pullback.snd f g) := by
    letI : QuasiCompact f := hf.toQuasiCompact
    exact MorphismProperty.pullback_snd f g inferInstance
  have h_locallyOfFiniteType : LocallyOfFiniteType (pullback.snd f g) := by
    letI : LocallyOfFiniteType f := hf.toLocallyOfFiniteType
    exact MorphismProperty.pullback_snd f g inferInstance
  exact
    { toQuasiCompact := h_quasiCompact
      toLocallyOfFiniteType := h_locallyOfFiniteType }

/-- Any base change of a finite type morphism is finite type. -/
@[stacks 01T4, instance]
instance instFiniteTypePullbackSndOfFiniteType [FiniteType f] :
    FiniteType (pullback.snd f g) :=
  finiteType_baseChange f g inferInstance

end

end AlgebraicGeometry.Scheme.Hom
