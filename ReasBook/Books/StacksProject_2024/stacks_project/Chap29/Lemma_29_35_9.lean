import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side owners `LocallyOfFiniteType` and
  `LocallyOfFinitePresentation`;
- the local ring-level analogue is `Algebra.GUnramified` in `Chap10/Definition_10_151_1.lean`.
-/

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Source-facing owner: a morphism of schemes is unramified if it is formally unramified and
locally of finite type. -/
class Unramified (f : X ⟶ S) : Prop extends FormallyUnramified f, LocallyOfFiniteType f

/-- A formally unramified morphism locally of finite type is unramified. -/
instance instUnramified [FormallyUnramified f] [LocallyOfFiniteType f] : Unramified f where
  toFormallyUnramified := ‹FormallyUnramified f›
  toLocallyOfFiniteType := ‹LocallyOfFiniteType f›

/-- Lemma 29.35.9 (1): a morphism is unramified exactly when it is formally unramified and
locally of finite type. -/
@[stacks 02GD]
theorem unramified_iff_formallyUnramified_and_locallyOfFiniteType (f : X ⟶ S) :
    Unramified f ↔ FormallyUnramified f ∧ LocallyOfFiniteType f := by
  constructor
  · intro h
    exact ⟨h.toFormallyUnramified, h.toLocallyOfFiniteType⟩
  · rintro ⟨hformally, hfiniteType⟩
    exact { toFormallyUnramified := hformally, toLocallyOfFiniteType := hfiniteType }

/-- An unramified morphism is formally unramified. -/
theorem Unramified.formallyUnramified (h : Unramified f) :
    FormallyUnramified f :=
  h.toFormallyUnramified

/-- An unramified morphism is locally of finite type. -/
theorem Unramified.locallyOfFiniteType (h : Unramified f) :
    LocallyOfFiniteType f :=
  h.toLocallyOfFiniteType

/-- Source-facing owner: a morphism of schemes is G-unramified if it is unramified and locally of
finite presentation; equivalently, it is formally unramified and locally of finite presentation. -/
class GUnramified (f : X ⟶ S) : Prop extends FormallyUnramified f, LocallyOfFinitePresentation f

/-- A formally unramified morphism locally of finite presentation is G-unramified. -/
instance instGUnramified [FormallyUnramified f] [LocallyOfFinitePresentation f] : GUnramified f where
  toFormallyUnramified := ‹FormallyUnramified f›
  toLocallyOfFinitePresentation := ‹LocallyOfFinitePresentation f›

/-- A G-unramified morphism is unramified. -/
instance instUnramifiedOfGUnramified [GUnramified f] : Unramified f where
  toFormallyUnramified := ‹GUnramified f›.toFormallyUnramified
  toLocallyOfFiniteType := by
    let _ : LocallyOfFinitePresentation f := ‹GUnramified f›.toLocallyOfFinitePresentation
    infer_instance

/-- A morphism is G-unramified exactly when it is unramified and locally of finite presentation. -/
theorem gUnramified_iff_unramified_and_locallyOfFinitePresentation (f : X ⟶ S) :
    GUnramified f ↔ Unramified f ∧ LocallyOfFinitePresentation f := by
  constructor
  · intro h
    exact ⟨by
      let _ : GUnramified f := h
      infer_instance, h.toLocallyOfFinitePresentation⟩
  · rintro ⟨hunramified, hfinitePresentation⟩
    exact
      { toFormallyUnramified := hunramified.formallyUnramified
        toLocallyOfFinitePresentation := hfinitePresentation }

/-- Lemma 29.35.9 (2): a morphism is G-unramified exactly when it is formally unramified and
locally of finite presentation. -/
@[stacks 02GD]
theorem gUnramified_iff_formallyUnramified_and_locallyOfFinitePresentation (f : X ⟶ S) :
    GUnramified f ↔ FormallyUnramified f ∧ LocallyOfFinitePresentation f := by
  constructor
  · intro h
    exact ⟨h.toFormallyUnramified, h.toLocallyOfFinitePresentation⟩
  · rintro ⟨hformally, hfinitePresentation⟩
    exact
      { toFormallyUnramified := hformally
        toLocallyOfFinitePresentation := hfinitePresentation }

/-- A G-unramified morphism is unramified. -/
theorem GUnramified.unramified (h : GUnramified f) :
    Unramified f :=
  let _ : GUnramified f := h
  inferInstance

/-- A G-unramified morphism is formally unramified. -/
theorem GUnramified.formallyUnramified (h : GUnramified f) :
    FormallyUnramified f :=
  h.toFormallyUnramified

/-- A G-unramified morphism is locally of finite type. -/
theorem GUnramified.locallyOfFiniteType (h : GUnramified f) :
    LocallyOfFiniteType f :=
  by
    let _ : LocallyOfFinitePresentation f := h.toLocallyOfFinitePresentation
    infer_instance

/-- A G-unramified morphism is locally of finite presentation. -/
theorem GUnramified.locallyOfFinitePresentation (h : GUnramified f) :
    LocallyOfFinitePresentation f :=
  h.toLocallyOfFinitePresentation

end AlgebraicGeometry
