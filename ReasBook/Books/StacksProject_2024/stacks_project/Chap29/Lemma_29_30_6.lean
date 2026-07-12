import StacksProject_2024.Chap29.Definition_29_21_1
import StacksProject_2024.Chap29.Definition_29_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/- Semantic recall / analogue check:
- `lean_leansearch` confirmed that the canonical scheme-side finite-presentation owner is
  `LocallyOfFinitePresentation`;
- Chapter 29 already exposes both source-facing affine-neighborhood owners
  `LocallyOfType RingHom.Syntomic f` and `LocallyOfType RingHom.FinitePresentation f`, together
  with the canonical bridge `Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType`;
- this lemma is therefore the direct source-faithful bridge obtained by projecting the
  finite-presentation clause from the local syntomic witnesses.
-/

/-- Lemma 29.30.6: a syntomic morphism is locally of finite presentation. -/
@[stacks 01UK]
theorem syntomic_locallyOfFinitePresentation
    (hf : Syntomic f) :
    LocallyOfFinitePresentation f := by
  rw [Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType f]
  refine ⟨fun x ↦ ?_⟩
  rcases (LocallyOfType.exists_affineNeighborhood RingHom.Syntomic hf x) with
    ⟨U, hxU, V, e, hsyntomic⟩
  exact ⟨U, hxU, V, e, RingHom.Syntomic.finitePresentation hsyntomic⟩

/-- A syntomic morphism is locally of finite presentation. -/
@[stacks 01UK, instance]
instance instLocallyOfFinitePresentationOfSyntomic [hf : Syntomic f] :
    LocallyOfFinitePresentation f :=
  syntomic_locallyOfFinitePresentation hf

end AlgebraicGeometry
