import StacksProject_2024.Chap29.Lemma_29_25_3
import StacksProject_2024.Chap29.Lemma_29_30_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

-- Semantic recall: `AlgebraicGeometry.Flat` is the canonical scheme-side flatness owner, with
-- affine-open criterion `AlgebraicGeometry.flat_iff`; Chapter 29 already exports the source-facing
-- affine-open criterion
-- `Scheme.Hom.syntomic_iff_affineOpen_appLE_syntomic` for syntomic morphisms, so this lemma is
-- the direct bridge from the source-facing syntomic owner to the canonical flat owner.

/-- Lemma 29.30.7: a syntomic morphism of schemes is flat. -/
@[stacks 01UL]
theorem syntomic_flat (hf : Syntomic f) :
    Flat f := by
  rw [Scheme.Hom.flat_iff_affineOpen_appLE_flat]
  rw [Scheme.Hom.syntomic_iff_affineOpen_appLE_syntomic] at hf
  intro U hU V hV e
  exact RingHom.Syntomic.flat (hf hU hV e)

end AlgebraicGeometry

end
