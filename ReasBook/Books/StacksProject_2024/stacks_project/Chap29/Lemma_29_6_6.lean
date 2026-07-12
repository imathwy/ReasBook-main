import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

variable {X1 X2 Y1 Y2 : Scheme}
variable {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2}
variable {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}

-- Semantic recall verified against mathlib: the canonical owners are `Scheme.Hom.image`,
-- `Scheme.Hom.toImage`, and `Scheme.Hom.imageι`, and the induced map between closed subschemes
-- is built with `Scheme.IdealSheafData.subschemeMap`. The Stacks tag evidence is consistent:
-- item tag `01R9` matches the source URL `/tag/01R9`.

namespace Scheme.Hom

private lemma imageMap_condition
    (sq : CommSq gX f₁ f₂ gY) :
    f₂.ker ≤ f₁.ker.map gY := by
  rw [← Scheme.Hom.ker_comp, ← sq.w]
  exact Scheme.Hom.le_ker_comp gX f₂

/-- Lemma 29.6.6 (1): a commutative square of schemes induces a morphism between the
scheme-theoretic images of the horizontal morphisms. -/
@[stacks 01R9]
noncomputable def imageMap
    (sq : CommSq gX f₁ f₂ gY) :
    image f₁ ⟶ image f₂ :=
  Scheme.IdealSheafData.subschemeMap f₁.ker f₂.ker gY (imageMap_condition sq)

/-- Lemma 29.6.6 (2): the induced morphism on scheme-theoretic images is compatible with the
closed-immersion maps into `Y1` and `Y2`. -/
@[stacks 01R9]
theorem imageMap_commSq
    (sq : CommSq gX f₁ f₂ gY) :
    CommSq (imageMap sq) (imageι f₁) (imageι f₂) gY := sorry

/-- Lemma 29.6.6 (3): the factorization maps from `X1` and `X2` to their scheme-theoretic images
fit into a commutative square with the induced image morphism. -/
@[stacks 01R9]
theorem toImage_imageMap_commSq
    (sq : CommSq gX f₁ f₂ gY) :
    CommSq gX (toImage f₁) (toImage f₂) (imageMap sq) := sorry

end Scheme.Hom

end

end AlgebraicGeometry
