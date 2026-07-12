import Mathlib.AlgebraicGeometry.Morphisms.Affine

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-morphism owner
-- `AlgebraicGeometry.IsAffineHom`, its affine-open criterion
-- `AlgebraicGeometry.isAffineHom_iff`, and the local existence theorem
-- `AlgebraicGeometry.isAffineHom_of_forall_exists_isAffineOpen`. The source remark is recorded
-- here as the direct affine-open-cover implication together with its explicit affine-preimage
-- consequence.

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Remark 29.11.4: if the target admits an affine open cover whose pullbacks along `f` are
affine, then `f` is affine. This isolates the direct implication `(2) → (1)` from
Lemma 29.11.3. -/
theorem isAffineHom_of_affineOpenCover
    (𝒰 : S.AffineOpenCover)
    (h𝒰 : ∀ i : 𝒰.I₀, IsAffine ((𝒰.openCover.pullback₁ f).X i)) :
    IsAffineHom f := sorry

/-- Under the affine-open-cover hypothesis of Remark 29.11.4, the preimage of any affine open of
the target is affine. -/
theorem isAffineOpen_preimage_of_affineOpenCover
    (𝒰 : S.AffineOpenCover)
    (h𝒰 : ∀ i : 𝒰.I₀, IsAffine ((𝒰.openCover.pullback₁ f).X i))
    (V : S.affineOpens) :
    IsAffineOpen ((TopologicalSpace.Opens.map f.base).obj (V : S.Opens)) := sorry

end

end AlgebraicGeometry
