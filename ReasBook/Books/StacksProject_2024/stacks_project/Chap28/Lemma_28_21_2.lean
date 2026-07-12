import StacksProject_2024.Chap28.Definition_28_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- Semantic recall: `lean_leansearch` was unavailable here (HTTP 500). The source-facing affine
-- `Spec` clause is best exposed through the canonical owner `tilde M`, while the cover criterion
-- uses the canonical owner `X.AffineOpenCover`.

/-- Lemma 28.21.2 (1): a quasi-coherent `\mathcal{O}_X`-module `ℱ` is locally projective if and
only if there exists an affine open covering of `X` on which all section modules are projective. -/
@[stacks 05JQ]
theorem isLocallyProjective_iff_exists_affineOpenCover_projectiveSections
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsLocallyProjective ℱ ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          Module.Projective (Γ(X, (𝒰.f i).opensRange)) (Γ(ℱ, (𝒰.f i).opensRange)) := sorry

/-- Lemma 28.21.2 (2): if `X = Spec(A)` and `ℱ = \widetilde{M}`, then `ℱ` is locally projective
if and only if `M` is a projective `A`-module. -/
@[stacks 05JQ]
theorem tilde_isLocallyProjective_iff_module_projective
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    IsLocallyProjective (tilde M) ↔ Module.Projective R M := sorry

end AlgebraicGeometry.Scheme.Modules
