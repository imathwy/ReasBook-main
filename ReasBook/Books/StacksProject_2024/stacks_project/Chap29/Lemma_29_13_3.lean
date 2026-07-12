import Mathlib
import StacksProject_2024.Chap29.Definition_29_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical owners `Scheme.IsQuasiAffine`, `IsOpenImmersion`,
  `QuasiCompact`, and `IsAffineHom`;
- local Chapter 29 inspection, especially `Lemma_29_11_3.lean`, confirms that the current
  environment does not expose a global relative-`Spec_S` owner for quasi-coherent
  `\mathcal O_S`-algebras;
- clauses (3) and (4) are therefore recorded in the equivalent affine-open local forms already
  used elsewhere in this chapter, rather than by introducing a fake global wrapper.
-/

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.13.3 (1): a morphism of schemes is quasi-affine if and only if the target admits an
affine open cover whose pullback pieces are quasi-affine schemes. -/
@[stacks 01SM]
theorem quasiAffineHom_iff_exists_affineOpenCover_preimage_isQuasiAffine :
    QuasiAffineHom f ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          ((𝒰.openCover.pullback₁ f).X i).IsQuasiAffine := sorry

/-- Lemma 29.13.3 (2): a morphism of schemes is quasi-affine if and only if the target admits an
affine open cover such that each pullback piece admits a quasi-compact open immersion into a
scheme affine over the corresponding cover member. This is the affine-open local form of the
relative-`Spec_S(\mathcal A)` presentation from the source. -/
@[stacks 01SM]
theorem quasiAffineHom_iff_exists_affineOpenCover_preimage_openImmersion_into_affineOverBase :
    QuasiAffineHom f ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (𝒰.X i)) (_ : IsAffineHom g)
            (j : ((𝒰.openCover.pullback₁ f).X i) ⟶ Y) (_ : QuasiCompact j)
            (_ : IsOpenImmersion j),
              j ≫ g = 𝒰.openCover.pullbackHom f i := sorry

/-- Lemma 29.13.3 (3): a morphism of schemes is quasi-affine if and only if the target admits an
affine open cover such that for each pullback piece the canonical morphism to the spectrum of its
global sections is a quasi-compact open immersion. This is the affine-open local form of the
source clause with `\mathcal A = f_*\mathcal O_X` and the canonical map from Constructions,
Lemma 27.4.7. -/
@[stacks 01SM]
theorem quasiAffineHom_iff_exists_affineOpenCover_preimage_toSpecΓ_quasiCompact_openImmersion :
    QuasiAffineHom f ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          QuasiCompact (((𝒰.openCover.pullback₁ f).X i).toSpecΓ) ∧
            IsOpenImmersion (((𝒰.openCover.pullback₁ f).X i).toSpecΓ) := sorry

end

end AlgebraicGeometry
