import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_4_2
import StacksProject_2024.stacks_project.Chap28.Definition_28_7_1
import StacksProject_2024.stacks_project.Chap28.Lemma_28_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- - Chapter 28 already uses `Scheme.HasRingPropertyLocally` as the canonical scheme owner for
--   locality on affine opens, and `Lemma_28_4_3` packages its affine/open-cover criteria;
-- - the source-facing owner for this file remains `Scheme.isNormal` from `Definition_28_7_1`;
-- - this file is therefore a bridge/view item: it specializes those existing locality criteria to
--   normality instead of restating a parallel affine-cover surface.

variable (X : Scheme.{u})

/-- Lemma 28.7.2 (0): a scheme `X` is normal if and only if normality is a local ring property on
its affine opens, i.e. iff `X.HasRingPropertyLocally (fun R ↦ IsNormalRing R)`. -/
theorem isNormal_iff_hasRingPropertyLocally_isNormalRing :
    X.isNormal ↔
      X.HasRingPropertyLocally (fun R : CommRingCat.{u} ↦ _root_.IsNormalRing R) := sorry

/-- Lemma 28.7.2 (1): a scheme `X` is normal if and only if for every affine open `U ⊆ X`, the
ring of sections `Γ(X, U)` is normal. -/
theorem isNormal_iff_forall_affineOpen_sectionsRing_isNormalRing :
    X.isNormal ↔
      ∀ U : X.affineOpens, _root_.IsNormalRing (Γ(X, U)) := sorry

/-- Lemma 28.7.2 (2): a scheme `X` is normal if and only if it admits an affine open cover, indexed
whose section rings are normal. -/
theorem isNormal_iff_exists_affineOpenCover_sectionsRing_isNormalRing :
    X.isNormal ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, _root_.IsNormalRing (Γ(X, (𝒰.openCover.f i).opensRange)) := sorry

/-- Lemma 28.7.2 (3): a scheme `X` is normal if and only if it admits an open cover by normal
open subschemes. -/
theorem isNormal_iff_exists_openCover_by_normalOpens :
    X.isNormal ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, ((𝒰.f i).opensRange).toScheme.isNormal := sorry

/-- Lemma 28.7.2 (4): if a scheme `X` is normal, then every open subscheme of `X` is normal. -/
theorem isNormal_toScheme (hX : X.isNormal) (U : X.Opens) :
    U.toScheme.isNormal := sorry

end AlgebraicGeometry.Scheme
