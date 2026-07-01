import SmoothManifoldsLee.Chap03.Sec03_16.Proposition_3_21
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` was unavailable in this session, so this file follows the local tangent-map
-- API already established in `Proposition_3_21` and nearby Section 3.16 files.

noncomputable section

open scoped Manifold ContDiff

section CompositionAndIdentity

universe uE uE' uE'' uH uH' uH'' uM uN uP

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {I : ModelWithCorners ℝ E H}
variable {I' : ModelWithCorners ℝ E' H'}
variable {I'' : ModelWithCorners ℝ E'' H''}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold I'' ∞ P]
variable {F : M → N} {G : N → P}

/-- Corollary 3.22 (1): the global differential carries composition to composition:
`d (G ∘ F) = dG ∘ dF`. -/
theorem tangentMap_comp_of_smooth
    (hF : ContMDiff I I' ∞ F) (hG : ContMDiff I' I'' ∞ G) :
    tangentMap I I'' (G ∘ F) = tangentMap I' I'' G ∘ tangentMap I I' F := sorry

/-- Corollary 3.22 (2): the global differential of the identity is the identity on the tangent
bundle. -/
theorem tangentMap_id_eq_id :
    tangentMap I I (id : M → M) = id := sorry

end CompositionAndIdentity

section Diffeomorphisms

universe uE uE' uH uH' uM uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {I' : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

/-- The tangent map of the inverse diffeomorphism is a left inverse to the tangent map. -/
theorem tangentMap_symm_leftInverse
    (Φ : M ≃ₘ⟮I, I'⟯ N) :
    Function.LeftInverse (tangentMap I' I Φ.symm) (tangentMap I I' Φ) := sorry

/-- The tangent map of the inverse diffeomorphism is a right inverse to the tangent map. -/
theorem tangentMap_symm_rightInverse
    (Φ : M ≃ₘ⟮I, I'⟯ N) :
    Function.RightInverse (tangentMap I' I Φ.symm) (tangentMap I I' Φ) := sorry

/-- Corollary 3.22 (3): if `Φ` is a diffeomorphism, then its global differential is a
diffeomorphism of tangent bundles, and its inverse is the global differential of `Φ.symm`. -/
def tangentMap_diffeomorph
    (Φ : M ≃ₘ⟮I, I'⟯ N) :
    TangentBundle I M ≃ₘ⟮I.tangent, I'.tangent⟯ TangentBundle I' N where
  toEquiv :=
    { toFun := tangentMap I I' Φ
      invFun := tangentMap I' I Φ.symm
      left_inv := tangentMap_symm_leftInverse Φ
      right_inv := tangentMap_symm_rightInverse Φ }
  contMDiff_toFun := Φ.contMDiff.contMDiff_tangentMap le_rfl
  contMDiff_invFun := Φ.symm.contMDiff.contMDiff_tangentMap le_rfl

/-- The diffeomorphism `tangentMap_diffeomorph Φ` acts by the tangent map of `Φ`. -/
theorem tangentMap_diffeomorph_apply
    (Φ : M ≃ₘ⟮I, I'⟯ N) (v : TangentBundle I M) :
    tangentMap_diffeomorph Φ v = tangentMap I I' Φ v := sorry

end Diffeomorphisms
