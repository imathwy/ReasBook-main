import SmoothManifolds_Lee_2012.Chap03.Sec03_14.Proposition_3_6
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u_𝕜 u_E u_E' u_H u_H' u_M u_M'

open scoped Manifold ContDiff

variable {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type u_E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type u_E'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type u_H} [TopologicalSpace H]
variable {H' : Type u_H'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
variable {M : Type u_M} [TopologicalSpace M] [ChartedSpace H M]
variable {M' : Type u_M'} [TopologicalSpace M'] [ChartedSpace H' M']
variable {n : ℕ∞ω}

/-
Notation 3.16-extra-4: this source-facing bridge is already provided upstream by
`diffeomorph_mfderiv_symm_eq_symm`, built from the canonical owner
`Diffeomorph.mfderivToContinuousLinearEquiv`.
-/
recall diffeomorph_mfderiv_symm_eq_symm
    (Φ : M ≃ₘ^n⟮I, I'⟯ M') (hn : n ≠ 0) (x : M) :
    mfderiv I' I Φ.symm (Φ x) =
      ((Φ.mfderivToContinuousLinearEquiv hn x).symm :
        TangentSpace I' (Φ x) →L[𝕜] TangentSpace I x)
