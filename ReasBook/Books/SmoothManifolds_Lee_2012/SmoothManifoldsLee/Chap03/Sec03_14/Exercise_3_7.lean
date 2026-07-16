import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_14.Proposition_3_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

section CompositionAndIdentity

universe u𝕜 uE uE' uE'' uH uH' uH'' uM uN uP

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {I : ModelWithCorners 𝕜 E H}
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {I'' : ModelWithCorners 𝕜 E'' H''}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold I'' ∞ P]
variable {F : M → N} {G : N → P} {p : M} {x : M}

/- Exercise 3.7 / Proposition 3.6 (1): Lee's differential `dFₚ` is the canonical manifold
derivative, already a continuous linear map on tangent spaces. -/
#check (mfderiv I I' F p :
    TangentSpace I p →L[𝕜] TangentSpace I' (F p)
)

/- Exercise 3.7 / Proposition 3.6 (1): for smooth maps, the source-facing composite rule is the
chapter bridge `mfderiv_comp_of_smooth`, derived from the canonical owner theorem `mfderiv_comp`.
-/
#check (mfderiv_comp_of_smooth :
    ContMDiff I I' ∞ F → ContMDiff I' I'' ∞ G →
    mfderiv I I'' (G ∘ F) p = (mfderiv I' I'' G (F p)).comp (mfderiv I I' F p)
)

/- Exercise 3.7 / Proposition 3.6 (3): the differential of the identity is the identity linear
map on the tangent space. -/
#check (mfderiv_id :
    mfderiv I I (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace I x)
)

end CompositionAndIdentity

section Diffeomorphisms

universe u𝕜 uE uE' uH uH' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H}
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {n : ℕ∞ω}
variable (Φ : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0) (x : M)

/- Exercise 3.7 / Proposition 3.6 (2): the differential of a `C^n` diffeomorphism is the
forward map of the canonical tangent-space equivalence. -/
#check (Φ.mfderivToContinuousLinearEquiv hn x :
    TangentSpace I x ≃L[𝕜] TangentSpace I' (Φ x)
)

/- Exercise 3.7 / Proposition 3.6 (2): coercing that tangent-space equivalence back to a
continuous linear map recovers the manifold derivative. -/
#check (Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ hn :
    ↑(Φ.mfderivToContinuousLinearEquiv hn x) = mfderiv I I' Φ x
)

/- Exercise 3.7 / Proposition 3.6 (3): the inverse-differential statement is the chapter bridge
built from the canonical owner `Diffeomorph.mfderivToContinuousLinearEquiv`. -/
#check (diffeomorph_mfderiv_symm_eq_symm Φ hn x :
    mfderiv I' I Φ.symm (Φ x) =
      ((Φ.mfderivToContinuousLinearEquiv hn x).symm :
        TangentSpace I' (Φ x) →L[𝕜] TangentSpace I x)
)

end Diffeomorphisms
