

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_4_43 (from Chap04/Sec04_26) -/
open scoped Manifold

universe u𝕜 uE uH uM uMtilde uE' uH' uM'

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]
variable [ConnectedSpace M]

-- Proof sketch: use the topological existence theorem for universal covering spaces on connected
-- manifolds, transport the smooth atlas along the covering projection to make the universal cover a
-- smooth manifold, and then apply uniqueness of lifts between simply connected covers to upgrade
-- the comparison homeomorphism to a diffeomorphism over the base.
/-- Corollary 4.43: every connected smooth manifold admits a universal smooth covering map from a
simply connected smooth manifold, and any other simply connected smooth covering of the same base
is diffeomorphic to it over the base. -/
theorem exists_universal_smooth_covering_manifold :
    ∃ (Mtilde : Type uMtilde) (_ : TopologicalSpace Mtilde) (_ : ChartedSpace H Mtilde)
      (_ : IsManifold I (⊤ : WithTop ℕ∞) Mtilde) (π : Mtilde → M),
      Manifold.IsUniversalSmoothCoveringMap I I π ∧
        ∀ {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
          {H' : Type uH'} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
          {M' : Type uM'} [TopologicalSpace M'] [ChartedSpace H' M']
          [IsManifold I' (⊤ : WithTop ℕ∞) M']
          (π' : M' → M),
          Manifold.IsUniversalSmoothCoveringMap I' I π' →
            ∃ Φ : Diffeomorph I I' Mtilde M' (⊤ : WithTop ℕ∞), π' ∘ Φ = π := sorry

end
