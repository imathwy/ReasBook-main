import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_62.Theorem_8_49

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling pass:
-- * source-facing statement: a finite-dimensional Lie algebra over a characteristic-zero field is
--   Lie-isomorphic to a Lie subalgebra of a matrix Lie algebra;
-- * core/canonical owners inspected: `exists_faithful_finite_dimensional_representation`,
--   `LieModule.toEnd`, `Module.finBasis`, `algEquivMatrix`, `LieEquiv.ofInjective`,
--   `Nonempty (𝔤 ≃ₗ⁅𝕜⁆ 𝔥)`;
-- * bridge used below: the Lie subalgebra image `ρ.range` of the canonical matrix-valued
--   representation obtained from a faithful finite-dimensional representation.

noncomputable section

universe u𝕜 u𝔤

section

variable (𝕜 : Type u𝕜) [Field 𝕜] [CharZero 𝕜]
variable (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] [FiniteDimensional 𝕜 𝔤]

/-- Corollary 8.50: every finite-dimensional Lie algebra over a characteristic-zero field is
Lie-isomorphic to a Lie subalgebra of some matrix Lie algebra `𝔤𝔩(n, 𝕜)` with the commutator
bracket. Lee's statement is the specialization `𝕜 = ℝ`. -/
theorem exists_lie_equiv_matrix_lieSubalgebra :
    ∃ (n : ℕ) (L : LieSubalgebra 𝕜 (Matrix (Fin n) (Fin n) 𝕜)), Nonempty (𝔤 ≃ₗ⁅𝕜⁆ L) := by
  have hrep :
      ∃ (V : Type _) (_ : AddCommGroup V) (_ : Module 𝕜 V) (_ : FiniteDimensional 𝕜 V)
        (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V), LieModule.IsFaithful 𝕜 𝔤 V :=
    exists_faithful_finite_dimensional_representation 𝕜 𝔤
  obtain ⟨V, hVAdd, hVModule, hVFinite, hVRingModule, hVLieModule, hfaithful⟩ := hrep
  letI := hVAdd
  letI := hVModule
  letI := hVFinite
  letI := hVRingModule
  letI := hVLieModule
  let e : Module.End 𝕜 V ≃ₗ⁅𝕜⁆ Matrix (Fin (Module.finrank 𝕜 V)) (Fin (Module.finrank 𝕜 V)) 𝕜 :=
    (algEquivMatrix (Module.finBasis 𝕜 V)).toLieEquiv
  let ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin (Module.finrank 𝕜 V)) (Fin (Module.finrank 𝕜 V)) 𝕜 :=
    e.toLieHom.comp (LieModule.toEnd 𝕜 𝔤 V)
  have htoEnd : Function.Injective (LieModule.toEnd 𝕜 𝔤 V) := by
    letI := hfaithful
    exact LieModule.IsFaithful.injective_toEnd
  have hρ : Function.Injective ρ := e.injective.comp htoEnd
  exact ⟨Module.finrank 𝕜 V, ρ.range, ⟨LieEquiv.ofInjective ρ hρ⟩⟩

end
