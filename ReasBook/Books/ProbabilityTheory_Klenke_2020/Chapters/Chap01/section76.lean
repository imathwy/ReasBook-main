import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_76 (from Items/Chap01) -/
universe u

/- Definition 1.76: A map `X : Ω → Ω'` is measurable from `(Ω, 𝓐)` to `(Ω', 𝓐')` in the
textbook sense exactly when it satisfies the canonical mathlib predicate `Measurable X`, meaning
that the preimage of every measurable set in the codomain is measurable in the domain. -/
recall Measurable

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: unfold `Measurable`; for maps into `ℝ`, the codomain measurable space is the
-- Borel `σ`-algebra, so the statement is exactly the specialization of the general definition.
/-- A real-valued map is measurable exactly when the preimage of every Borel subset of `ℝ` is
measurable. -/
theorem measurable_real_map_iff {X : Ω → ℝ} :
    Measurable X ↔ ∀ s : Set ℝ, @MeasurableSet ℝ (borel ℝ) s → MeasurableSet (X ⁻¹' s) :=
  Iff.rfl
