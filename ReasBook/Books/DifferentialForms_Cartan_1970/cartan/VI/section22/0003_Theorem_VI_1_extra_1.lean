import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

-- Semantic recall note: the canonical owner for this source-facing open-mapping statement is
-- mathlib's `AnalyticOnNhd.is_constant_or_isOpen`.

/-- Theorem VI.1-extra-1. If `f` is holomorphic on a preconnected open set `D ⊆ ℂ` and is not
constant on `D`, then the image `f '' D` is an open set of the complex plane. With the
nonconstancy hypothesis, this is equivalent to the usual connected-open-set formulation. -/
theorem complex_holomorphic_image_isOpen
    {D : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) (hD_open : IsOpen D)
    (hD_preconnected : IsPreconnected D) (h_nonconst : ¬ ∃ w : ℂ, ∀ z ∈ D, f z = w) :
    IsOpen (f '' D) :=
  (hf.is_constant_or_isOpen hD_preconnected).resolve_left h_nonconst
    D subset_rfl hD_open
