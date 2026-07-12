import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain sampling:
- primary domain: algebraic elements under scalar-extension maps;
- sampled owner declarations:
  `IsAlgebraic.algebraMap`,
  `IsAlgebraic.algHom`,
  `isAlgebraic_algHom_iff`;
- best owner abstraction: the pointwise owner `IsAlgebraic`, with algebraicity over the base ring
  transported along the canonical algebra map by `IsAlgebraic.algebraMap`;
- primitive data: algebraicity of `x` over `ℚ`;
- derived API: algebraicity of its complex image under `ℚ → ℝ → ℂ`.

Layer triage:
- `source-facing`: the textbook special case for a real algebraic number viewed in `ℂ`;
- `core/canonical`: `IsAlgebraic.algebraMap`;
- `bridge/view`: this theorem, as the `ℝ → ℂ` specialization of the owner theorem. -/

/-- Lemma PI-16: if `x : ℝ` is algebraic over `ℚ`, then its complex image `(x : ℂ)` is
algebraic over `ℚ`. -/
theorem isAlgebraic_rat_complex_ofReal {x : ℝ} (hx : IsAlgebraic ℚ x) :
    IsAlgebraic ℚ (x : ℂ) :=
  hx.algebraMap
