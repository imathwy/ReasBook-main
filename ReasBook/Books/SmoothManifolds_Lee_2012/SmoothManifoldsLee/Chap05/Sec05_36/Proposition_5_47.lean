import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_37.Problem_5_21

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` did not surface a matching mathlib regular-domain
-- theorem, so this proposition reuses the local Chapter 5 owners already formalized in
-- `Problem_5_21`.

/- Proposition 5.47 (1): for a smooth function `f : M → ℝ`, the closed sublevel set
`f ⁻¹' Set.Iic b` of any regular value `b` admits a smooth manifold-with-boundary structure making
it a regular domain in `M`. This is exactly
`regularSublevel_preimage_exists_regularDomain`. -/
#check regularSublevel_preimage_exists_regularDomain

/- Proposition 5.47 (2): if `a < b` are regular values of a smooth function `f : M → ℝ`, then
the closed strip `f ⁻¹' Set.Icc a b` admits a smooth manifold-with-boundary structure making it a
regular domain in `M`. This is exactly
`regularClosedInterval_preimage_exists_regularDomain`. -/
#check regularClosedInterval_preimage_exists_regularDomain
