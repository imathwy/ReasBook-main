import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap02.Definition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 2.1 lies in the dual-norm domain for separated seminorms on finite-dimensional real
inner-product spaces.

Sampled owner-style declarations:
* mathlib `Seminorm.closedBall_zero_eq`
* `Seminorm.IsNorm` in `Definition_2_5`
* `Seminorm.dualNorm` in `Definition_2_5`
* `Seminorm.inner_le_dualNorm_mul` in `Definition_2_5`

Best owner abstraction:
* `Seminorm.dualNorm p`

Primitive data:
* a seminorm `p : Seminorm ℝ E`
* a finite-dimensional real inner-product-space structure on `E`
* the separation hypothesis `[Seminorm.IsNorm p]`

Derived API:
* the support-function formula `Seminorm.dualNorm_apply`
* the pairing estimate `Seminorm.inner_le_dualNorm_mul`

Source/core/bridge triage:
* source-facing: Proposition 2.1, the textbook pairing estimate for a norm and its dual norm
* core/canonical: `Seminorm.inner_le_dualNorm_mul` as a direct companion theorem of
  `Seminorm.dualNorm`
* bridge/view: `Seminorm.dualNorm_apply`

The pairing estimate is derived API of the dual-norm owner, so the theorem now lives in
`Definition_2_5` next to `Seminorm.dualNorm`. This numbered item is therefore a direct recall,
not a second owner file. -/

/- Proposition 2.1 is the direct owner recall of the dual-pairing estimate attached to
`Seminorm.dualNorm`. -/
#check Seminorm.inner_le_dualNorm_mul
