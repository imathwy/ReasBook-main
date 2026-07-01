import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 15.20: For a family `F : ι → E → ℝ` of real-valued functions on a metric space `E`,
the textbook notion of being uniformly equicontinuous is the canonical mathlib predicate
`UniformEquicontinuous F`. In the metric-space case, this means that for every `ε > 0` there
exists `δ > 0` such that `|F i t - F i s| < ε` for all indices `i` and all `s, t : E` with
`dist s t < δ`. -/
recall UniformEquicontinuous
