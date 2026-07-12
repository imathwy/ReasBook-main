import Mathlib
import SmoothManifolds_Lee_2012.Chap05.Sec05_31.Example_5_26

-- Declarations for this item will be appended below by the statement pipeline.

open Topology

/-- Example 5.19: the figure-eight image carries the immersed-submanifold structure coming from its
injective smooth parametrization, but it is not embedded in `ℝ²` because the inclusion does not
have the subspace-topology embedding property. -/
-- Proof sketch: the immersed structure is the canonical owner-side object
-- `figureEightCurveImmersedSubmanifold = figureEightCurve_isImmersion.toImmersedSubmanifold
--   figureEightCurve_injective`;
-- its inclusion map is exactly the figure-eight parametrization, which is not an embedding by
-- Example 4.19.
theorem figureEightCurve_image_is_immersed_not_embedded :
    ¬ IsEmbedding figureEightCurveImmersedSubmanifold.inclusion := by
  simpa [figureEightCurveImmersedSubmanifold] using figureEightCurve_not_isEmbedding
