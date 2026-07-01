import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.2-extra-4: a complete or maximal smooth atlas is the maximal atlas attached to a
charted space and structure groupoid; its members are exactly the charts smoothly compatible with
every chart in the given atlas. This is the core owner abstraction; the manifold-specialized
bridge is `IsManifold.maximalAtlas`. -/
recall StructureGroupoid.maximalAtlas
