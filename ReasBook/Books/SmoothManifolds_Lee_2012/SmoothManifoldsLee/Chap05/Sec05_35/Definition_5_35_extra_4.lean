import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff
open Manifold

noncomputable section

local notation "Plane" => ℝ × ℝ

namespace Set

/-- A subset of `ℝ²` admits an embedded-curve structure when its subtype carries a smooth
boundaryless `1`-manifold structure for which the inclusion into `ℝ²` is an embedded
submanifold. -/
abbrev AdmitsEmbeddedCurveStructure (S : Set Plane) : Prop :=
  ∃ _ : ChartedSpace ℝ S, ∃ _ : IsManifold 𝓘(ℝ) ⊤ S,
    IsEmbeddedSubmanifold 𝓘(ℝ, Plane) 𝓘(ℝ) S

/-- A subset of `ℝ²` admits an immersed-curve structure with topology `t` when that topology on the
subtype supports a smooth `1`-manifold structure whose inclusion into `ℝ²` is an immersion. -/
abbrev IsImmersedCurveWithTopology (S : Set Plane) (t : TopologicalSpace S) : Prop :=
  let _ : TopologicalSpace S := t
  ∃ _ : ChartedSpace ℝ S, ∃ _ : IsManifold 𝓘(ℝ) ⊤ S,
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane)

/-- A subset of `ℝ²` admits an immersed-curve structure when some topology on its subtype supports
such a smooth immersed-curve structure. -/
abbrev AdmitsImmersedCurveStructure (S : Set Plane) : Prop :=
  ∃ t : TopologicalSpace S, IsImmersedCurveWithTopology S t

end Set
