import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0004_Definition_II_1_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A differential form admits a primitive within `D` at `z` when some open neighborhood of `z`
contained in `D` carries a primitive. -/
def HasPrimitiveWithinAt (D : Set E) (ω : E → E →L[ℝ] G) (z : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ z ∈ U ∧ U ⊆ D ∧ HasPrimitiveOn U ω

-- Proof sketch: choose a ball contained in the open neighborhood from the local primitive witness,
-- then restrict the primitive to that ball.
/-- A local primitive at a point restricts to a primitive on some open ball centered at that point
and contained in the ambient domain. -/
theorem HasPrimitiveWithinAt.exists_ball
    {D : Set E} {ω : E → E →L[ℝ] G} {z : E} (hω : HasPrimitiveWithinAt D ω z) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ D ∧ HasPrimitiveOn (Metric.ball z r) ω := by
  rcases hω with ⟨U, hU_open, hzU, hUD, hU_primitive⟩
  rcases Metric.isOpen_iff.mp hU_open z hzU with ⟨r, hr, hballU⟩
  exact ⟨r, hr, hballU.trans hUD, hU_primitive.mono hballU⟩

/-- A local primitive remains local after composition with a continuous linear map on the target. -/
theorem HasPrimitiveWithinAt.comp
    {D : Set E} {ω : E → E →L[ℝ] G} {z : E} (hω : HasPrimitiveWithinAt D ω z)
    (L : G →L[ℝ] H) :
    HasPrimitiveWithinAt D (fun x ↦ L.comp (ω x)) z := by
  rcases hω with ⟨U, hU_open, hzU, hUD, hU_primitive⟩
  exact ⟨U, hU_open, hzU, hUD, hU_primitive.comp L⟩

/-- Definition II.1-extra-6: a `G`-valued differential form on `D` is closed when every point of
`D` has an open neighborhood inside `D` on which the form has a primitive. -/
def IsClosedOn (ω : E → E →L[ℝ] G) (D : Set E) : Prop :=
  ∀ z ∈ D, HasPrimitiveWithinAt D ω z

/-- Closedness is preserved by composition with a continuous linear map on the target. -/
theorem IsClosedOn.comp
    {D : Set E} {ω : E → E →L[ℝ] G} (hω : IsClosedOn ω D) (L : G →L[ℝ] H) :
    IsClosedOn (fun z ↦ L.comp (ω z)) D := by
  intro z hz
  exact (hω z hz).comp L

-- Proof sketch: from a neighborhood `U` of `z` on which `ω` has a primitive, use openness of `U`
-- to choose a radius `r > 0` with `Metric.ball z r ⊆ U`; restrict the same primitive to that ball.
/-- A closed form admits a primitive on some open disc centered at each point of the domain. -/
theorem IsClosedOn.exists_ball_primitive
    {D : Set E} {ω : E → E →L[ℝ] G} (hω : IsClosedOn ω D) {z : E} (hz : z ∈ D) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ D ∧ HasPrimitiveOn (Metric.ball z r) ω := by
  exact HasPrimitiveWithinAt.exists_ball (hω z hz)
