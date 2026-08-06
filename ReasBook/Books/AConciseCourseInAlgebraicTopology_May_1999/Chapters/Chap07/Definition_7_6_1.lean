import Mathlib.Topology.ContinuousMap.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Problem_5_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_1_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

-- This item uses the set-theoretic fiber `p ⁻¹' {b}` together with its canonical continuous
-- inclusion. Although the source introduces this for fibrations, the construction itself depends
-- only on the continuous map `p`.

/-- Definition 7.6.1: for a continuous map `p : C(E, B)` and `b : B`, the fiber `F_b` is the
preimage `p ⁻¹' ({b} : Set B)` of `b`. In particular, this is the source-facing fiber used later
for fibrations. -/
abbrev fiber (p : C(E, B)) (b : B) : Set E :=
  p ⁻¹' ({b} : Set B)

/-- A fiber of a map between May spaces is a closed subspace, hence is again compactly generated
weak Hausdorff with its ordinary subtype topology. -/
instance fiberCompactlyGeneratedWeakHausdorffSpace
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
    [CompactlyGeneratedWeakHausdorffSpace.{v, v} B]
    (p : C(E, B)) (b : B) :
    CompactlyGeneratedWeakHausdorffSpace.{u, u} (fiber p b) := by
  have hclosed : IsClosed (fiber p b) :=
    (isClosed_singleton : IsClosed ({b} : Set B)).preimage p.continuous
  let _ : WeaklyHausdorffSpace.{u, u} (fiber p b) :=
    Subtype.weaklyHausdorffSpace
  let _ : UCompactlyGeneratedSpace.{u} (fiber p b) :=
    Subtype.uCompactlyGeneratedSpaceOfIsClosed hclosed
  infer_instance

/-- The inclusion `i_b : fiber p b ⟶ E` of the fiber over `b` into `E`. -/
def fiberInclusion (p : C(E, B)) (b : B) : C(fiber p b, E) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- `fiberInclusion p b` is the canonical continuous subtype inclusion. -/
theorem fiberInclusion_def (p : C(E, B)) (b : B) :
    fiberInclusion p b = ⟨Subtype.val, continuous_subtype_val⟩ := rfl

/-- Composing the fiber inclusion with `p` gives the constant map at the basepoint `b`. -/
@[simp] theorem comp_fiberInclusion (p : C(E, B)) (b : B) :
    p.comp (fiberInclusion p b) = ContinuousMap.const (fiber p b) b := by
  ext x
  exact Set.mem_singleton_iff.mp x.2

/-- A point of `E` lies in `fiber p b` exactly when `p` sends it to `b`. -/
@[simp] theorem mem_fiber_iff (p : C(E, B)) (b : B) (e : E) :
    e ∈ fiber p b ↔ p e = b := Iff.rfl

/-- Applying `fiberInclusion p b` to a fiber point returns its underlying point of `E`. -/
@[simp] theorem fiberInclusion_apply (p : C(E, B)) (b : B) (x : fiber p b) :
    fiberInclusion p b x = x.1 := rfl
