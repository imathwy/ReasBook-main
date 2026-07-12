import Mathlib
import StacksProject_2024.Chap34.Definition_34_3_5
import StacksProject_2024.Chap34.Definition_34_4_1
import StacksProject_2024.Chap34.Definition_34_5_1
import StacksProject_2024.Chap34.Definition_34_6_1
import StacksProject_2024.Chap34.Definition_34_7_1
import StacksProject_2024.Chap34.Definition_34_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical mathlib owners
-- `Scheme.fppfPrecoverage`, `Scheme.fpqcPrecoverage`, and
-- `Scheme.fppfTopology_le_fpqcTopology`; local Chapter 34 precedent fixes the source-facing fpqc
-- owner at `IsFpqcCovering` on indexed families `ι → Over T`.

variable {T : Scheme.{u}} {ι : Type v}

/-- Lemma 34.9.7 (1): any fppf covering of a scheme is an fpqc covering. -/
@[stacks 022C]
theorem isFpqcCovering_of_fppfCover (cover : FppfCover T) :
    IsFpqcCovering (fun i : cover.I₀ ↦ Over.mk (cover.f i)) := sorry

/-- Lemma 34.9.7 (2): any syntomic covering of a scheme is an fpqc covering. -/
@[stacks 022C]
theorem isFpqcCovering_of_syntomicCover (cover : SyntomicCover T) :
    IsFpqcCovering (fun i : cover.I₀ ↦ Over.mk (cover.f i)) := sorry

/-- Lemma 34.9.7 (3): any smooth covering of a scheme is an fpqc covering. -/
@[stacks 022C]
theorem isFpqcCovering_of_smoothCovering
    (family : ι → Over T) (hfamily : Scheme.SmoothCovering family) :
    IsFpqcCovering family := sorry

/-- Lemma 34.9.7 (4): any etale covering of a scheme is an fpqc covering. -/
@[stacks 022C]
theorem isFpqcCovering_of_etaleCovering (cover : Scheme.Cover Scheme.etalePrecoverage T) :
    IsFpqcCovering (fun i : cover.I₀ ↦ Over.mk (cover.f i)) := sorry

/-- Lemma 34.9.7 (5): any Zariski covering of a scheme is an fpqc covering. -/
@[stacks 022C]
theorem isFpqcCovering_of_zariskiCovering (cover : T.OpenCover) :
    IsFpqcCovering (fun i : cover.I₀ ↦ Over.mk (cover.f i)) := sorry

end AlgebraicGeometry
