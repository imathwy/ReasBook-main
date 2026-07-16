import StacksProject_2024.stacks_project.Chap34.Definition_34_10_7
import StacksProject_2024.stacks_project.Chap34.Lemma_34_9_7
import StacksProject_2024.stacks_project.Chap34.Lemma_34_10_2
import StacksProject_2024.stacks_project.Chap34.Lemma_34_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced mathlib's Zariski topology and pretopology owners,
-- while local Chapter 34 files provide the source-facing `IsVCovering`, `IsFpqcCovering`,
-- `FppfCover`, `SyntomicCover`, `Scheme.SmoothCovering`, `Scheme.Cover Scheme.etalePrecoverage`,
-- `Scheme.OpenCover`, and `PhCovering` predicates used below.

variable {T : Scheme.{u}} {ι : Type v}

/-- Lemma 34.10.10 (1): any fpqc covering of a scheme is a `V` covering. -/
@[stacks 0ETK]
theorem isVCovering_of_isFpqcCovering (X : ι → Over T) (hX : IsFpqcCovering X) :
    IsVCovering T (fun i ↦ (X i).left) (fun i ↦ (X i).hom) := sorry

/-- Lemma 34.10.10 (2): any fppf covering of a scheme is a `V` covering. -/
@[stacks 0ETK]
theorem isVCovering_of_fppfCover (cover : FppfCover T) :
    IsVCovering T cover.X cover.f := sorry

/-- Lemma 34.10.10 (3): any syntomic covering of a scheme is a `V` covering. -/
@[stacks 0ETK]
theorem isVCovering_of_syntomicCover (cover : SyntomicCover T) :
    IsVCovering T cover.X cover.f := sorry

/-- Lemma 34.10.10 (4): any smooth covering of a scheme is a `V` covering. -/
@[stacks 0ETK]
theorem isVCovering_of_smoothCovering
    (family : ι → Over T) (hfamily : Scheme.SmoothCovering family) :
    IsVCovering T (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- Lemma 34.10.10 (5): any étale covering of a scheme is a `V` covering. -/
@[stacks 0ETK]
theorem isVCovering_of_etaleCovering (cover : Scheme.Cover Scheme.etalePrecoverage T) :
    IsVCovering T cover.X cover.f := sorry

/-- Lemma 34.10.10 (6): any Zariski covering of a scheme is a `V` covering. -/
@[stacks 0ETK]
theorem isVCovering_of_zariskiCovering (cover : T.OpenCover) :
    IsVCovering T cover.X cover.f := sorry

/-- Lemma 34.10.10 (7): any ph covering of a scheme is a `V` covering. -/
@[stacks 0ETK]
theorem isVCovering_of_phCovering {X : ι → Scheme.{u}} {π : ∀ i, X i ⟶ T}
    (hπ : PhCovering X π) :
    IsVCovering T X π := sorry

end AlgebraicGeometry
