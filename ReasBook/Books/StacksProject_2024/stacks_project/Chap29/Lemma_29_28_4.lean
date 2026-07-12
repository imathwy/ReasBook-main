import StacksProject_2024.Chap29.Definition_29_28_4

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` was unavailable here because the semantic endpoint returned HTTP 429;
- local project precedent now exposes the pointwise fibre-dimension owner
  `Scheme.Hom.fiberDimensionAt` and its cutoff locus `Scheme.Hom.fiberDimensionLELocus` in
  `Chap29/Definition_29_28_4.lean`, while `Chap10/Lemma_10_123_13.lean` uses the mathlib-style
  scheme surface `Scheme.Hom.isOpen_*` for openness loci. The declaration below is the openness
  companion for that source-facing locus.
-/

variable {X S : Scheme.{u}}

/-- Lemma 29.28.4: if `f : X ⟶ S` is locally of finite type, then the set of points `x ∈ X` such
that the fiber dimension `dim_x X_{f(x)}` is at most `n` is open. -/
@[stacks 02FZ]
theorem isOpen_fiberDimensionLELocus (f : X ⟶ S) [LocallyOfFiniteType f] (n : ℕ) :
    IsOpen (f.fiberDimensionLELocus n) := sorry

end Scheme.Hom

end AlgebraicGeometry
