import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_2_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {B : Type u} [TopologicalSpace B]

open Path.Homotopic.Quotient

/-- Construction 3.8.3: the universal-cover candidate over a basepoint `b` is the total space of
endpoint-fixed homotopy classes of paths in `B` starting at `b`, indexed by their endpoint. -/
abbrev universalCoverCandidate (b : B) : Type u :=
  Σ x : B, Path.Homotopic.Quotient b x

/-- The endpoint of the sigma-point `⟨x, γ⟩` is its index `x`. -/
@[simp] theorem universalCoverCandidate_mk_fst (b : B) {x : B}
    (γ : Path.Homotopic.Quotient b x) :
    (⟨x, γ⟩ : universalCoverCandidate b).1 = x :=
  rfl

/-- The path-class component of the sigma-point `⟨x, γ⟩` is `γ`. -/
@[simp] theorem universalCoverCandidate_mk_snd (b : B) {x : B}
    (γ : Path.Homotopic.Quotient b x) :
    (⟨x, γ⟩ : universalCoverCandidate b).2 = γ :=
  rfl

/-- The canonical sigma-point represented by a path has endpoint `f 1`. -/
-- Proof sketch: the first component of `⟨x, mk f⟩` is definitionally `x`, and `Path.target`
-- identifies `x` with `f 1`.
@[simp] theorem universalCoverCandidate_mk_fst_eq_endpoint (b : B) {x : B} (f : Path b x) :
    (⟨x, mk f⟩ : universalCoverCandidate b).1 = f 1 := by
  simp
