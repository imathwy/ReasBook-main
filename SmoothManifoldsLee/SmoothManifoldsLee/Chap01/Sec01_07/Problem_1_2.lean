import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Topology

/-- Problem 1-2 (1): every point of the disjoint union of copies of `ℝ` lies in the source of a
local chart to `ℝ`, so this disjoint union is locally Euclidean of dimension `1`. -/
-- Proof sketch: for `x = ⟨i, r⟩`, the inclusion
-- `Sigma.mk i : ℝ → Sigma fun j : ι ↦ ℝ` is an open embedding.
-- Its associated open partial homeomorphism has target the `i`-th summand, and the inverse chart
-- is therefore an `OpenPartialHomeomorph (Sigma fun j : ι ↦ ℝ) ℝ` whose source contains `x`.
theorem sigma_real_exists_open_homeomorph {ι : Type u} (x : Sigma fun _ : ι ↦ ℝ) :
    ∃ e : OpenPartialHomeomorph (Sigma fun _ : ι ↦ ℝ) ℝ, x ∈ e.source := by
  rcases x with ⟨i, r⟩
  let σ : ι → Type := fun _ : ι ↦ ℝ
  have hsigmaMk : Topology.IsOpenEmbedding (@Sigma.mk ι σ i) := Topology.IsOpenEmbedding.sigmaMk
  let e : OpenPartialHomeomorph (Sigma σ) ℝ :=
    (hsigmaMk.toOpenPartialHomeomorph (@Sigma.mk ι σ i)).symm
  have hx : @Sigma.mk ι σ i r ∈ e.source := by
    change @Sigma.mk ι σ i r ∈ (hsigmaMk.toOpenPartialHomeomorph (@Sigma.mk ι σ i)).target
    simpa using (Set.mem_range_self r : @Sigma.mk ι σ i r ∈ Set.range (@Sigma.mk ι σ i))
  refine ⟨by simpa [σ] using e, ?_⟩
  simpa [σ] using hx

/- Problem 1-2 (2): the disjoint union of copies of `ℝ` is Hausdorff. -/
recall Sigma.t2Space

/-- Problem 1-2 (3): if the index set is uncountable, then the disjoint union of copies of `ℝ` is
not second-countable. -/
-- Proof sketch: in a second-countable space, any family of pairwise disjoint nonempty open sets is
-- countable. The summand ranges `Set.range (Sigma.mk i)` form such a family in
-- `Sigma fun i : ι ↦ ℝ`, so an
-- uncountable index set contradicts second countability.
theorem sigma_real_not_secondCountableTopology {ι : Type u} [Uncountable ι] :
    ¬ SecondCountableTopology (Sigma fun _ : ι ↦ ℝ) := by
  intro hσ
  letI : SecondCountableTopology (Sigma fun _ : ι ↦ ℝ) := hσ
  let s : ι → Set (Sigma fun _ : ι ↦ ℝ) := fun i ↦ Set.range (Sigma.mk i)
  have hs : Pairwise fun i j ↦ Disjoint (s i) (s j) := fun i j hij ↦ by
    refine Set.disjoint_left.2 fun x hx hx' ↦ hij ?_
    rcases hx with ⟨y, rfl⟩
    rcases hx' with ⟨z, h⟩
    exact (congr_arg Sigma.fst h).symm
  have hcount : Countable ι :=
    hs.countable_of_isOpen_disjoint
      (fun _ ↦ isOpen_range_sigmaMk)
      (fun i ↦ ⟨⟨i, (0 : ℝ)⟩, Set.mem_range_self (0 : ℝ)⟩)
  exact Uncountable.not_countable hcount
