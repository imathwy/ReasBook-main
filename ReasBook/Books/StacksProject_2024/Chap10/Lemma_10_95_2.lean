import Mathlib
import StacksProject_2024.Chap10.Definition_10_84_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

namespace Module

omit [Module.FaithfullyFlat R S] in
/-- Helper for Lemma 10.95.2: a finite sum of pure tensors whose module factors lie in a set `u`
belongs to the base change of the span of `u`. -/
lemma sum_tmul_mem_baseChange_span_of_range_subset
    {u : Set M} {k : ℕ} (a : Fin k → S) (m : Fin k → M) (hm : ∀ j, m j ∈ u) :
    (∑ j, a j ⊗ₜ[R] m j) ∈ (Submodule.span R u).baseChange S := by
  -- Each pure tensor lands in the base change because its module factor lies in the chosen span.
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  exact Submodule.tmul_mem_baseChange_of_mem (a j) (Submodule.subset_span (hm j))

omit [Module.FaithfullyFlat R S] in
/-- Helper for Lemma 10.95.2: if the base change of a submodule is all of `S ⊗[R] M`, then the
tensor product of the inclusion map is surjective. -/
lemma subtype_lTensor_surjective_of_baseChange_eq_top
    (P : Submodule R M) (hP : P.baseChange S = ⊤) :
    Function.Surjective (P.subtype.lTensor S) := by
  have hP_range : LinearMap.range (P.subtype.baseChange S) = ⊤ := by
    -- The definition of `baseChange` is the range of the tensorized inclusion.
    simpa [Submodule.baseChange] using hP
  have hsurj_baseChange : Function.Surjective (P.subtype.baseChange S) := by
    -- A linear map is surjective precisely when its range is `⊤`.
    rw [← LinearMap.range_eq_top]
    exact hP_range
  -- The tensorized inclusion is definitionally the base-changed inclusion.
  simpa [LinearMap.baseChange_eq_ltensor] using hsurj_baseChange

/-- Helper for Lemma 10.95.2: faithful flatness reflects the fact that a submodule with full base
change is already the whole module. -/
lemma submodule_eq_top_of_baseChange_eq_top
    (P : Submodule R M) (hP : P.baseChange S = ⊤) :
    P = ⊤ := by
  have hsurjTensor : Function.Surjective (P.subtype.lTensor S) :=
    subtype_lTensor_surjective_of_baseChange_eq_top (R := R) (S := S) P hP
  have hsurj : Function.Surjective P.subtype := by
    simpa using
      (Module.FaithfullyFlat.lTensor_surjective_iff_surjective
        (R := R) (M := S) (f := P.subtype)).mp hsurjTensor
  -- Surjectivity of the subtype map says that every element of `M` already lies in `P`.
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨y, rfl⟩ := hsurj x
  exact y.2

/-- Lemma 10.95.2: if the faithfully flat base change `S ⊗[R] M` is spanned over `S` by a
countable subset, then `M` is spanned over `R` by a countable subset. This is the canonical Lean
form of the textbook statement that countable generation descends from `M ⊗_R S`. -/
theorem countablyGenerated_of_countablyGenerated_tensorProduct_of_faithfullyFlat
    (h : CountablyGenerated S (S ⊗[R] M)) :
    CountablyGenerated R M := by
  classical
  rw [Module.countablyGenerated_iff] at h ⊢
  rcases h with ⟨s, hs, hspan⟩
  have hdecomp (x : s) : ∃ k : ℕ, ∃ a : Fin k → S, ∃ m : Fin k → M,
      x.1 = ∑ j, a j ⊗ₜ[R] m j := by
    -- Decompose each chosen tensor generator into a finite sum of pure tensors.
    simpa using TensorProduct.exists_sum_tmul_eq x.1
  choose k a m hm using hdecomp
  let u : Set M := ⋃ x : s, Set.range (m x)
  let P : Submodule R M := Submodule.span R u
  have hu : u.Countable := by
    -- The module factors form a countable union of finite ranges indexed by the countable set `s`.
    letI : Countable s := hs.to_subtype
    simpa [u] using Set.countable_iUnion (fun x : s ↦ Set.countable_range (m x))
  have hs_subset : s ⊆ P.baseChange S := by
    intro y hy
    let x : s := ⟨y, hy⟩
    have hm_mem : ∀ j, m x j ∈ u := by
      intro j
      exact Set.mem_iUnion.2 ⟨x, Set.mem_range_self j⟩
    have hx_mem : (∑ j, a x j ⊗ₜ[R] m x j) ∈ P.baseChange S := by
      -- Every summand belongs to the base change of `P`, so the whole finite sum does as well.
      simpa [P] using
        sum_tmul_mem_baseChange_span_of_range_subset
          (R := R) (S := S) (u := u) (a := a x) (m := m x) hm_mem
    have hx' : x.1 ∈ P.baseChange S := by
      -- Rewrite the chosen tensor decomposition back to the original generator.
      rw [hm x]
      exact hx_mem
    -- Replacing the generator by its chosen tensor decomposition puts it into `P.baseChange S`.
    simpa [x] using hx'
  have hP : P.baseChange S = ⊤ := by
    -- Since `s` spans the tensor product and every generator lies in `P.baseChange S`,
    -- the base-changed submodule is the whole tensor product.
    apply eq_top_iff.mpr
    rw [← hspan]
    exact Submodule.span_le.2 hs_subset
  refine ⟨u, hu, ?_⟩
  -- Faithful flatness descends the equality `P.baseChange S = ⊤` back to `P = ⊤`.
  simpa [P] using
    submodule_eq_top_of_baseChange_eq_top (R := R) (S := S) (M := M) P hP

end Module

end
