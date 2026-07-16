import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_84_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance high] Algebra.TensorProduct.leftAlgebra Algebra.toModule

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.95.4: base change is monotone with respect to inclusion of
`R`-submodules. -/
lemma baseChange_mono {P P' : Submodule R M} (h : P ≤ P') :
    P.baseChange S ≤ P'.baseChange S := by
  -- Rewrite both base changes as spans of pure tensors so monotonicity reduces to `span_mono`.
  rw [Submodule.baseChange_eq_span (A := S), Submodule.baseChange_eq_span (A := S)]
  refine Submodule.span_mono ?_
  intro z hz
  rcases hz with ⟨m, hm, rfl⟩
  exact ⟨m, h hm, rfl⟩

/-- Helper for Lemma 10.95.4: every tensor lies in the base change of the span of finitely many
module elements. -/
lemma exists_finset_span_mem_baseChange (y : S ⊗[R] M) :
    ∃ s : Finset M, y ∈ (Submodule.span R (s : Set M)).baseChange S := by
  classical
  -- Expand the tensor as a finite sum of pure tensors and keep only the module components.
  obtain ⟨t, ht⟩ := TensorProduct.exists_finset (R := R) y
  refine ⟨t.image Prod.snd, ?_⟩
  rw [ht]
  refine Submodule.sum_mem _ ?_
  intro p hp
  have hp_mem : p.2 ∈ Submodule.span R (t.image Prod.snd : Set M) := by
    apply Submodule.subset_span
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem Prod.snd hp)
  exact Submodule.tmul_mem_baseChange_of_mem (R := R) (A := S) p.1 hp_mem

/-- Helper for Lemma 10.95.4: the span of a countable subset is countably generated. -/
lemma countablyGenerated_span_of_countable {s : Set M} (hs : s.Countable) :
    (Submodule.span R s).CountablyGenerated := by
  -- This is exactly the defining formulation of countable generation for submodules.
  rw [Submodule.countablyGenerated_iff]
  exact ⟨s, hs, rfl⟩

-- Proof sketch: choose countably many generators for `Q`, write each generator as a finite sum of
-- pure tensors, and let `P` be the submodule spanned by all module components appearing in those
-- sums. This spanning set is still countable, and every generator of `Q` lies in `P.baseChange S`,
-- hence the whole submodule `Q` is contained in `P.baseChange S`.
/-- Lemma 10.95.4: every countably generated `S`-submodule `Q` of the scalar extension
`S ⊗[R] M` is contained in the base change of a countably generated `R`-submodule `P ≤ M`. This
is the canonical Lean form of saying that the image of `P ⊗_R S → M ⊗_R S` contains `Q`. -/
@[stacks 05A7]
theorem exists_countablyGenerated_submodule_whose_baseChange_contains
    {Q : Submodule S (S ⊗[R] M)}
    (hQ : Q.CountablyGenerated) :
    ∃ P : Submodule R M, P.CountablyGenerated ∧ Q ≤ P.baseChange S := by
  classical
  rcases (Submodule.countablyGenerated_iff.mp hQ) with ⟨t, ht_countable, ht_span⟩
  let support : S ⊗[R] M → Finset M := fun y ↦
    Classical.choose (exists_finset_span_mem_baseChange (R := R) (S := S) (M := M) y)
  have support_mem :
      ∀ y : S ⊗[R] M, y ∈ (Submodule.span R (support y : Set M)).baseChange S := by
    -- Each chosen support was defined precisely so that it spans a base change containing `y`.
    intro y
    exact Classical.choose_spec
      (exists_finset_span_mem_baseChange (R := R) (S := S) (M := M) y)
  let U : Set M := ⋃ y : t, (support y : Set M)
  let P : Submodule R M := Submodule.span R U
  have hU_countable : U.Countable := by
    -- A countable family of finite supports still has countable union.
    letI : Countable t := ht_countable.to_subtype
    simpa [U] using Set.countable_iUnion (fun y : t ↦ Finset.countable_toSet (support y))
  have hPcg : P.CountablyGenerated := by
    -- The final submodule is spanned by the countable union of all chosen supports.
    exact countablyGenerated_span_of_countable (R := R) (hs := hU_countable)
  have hQle : Q ≤ P.baseChange S := by
    -- It suffices to check the chosen generators of `Q`.
    rw [← ht_span]
    refine Submodule.span_le.2 ?_
    intro y hy
    let y' : t := ⟨y, hy⟩
    have hspan_le : Submodule.span R (support y' : Set M) ≤ P := by
      -- The support of a chosen generator is part of the union used to define `P`.
      refine Submodule.span_mono ?_
      intro m hm
      exact Set.mem_iUnion.2 ⟨y', hm⟩
    have hy_mem : y ∈ (Submodule.span R (support y' : Set M)).baseChange S := by
      -- Reuse the finite-support containment for this specific generator.
      simpa using support_mem y
    exact baseChange_mono (R := R) (S := S) (M := M) hspan_le hy_mem
  exact ⟨P, hPcg, hQle⟩

end
