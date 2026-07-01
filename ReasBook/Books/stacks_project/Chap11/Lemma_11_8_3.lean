import Mathlib
import stacks_project.Chap11.Lemma_11_7_4
import stacks_project.Chap11.Theorem_11_8_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for Lemma 11.8.3:
- primary domain: maximal subfields as splitting fields of finite central simple algebras;
- sampled owner declarations:
  `CSA.IsSplitBy`,
  `CSA.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq`,
  `IsMaximalSubfield`,
  `IsMaximalSubfield.finrank_sq`;
- best owner abstraction: `CSA.IsSplitBy` is the core/canonical owner, while `IsMaximalSubfield`
  is the source-facing maximal-subfield hypothesis and this lemma is the bridge from the latter to
  the former;
- primitive data: the maximal subfield `K₀ : Subalgebra k A`, its inclusion `K₀ →ₐ[k] A`, and
  the square-dimension formula from `IsMaximalSubfield.finrank_sq`;
- derived API: the splitting statement for the canonical representative `CSA.mk (AlgCat.of k A)`.

Source/core/bridge triage:
- `source-facing`: this lemma for maximal subfields of a finite central skew field;
- `core/canonical`: `CSA.IsSplitBy`;
- `bridge/view`: the application of Theorem 11.8.2 with the canonical inclusion `K₀ →ₐ[k] A`. -/

section

variable {k : Type u} [Field k]
variable {A : Type v} [DivisionRing A] [Algebra k A] [FiniteDimensional k A]
  [Algebra.IsCentral k A]

-- Proof sketch: apply Theorem 11.8.2 to the central simple algebra underlying `A`, taking
-- `B := A` and the canonical inclusion `K₀ →ₐ[k] A` of the maximal subfield `K₀`. Lemma 11.7.4
-- identifies the finrank hypothesis required by Theorem 11.8.2.
/-- Lemma 11.8.3: if `K₀` is a maximal `k`-subfield of a finite central skew field `A`, then
`K₀` splits the associated finite central simple `k`-algebra. -/
theorem maximal_subfield_splits
    (K₀ : Subalgebra k A) [IsMaximalSubfield K₀] :
    (CSA.mk (AlgCat.of k A)).IsSplitBy K₀ := by
  refine
    ((CSA.mk (AlgCat.of k A)).isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq
      K₀).2 ?_
  refine ⟨CSA.mk (AlgCat.of k A), IsBrauerEquivalent.refl _, ⟨K₀.val⟩, ?_⟩
  simpa using IsMaximalSubfield.finrank_sq K₀

end
