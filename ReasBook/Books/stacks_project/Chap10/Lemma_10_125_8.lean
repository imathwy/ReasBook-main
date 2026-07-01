import Mathlib
import stacks_project.Chap10.Lemma_10_125_7

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]

/- 
Domain-style sampling:
- primary domain: source-facing loci on `Spec(S)` cut out by local fiber invariants of a finite
  presentation ring map, together with their topological finiteness properties;
- sampled owner declarations of the same kind:
  `relativeDimensionAtLELocus`,
  `exists_openNhdsOf_mem_relativeDimensionAtLELocus`,
  `Module.flatOverBaseLocus`,
  `Module.isOpen_flatOverBaseLocus_of_finitePresentation`;
- best owner abstraction: the named locus owner `relativeDimensionAtLELocus`; openness and
  quasi-compactness are derived API of that owner rather than new primitive data;
- primitive data: the finite presentation map `R → S` and the bound `n`;
- derived API: the open and compactness statements for the owner locus.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the bounded relative-dimension locus is open and
  quasi-compact;
- `core/canonical`: the owner `relativeDimensionAtLELocus R S n`;
- `bridge/view`: the separate `IsOpen` and `IsCompact` companion theorems below.
-/

-- Proof sketch: openness is exactly the local neighborhood criterion from
-- `exists_openNhdsOf_mem_relativeDimensionAtLELocus`.
/-- The locus where the relative dimension of a finitely presented algebra is at most `n` is open
in `Spec(S)`. -/
theorem isOpen_relativeDimensionAtLELocus_of_finitePresentation (n : ℕ) :
    IsOpen (relativeDimensionAtLELocus R S n) := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  rcases exists_openNhdsOf_mem_relativeDimensionAtLELocus n q hq with ⟨U, hU⟩
  exact Filter.mem_of_superset (U.isOpen.mem_nhds U.mem) hU

-- Proof sketch: descend the finite presentation to a finite type `ℤ`-model, identify the locus by
-- `relativeDimensionAt_le_preimage_eq_baseChange`, and use quasi-compactness of open subsets of the
-- Noetherian spectrum downstairs.
/-- The locus where the relative dimension of a finitely presented algebra is at most `n` is
quasi-compact in `Spec(S)`. -/
theorem isCompact_relativeDimensionAtLELocus_of_finitePresentation (n : ℕ) :
    IsCompact (relativeDimensionAtLELocus R S n) := sorry

-- Proof sketch: openness is the pointwise neighborhood statement of Lemma `10.125.6`. For
-- quasi-compactness, descend the finite presentation to a finitely generated `ℤ`-subalgebra of
-- the source, identify the locus with the inverse image of the corresponding locus after base
-- change using Lemma `10.125.7`, and use that open subsets of the Noetherian spectrum downstairs
-- are quasi-compact.
/-- Lemma 10.125.8: if `R → S` is of finite presentation, then the locus
`{ q ∈ Spec(S) | dim_q(S/R) ≤ n }` is an open and quasi-compact subset of `Spec(S)`. -/
theorem isOpen_isCompact_relativeDimensionAtLELocus_of_finitePresentation (n : ℕ) :
    IsOpen (relativeDimensionAtLELocus R S n) ∧
      IsCompact (relativeDimensionAtLELocus R S n) :=
  ⟨isOpen_relativeDimensionAtLELocus_of_finitePresentation n,
    isCompact_relativeDimensionAtLELocus_of_finitePresentation n⟩

end
