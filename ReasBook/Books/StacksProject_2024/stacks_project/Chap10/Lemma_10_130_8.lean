import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_10_5
import StacksProject_2024.stacks_project.Chap10.Definition_10_104_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_130_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum TopologicalSpace

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

variable [Algebra.FinitePresentation R S] [Module.Flat R S]

/- 
Domain-style sampling for Cohen-Macaulay fiber stratifications:
- primary domain: source-facing strata in `Spec(S)` cut out by the Cohen-Macaulay fiber locus and
  the exact relative fiber dimension, together with the quotient-factor decomposition attached to a
  finite clopen partition;
- sampled declarations of the same kind:
  `cohenMacaulayFiberLocus`,
  `isOpen_cohenMacaulayFiber_and_relativeDimensionAt_eq_of_finitePresentation_flat`,
  `relativeDimensionAt`,
  `exists_product_decomposition_by_dimensionStrata_of_finiteType_cohenMacaulay`;
- best owner abstraction: the source-facing owner is the actual stratum
  `(cohenMacaulayFiberLocus R S) ∩ { q : PrimeSpectrum S | relativeDimensionAt R S q = d }`;
  the product decomposition is only a `bridge/view` built from those strata;
- primitive data: the canonical locus owner `cohenMacaulayFiberLocus R S`, the pointwise
  invariant `relativeDimensionAt R S q`, and the flat finitely presented map `R → S`;
- derived API: openness of each stratum, finiteness of the nonempty strata, and the quotient
  factors whose spectra identify with those exact strata.

Source/core/bridge triage:
- `source-facing`: the exact Cohen-Macaulay fiber dimension-`d` stratum on `Spec(S)`;
- `core/canonical`: `cohenMacaulayFiberLocus`, `relativeDimensionAt`, `EquidimensionalSpace`, and
  `zeroLocus`;
- `bridge/view`: quotient ideals `I d` together with an `AlgEquiv` from `S` to the finite product
  of the corresponding quotient factors.
-/

-- Proof sketch: for each `d`, let `W d ⊆ Spec(S)` be the open locus from Lemma `10.130.4`
-- where the fiber local rings are Cohen-Macaulay and have relative dimension `d`. These opens are
-- pairwise disjoint and cover `Spec(S)`. Apply Lemma `10.24.3` repeatedly to the finite clopen
-- partition by the nonempty `W d` to obtain idempotents and hence a finite product decomposition
-- of `S` into quotient factors. Each factor is supported on one stratum, so its fibers remain
-- Cohen-Macaulay and equidimensional; when a fiber is nonempty, its Krull dimension is the
-- indexed dimension.
/-- Lemma 10.130.8: if `R → S` is flat and of finite presentation with Cohen-Macaulay fibers, then
`S` admits a finite product decomposition into quotient `R`-algebras indexed by the occurring
fiber dimensions. The `d`-th quotient factor cuts out exactly the nonempty stratum
`cohenMacaulayFiberLocus R S ∩
  { q : PrimeSpectrum S | relativeDimensionAt R S q = d }`,
and is again flat and finitely presented over `R` with Cohen-Macaulay fibers that are
equidimensional of Krull dimension `d` whenever the fiber is nonempty. -/
theorem exists_product_decomposition_by_pure_fiber_dimension_of_finitePresentation_flat
    (hCM : ∀ p : PrimeSpectrum R, CohenMacaulayRing (p.asIdeal.Fiber S)) :
    ∃ (D : Finset ℕ) (I : D → Ideal S) (e : S ≃ₐ[R] ((d : D) → S ⧸ I d)),
      (∀ d : D,
        cohenMacaulayFiberLocus R S ∩
            { q : PrimeSpectrum S | relativeDimensionAt R S q = ((d : ℕ) : WithBot ℕ∞) } =
          zeroLocus (I d : Set S)) ∧
        ∀ d : D,
          Set.Nonempty
              (cohenMacaulayFiberLocus R S ∩
                { q : PrimeSpectrum S | relativeDimensionAt R S q = ((d : ℕ) : WithBot ℕ∞) }) ∧
            Algebra.FinitePresentation R (S ⧸ I d) ∧
              Module.Flat R (S ⧸ I d) ∧
                ∀ p : PrimeSpectrum R,
                  CohenMacaulayRing (p.asIdeal.Fiber (S ⧸ I d)) ∧
                    EquidimensionalSpace (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ I d))) ∧
                      Nonempty (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ I d))) →
                        ringKrullDim (p.asIdeal.Fiber (S ⧸ I d)) = (d : ℕ) := sorry

end
