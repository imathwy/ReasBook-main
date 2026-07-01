import Mathlib
import stacks_project.Chap05.Definition_5_10_5
import stacks_project.Chap10.Definition_10_104_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum TopologicalSpace

namespace PrimeSpectrum

section

variable (S : Type v) [CommRing S]

/-- The dimension-`d` stratum of `Spec(S)`, defined by local Krull dimension. The source uses the
dimension stratification itself, not an auxiliary finite package, so this set is the source-facing
owner for Lemma `10.114.7`. -/
def dimensionStratum (d : ℕ) : Set (PrimeSpectrum S) :=
  { x | topologicalKrullDimAt x = d }

@[simp] theorem mem_dimensionStratum (x : PrimeSpectrum S) (d : ℕ) :
    x ∈ dimensionStratum S d ↔ topologicalKrullDimAt x = d :=
  Iff.rfl

theorem disjoint_dimensionStratum_of_ne {d e : ℕ} (hde : d ≠ e) :
    Disjoint (dimensionStratum S d) (dimensionStratum S e) := by
  rw [Set.disjoint_left]
  intro x hx he
  exact hde (by simpa using hx.symm.trans he)

end

end PrimeSpectrum

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [CohenMacaulayRing S]

/- Domain-style sampling for finite-type Cohen-Macaulay spectra by dimension:
- primary domain: topological dimension strata in `Spec(S)` and clopen/product decompositions of
  affine schemes;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`,
  `topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtMaximal`,
  `TopologicalSpace.EquidimensionalSpace`,
  `exists_idempotent_partition_of_isCompl_open`,
  `exists_product_decomposition_by_pure_fiber_dimension_of_finitePresentation_flat`;
- best owner abstraction: the source-facing owner is the actual dimension-`d` stratum
  `{x : Spec(S) | topologicalKrullDimAt x = d}`; the product decomposition is only a
  `bridge/view` built from those strata;
- primitive data: the stratum itself, defined from the canonical owner `topologicalKrullDimAt`;
- derived API: clopen-ness, disjointness, equidimensionality, dimension equalities, finiteness of
  the nonempty strata, and the quotient-factor decomposition attached to them.

Source/core/bridge triage:
* `source-facing`: `PrimeSpectrum.dimensionStratum S d`;
* `core/canonical`: `topologicalKrullDimAt`, `EquidimensionalSpace`, and clopen subsets of
  `Spec(S)`;
* `bridge/view`: quotient ideals `I` with `zeroLocus (I : Set S) = dimensionStratum S d`, and the
  resulting `AlgEquiv` product decomposition of `S`.
-/

-- Proof sketch: for each point `x : Spec(S)`, Lemmas `10.114.5` and `10.114.6` identify
-- `topologicalKrullDimAt x` with the common dimension of the irreducible components through `x`,
-- equivalently with the Krull dimensions of maximal localizations above `x`. In a
-- Cohen-Macaulay finite-type algebra over a field, irreducible components that meet have the same
-- dimension, so the dimension-`d` locus is a union of connected components and hence clopen.
/-- For a finite type Cohen-Macaulay algebra over a field, the dimension-`d` stratum of `Spec(S)`
is open and closed. -/
theorem isClopen_dimensionStratum_of_finiteType_cohenMacaulay (d : ℕ) :
    IsClopen (PrimeSpectrum.dimensionStratum S d) := sorry

-- Proof sketch: every irreducible component of the clopen stratum inherits the same local
-- dimension value `d`, so the stratum is equidimensional; if the stratum is nonempty, its common
-- topological Krull dimension is exactly `d`.
/-- Every nonempty dimension-`d` stratum of `Spec(S)` is equidimensional of dimension `d`. -/
theorem equidimensionalSpace_dimensionStratum_of_finiteType_cohenMacaulay (d : ℕ) :
    EquidimensionalSpace (PrimeSpectrum.dimensionStratum S d) := sorry

/-- If the dimension-`d` stratum of `Spec(S)` is nonempty, then its topological Krull dimension is
`d`. -/
theorem topologicalKrullDim_dimensionStratum_of_finiteType_cohenMacaulay {d : ℕ}
    (hd : (PrimeSpectrum.dimensionStratum S d).Nonempty) :
    topologicalKrullDim (PrimeSpectrum.dimensionStratum S d) = d := sorry

-- Proof sketch: every point of `Spec(S)` lies in the unique stratum corresponding to its local
-- Krull dimension, and only finitely many local dimensions occur because `Spec(S)` has finitely
-- many irreducible components.
/-- The nonempty dimension strata of `Spec(S)` form a finite clopen partition. -/
theorem finite_nonempty_dimensionStrata_of_finiteType_cohenMacaulay :
    { d : ℕ | (PrimeSpectrum.dimensionStratum S d).Nonempty }.Finite := sorry

/-- The dimension strata cover `Spec(S)`. -/
theorem iUnion_dimensionStratum_of_finiteType_cohenMacaulay :
    (⋃ d : ℕ, PrimeSpectrum.dimensionStratum S d) = Set.univ := sorry

-- Proof sketch: apply the clopen stratification theorem to write `Spec(S)` as a finite disjoint
-- union of the nonempty `PrimeSpectrum.dimensionStratum S d`. Repeatedly apply the standard
-- correspondence between clopen subsets of `Spec(S)` and quotient factors of `S`. The resulting
-- quotient ideal `I d` cuts out exactly the dimension-`d` stratum, so the product decomposition is
-- a bridge from the source-facing strata to the canonical quotient factors.
/-- A finite type Cohen-Macaulay algebra over a field is a finite product of quotient factors
indexed by the nonempty dimension strata of `Spec(S)`. The `d`-th quotient factor cuts out exactly
the stratum `PrimeSpectrum.dimensionStratum S d`, and is again Cohen-Macaulay and equidimensional
of Krull dimension `d`. -/
theorem exists_product_decomposition_by_dimensionStrata_of_finiteType_cohenMacaulay :
    ∃ (D : Finset ℕ) (I : D → Ideal S) (e : S ≃ₐ[k] ∀ d : D, S ⧸ I d),
      (∀ d : D,
        PrimeSpectrum.dimensionStratum S (d : ℕ) = zeroLocus (I d : Set S)) ∧
        ∀ d : D,
          (PrimeSpectrum.dimensionStratum S (d : ℕ)).Nonempty ∧
            CohenMacaulayRing (S ⧸ I d) ∧
              EquidimensionalSpace (PrimeSpectrum (S ⧸ I d)) ∧
              ringKrullDim (S ⧸ I d) = (d : ℕ) := sorry

end
