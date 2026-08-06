import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Problem_10_8_5

open AlgebraicTopology Topology
open scoped Topology.CWComplex

universe u

noncomputable section

-- Source-facing theorem with the Chapter 10 finite-CW Euler characteristic owner and the
-- canonical singular-chain complex owner `HomologicalComplex.homologyEulerChar`.

/-- Helper for Problem 13.6.1: a finite CW complex has no cells in sufficiently large
dimension. -/
theorem existsCellCutoff
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    [CWComplex.Finite (Set.univ : Set X)] :
    ∃ N : ℕ, ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n) := by
  -- Convert the eventual vanishing of cells from `CWComplex.Finite` into a concrete cutoff.
  have hfinite : ∀ᶠ n in Filter.atTop, IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n) :=
    (inferInstance : CWComplex.Finite (Set.univ : Set X)).eventually_isEmpty_cell
  simpa [Filter.eventually_atTop, ge_iff_le] using hfinite

/-- Helper for Problem 13.6.1: isomorphic field-valued chain complexes have the same homological
Euler characteristic. -/
theorem homologyEulerChar_eq_ofIso
    (k : Type u) [Field k] {C D : ChainComplex (ModuleCat.{u} k) ℕ} (e : C ≅ D) :
    HomologicalComplex.homologyEulerChar C = HomologicalComplex.homologyEulerChar D := by
  -- Compare the degreewise homology ranks through the homology isomorphisms induced by `e`.
  have hFinrank :
      (fun n ↦ Module.finrank k (C.homology n)) =
        fun n ↦ Module.finrank k (D.homology n) := by
    funext n
    simpa using
      LinearEquiv.finrank_eq
        (((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n).mapIso
          e).toLinearEquiv)
  -- Then unfold the Euler characteristic and rewrite the summands pointwise.
  simpa [HomologicalComplex.homologyEulerChar] using
    congrArg
      (fun f : ℕ → ℕ ↦
        ∑ᶠ n : ℕ, (((ComplexShape.down ℕ).χ n : ℤ) * f n))
      hFinrank

/-- Helper for Problem 13.6.1: if a finite-dimensional field-valued chain complex is already
known to have Euler characteristic equal to its homological Euler characteristic, then any
finite-support cell-count description of its graded pieces immediately yields the alternating
cell-count formula for homology. -/
theorem homologyEulerChar_eq_sum_range_of_eulerChar
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (k : Type u) [Field k] (C : ChainComplex (ModuleCat.{u} k) ℕ)
    [∀ n : ℕ, C.HasHomology n] {N : ℕ}
    (hEuler : HomologicalComplex.eulerChar C = HomologicalComplex.homologyEulerChar C)
    (hSupport : GradedObject.finrankSupport C.X ⊆ Finset.range N)
    (hFinrank :
      ∀ n : ℕ, Module.finrank k (C.X n) = Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n)) :
    HomologicalComplex.homologyEulerChar C =
      Finset.sum (Finset.range N) fun n ↦
        (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n) := by
  -- Replace homological Euler characteristic with the ordinary Euler characteristic of the same
  -- chain complex, so only the chain-group support and ranks remain.
  calc
    HomologicalComplex.homologyEulerChar C = HomologicalComplex.eulerChar C := hEuler.symm
    _ = ∑ n ∈ Finset.range N, ((ComplexShape.down ℕ).χ n : ℤ) * Module.finrank k (C.X n) := by
          simpa using
            HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset C (Finset.range N)
              hSupport
    _ = ∑ n ∈ Finset.range N,
          ((ComplexShape.down ℕ).χ n : ℤ) *
            Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [hFinrank n]
    _ = Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [downNatEulerSign_eq_negOnePow]

/-- Helper for Problem 13.6.1: the missing ingredient is a field-valued cellular chain model for
`X` whose homology computes the singular homology of `X`, whose Euler characteristic agrees with
its homological Euler characteristic, and whose degreewise chain-group ranks are the cell counts
up to the chosen cutoff. -/
theorem existsCellularFieldEulerComparison
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    [CWComplex.Finite (Set.univ : Set X)] (k : Type u) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n)) :
    ∃ C : ChainComplex (ModuleCat.{u} k) ℕ,
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
        HomologicalComplex.homologyEulerChar C ∧
      HomologicalComplex.eulerChar C = HomologicalComplex.homologyEulerChar C ∧
      GradedObject.finrankSupport C.X ⊆ Finset.range N ∧
      (∀ n : ℕ, Module.finrank k (C.X n) =
        Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n)) := by
  -- Route correction: reuse the earlier subset-level comparison package at `Set.univ` instead of
  -- rebuilding a new singular-to-cellular model locally.
  rcases existsCellularFieldEulerComparisonOnSubset (C := (Set.univ : Set X)) (k := k) hN with
    ⟨C, hComparison, hEuler, hSupport, hFinrank⟩
  -- Transport the singular-homology comparison term across the canonical `Set.univ` homeomorphism.
  refine ⟨C, ?_, hEuler, hSupport, hFinrank⟩
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
        fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set X)) :=
      by
        -- Compare `X` with its whole-space subtype via the canonical homeomorphism.
        symm
        -- Then apply the Chapter 10 homotopy-invariance owner on that homeomorphism.
        simpa using
          singularHomologyEulerChar_eq_of_homotopyEquiv
            (X := (Set.univ : Set X)) (Y := X) (k := k)
            (Homeomorph.Set.univ X).toHomotopyEquiv
    _ = HomologicalComplex.homologyEulerChar C := hComparison

/-- Helper for Problem 13.6.1: once the CW cells of `X` vanish above degree `N - 1`, the Euler
characteristic of the singular homology with field coefficients should normalize to the same
finite alternating cell-count sum. -/
theorem fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_model
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (k : Type u) [Field k] {N : ℕ}
    (C : ChainComplex (ModuleCat.{u} k) ℕ)
    [∀ n : ℕ, C.HasHomology n]
    (hComparison :
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
        HomologicalComplex.homologyEulerChar C)
    (hEuler : HomologicalComplex.eulerChar C = HomologicalComplex.homologyEulerChar C)
    (hSupport : GradedObject.finrankSupport C.X ⊆ Finset.range N)
    (hFinrank :
      ∀ n : ℕ, Module.finrank k (C.X n) =
        Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n)) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
      Finset.sum (Finset.range N) fun n ↦
        (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n) := by
  -- Transport the singular-homology Euler characteristic to the chosen cellular model `C`.
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
        HomologicalComplex.homologyEulerChar C := hComparison
    -- Then rewrite the model's homological Euler characteristic by its finite cell-count package.
    _ = Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n) :=
      homologyEulerChar_eq_sum_range_of_eulerChar (X := X) (k := k) C hEuler hSupport hFinrank

/-- Helper for Problem 13.6.1: once both sides are rewritten using the same cutoff on the CW
cells, the theorem follows by comparing them to the common alternating cell-count sum. -/
theorem finiteCWEulerCharacteristic_eq_singularHomologyEulerChar_of_cutoff
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    [CWComplex.Finite (Set.univ : Set X)] (k : Type u) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n))
    (hField :
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
        Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n)) :
    χ((Set.univ : Set X)) = fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) := by
  -- Rewrite the CW Euler characteristic using the same cutoff that already computes homology.
  rw [cwEulerCharacteristic_eq_sum_range_of_isEmpty_cell (C := (Set.univ : Set X)) hN]
  exact hField.symm

/-- Helper for Problem 13.6.1: once the CW cells of `X` vanish above degree `N - 1`, the Euler
characteristic of the singular homology with field coefficients should normalize to the same
finite alternating cell-count sum. -/
theorem fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_isEmpty_cell
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    [CWComplex.Finite (Set.univ : Set X)] (k : Type u) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n)) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
      Finset.sum (Finset.range N) fun n ↦
        (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n) :=
by
  -- Reduce the source-facing statement to the existence of a cellular field model with the
  -- expected Euler-characteristic package.
  rcases existsCellularFieldEulerComparison (X := X) (k := k) hN with
    ⟨C, hComparison, hEuler, hSupport, hFinrank⟩
  -- The new helper isolates the already-finished algebraic normalization from the missing
  -- singular-to-cellular comparison package.
  exact
    fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_model
      (X := X) (k := k) C hComparison hEuler hSupport hFinrank

/-- Problem 13.6.1. For a finite CW complex `X`, the Euler characteristic `χ(X)` equals the
Euler characteristic `χ(H_*(X; k))` of its singular homology with coefficients in any field `k`.
Here `χ(X)` is formalized as `χ((Set.univ : Set X))`, and the homology side is the canonical owner
`fieldTopologicalSingularHomologyEulerChar k (TopCat.of X)`. -/
theorem finiteCWEulerCharacteristic_eq_singularHomologyEulerChar
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    [CWComplex.Finite (Set.univ : Set X)] (k : Type u) [Field k] :
    χ((Set.univ : Set X)) = fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) := by
  -- Compare both sides with the same finite alternating sum obtained from a cutoff on the cells.
  rcases existsCellCutoff (X := X) with ⟨N, hN⟩
  -- Rewrite both sides using that common cutoff and compare them to the same alternating sum.
  exact
    finiteCWEulerCharacteristic_eq_singularHomologyEulerChar_of_cutoff
      (X := X) (k := k) hN
      (fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_isEmpty_cell
        (X := X) (k := k) hN)
