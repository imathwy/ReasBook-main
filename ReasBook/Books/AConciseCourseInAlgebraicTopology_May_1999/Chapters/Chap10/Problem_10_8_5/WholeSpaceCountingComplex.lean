import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Data.Finite.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.CWComplex.Classical.Finite

open CategoryTheory Topology
open scoped Topology.CWComplex

universe u w

noncomputable section

/-- Helper for Problem 10.8.5: the free `k`-module on the `n`-cells of the whole-space CW owner.
-/
abbrev wholeSpaceCellModule
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (k : Type w) [Field k] (n : ℕ) : ModuleCat.{max u w} k :=
  ModuleCat.of k (Topology.CWComplex.cell (Set.univ : Set Z) n →₀ k)

/-- Helper for Problem 10.8.5: the zero differential on the whole-space cell-counting complex
has square zero. -/
theorem wholeSpaceCellCountingComplexSquareZero
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (k : Type w) [Field k] :
    ∀ n : ℕ,
      (0 :
        wholeSpaceCellModule (Z := Z) k (n + 2) ⟶
          wholeSpaceCellModule (Z := Z) k (n + 1)) ≫
        (0 :
          wholeSpaceCellModule (Z := Z) k (n + 1) ⟶
            wholeSpaceCellModule (Z := Z) k n) = 0 := by
  intro n
  -- The explicit whole-space model uses zero differentials everywhere.
  simp

/-- Helper for Problem 10.8.5: the explicit whole-space cell-counting complex with zero
differential. -/
noncomputable def wholeSpaceCellCountingComplex
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (k : Type w) [Field k] : ChainComplex (ModuleCat.{max u w} k) ℕ :=
  ChainComplex.of
    (wholeSpaceCellModule (Z := Z) k)
    (fun _ ↦ 0)
    (wholeSpaceCellCountingComplexSquareZero (Z := Z) k)

/-- Helper for Problem 10.8.5: the zero-differential whole-space cell-counting complex has
homology in every degree. -/
theorem wholeSpaceCellCountingComplexPrevDifferentialZero
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (k : Type w) [Field k] (n : ℕ) :
    let K := wholeSpaceCellCountingComplex (Z := Z) k
    K.d ((ComplexShape.down ℕ).prev n) n = 0 := by
  let K := wholeSpaceCellCountingComplex (Z := Z) k
  -- The predecessor differential is one of the explicit zero maps in `ChainComplex.of`.
  rw [ChainComplex.prev]
  simp [wholeSpaceCellCountingComplex]
  rfl

/-- Helper for Problem 10.8.5: the outgoing differential of the whole-space cell-counting complex
also vanishes in every degree. -/
theorem wholeSpaceCellCountingComplexNextDifferentialZero
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (k : Type w) [Field k] (n : ℕ) :
    let K := wholeSpaceCellCountingComplex (Z := Z) k
    K.d n ((ComplexShape.down ℕ).next n) = 0 := by
  let K := wholeSpaceCellCountingComplex (Z := Z) k
  cases n with
  | zero =>
      -- In degree `0`, `next` stays at `0`, so this is a shape-forced zero differential.
      simp [wholeSpaceCellCountingComplex]
      rfl
  | succ n =>
      -- In positive degree, the target index is `n`, and the chosen differential is still zero.
      rw [ChainComplex.next_nat_succ]
      simp [wholeSpaceCellCountingComplex]
      rfl

/-- Helper for Problem 10.8.5: the zero-differential whole-space cell-counting complex has
homology in every degree. -/
theorem wholeSpaceCellCountingComplexHasHomology
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (k : Type w) [Field k] (n : ℕ) :
    (wholeSpaceCellCountingComplex (Z := Z) k).HasHomology n := by
  let K := wholeSpaceCellCountingComplex (Z := Z) k
  refine ShortComplex.HasHomology.mk' ?_
  -- Both maps in the degree-`n` short complex vanish because the differential is identically
  -- zero.
  refine ShortComplex.HomologyData.ofZeros (K.sc n) ?_ ?_
  · simpa [K] using wholeSpaceCellCountingComplexPrevDifferentialZero (Z := Z) (k := k) n
  · simpa [K] using wholeSpaceCellCountingComplexNextDifferentialZero (Z := Z) (k := k) n

/-- Helper for Problem 10.8.5: in the zero-differential whole-space cell-counting complex, the
`n`-th homology is the degree-`n` chain group itself. -/
noncomputable def wholeSpaceCellCountingComplexHomologyIso
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (k : Type w) [Field k] (n : ℕ) :
    let K := wholeSpaceCellCountingComplex (Z := Z) k
    K.homology n ≅ K.X n := by
  let K := wholeSpaceCellCountingComplex (Z := Z) k
  have hZeroLeft : (K.sc n).f = 0 := by
    -- The incoming differential is zero in the explicit model.
    simpa [K] using wholeSpaceCellCountingComplexPrevDifferentialZero (Z := Z) (k := k) n
  have hZeroRight : (K.sc n).g = 0 := by
    -- The outgoing differential is also zero in the explicit model.
    simpa [K] using wholeSpaceCellCountingComplexNextDifferentialZero (Z := Z) (k := k) n
  let hData : (K.sc n).HomologyData :=
    ShortComplex.HomologyData.ofZeros (K.sc n) hZeroLeft hZeroRight
  -- Local instance justification (proof interface): the chosen zero-map homology data is the
  -- canonical way to expose the degreewise homology of the explicit zero-differential model.
  letI : K.HasHomology n := ShortComplex.HasHomology.mk' hData
  -- The chosen homology data identifies the short-complex homology with the middle object.
  simpa [K, wholeSpaceCellModule] using hData.left.homologyIso

/-- Helper for Problem 10.8.5: the explicit whole-space cell-counting complex already has the
algebraic equality `χ = χ(H_*)` because its homology groups are just its chain groups. -/
theorem wholeSpaceCellCountingComplexEulerChar_eq_homologyEulerChar
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] :
    let K := wholeSpaceCellCountingComplex (Z := Z) k
    HomologicalComplex.eulerChar K = HomologicalComplex.homologyEulerChar K := by
  let K := wholeSpaceCellCountingComplex (Z := Z) k
  -- Local instance justification (proof interface): the explicit zero-differential model has
  -- degreewise homology by the zero-map short-complex data proved above.
  letI : ∀ n : ℕ, K.HasHomology n := fun n ↦
    wholeSpaceCellCountingComplexHasHomology (Z := Z) (k := k) n
  have hFinrank :
      (fun n ↦ Module.finrank k (K.X n)) =
        fun n ↦ Module.finrank k (K.homology n) := by
    funext n
    -- Compare the degree-`n` chain group with the same degree homology through the
    -- zero-differential homology isomorphism.
    simpa [K] using
      LinearEquiv.finrank_eq
        ((wholeSpaceCellCountingComplexHomologyIso (Z := Z) (k := k) n).toLinearEquiv).symm
  -- Once the degreewise ranks agree, the two Euler characteristics are the same `finsum`.
  simpa [HomologicalComplex.eulerChar, HomologicalComplex.homologyEulerChar] using
    congrArg
      (fun f : ℕ → ℕ ↦
        ∑ᶠ n : ℕ, (((ComplexShape.down ℕ).χ n : ℤ) * f n))
      hFinrank

/-- Helper for Problem 10.8.5: above the cutoff `N`, the whole-space counting complex has zero
graded support because its chain groups are free modules on empty cell sets. -/
theorem wholeSpaceCellCountingComplex_finrankSupport_subset_range
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    let K := wholeSpaceCellCountingComplex (Z := Z) k
    GradedObject.finrankSupport K.X ⊆ Finset.range N := by
  let K := wholeSpaceCellCountingComplex (Z := Z) k
  rw [GradedObject.finrankSupport_subset_iff]
  intro n hn
  have hnGE : N ≤ n := by
    exact le_of_not_gt fun hlt ↦ hn (Finset.mem_range.2 hlt)
  have hEmpty : IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n) := hN n hnGE
  letI : IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n) := hEmpty
  letI : Fintype (Topology.CWComplex.cell (Set.univ : Set Z) n) := Fintype.ofFinite _
  -- Above the cutoff, the explicit chain group is the free module on an empty index type.
  change Module.finrank k (Topology.CWComplex.cell (Set.univ : Set Z) n →₀ k) = 0
  calc
    Module.finrank k (Topology.CWComplex.cell (Set.univ : Set Z) n →₀ k) =
        Fintype.card (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
      Module.finrank_finsupp_self (R := k)
        (ι := Topology.CWComplex.cell (Set.univ : Set Z) n)
    _ = 0 := Fintype.card_of_isEmpty

/-- Helper for Problem 10.8.5: each degree of the whole-space counting complex has rank equal to
the number of cells in that degree. -/
theorem wholeSpaceCellCountingComplex_finrank_eq_cellCard
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] :
    ∀ n : ℕ,
      Module.finrank k ((wholeSpaceCellCountingComplex (Z := Z) k).X n) =
        Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n) := by
  intro n
  letI : Finite (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
    (inferInstance : CWComplex.Finite (Set.univ : Set Z)).finite_cell n
  letI : Fintype (Topology.CWComplex.cell (Set.univ : Set Z) n) := Fintype.ofFinite _
  -- Degreewise, the explicit chain group is the free module on the `n`-cells.
  change Module.finrank k (Topology.CWComplex.cell (Set.univ : Set Z) n →₀ k) =
    Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n)
  calc
    Module.finrank k (Topology.CWComplex.cell (Set.univ : Set Z) n →₀ k) =
        Fintype.card (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
      Module.finrank_finsupp_self (R := k)
        (ι := Topology.CWComplex.cell (Set.univ : Set Z) n)
    _ = Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
      Nat.card_eq_fintype_card.symm

/-- Helper for Problem 10.8.5: the explicit whole-space cell-counting complex already has the
entire algebraic package needed downstream: its Euler characteristic equals its homological Euler
characteristic, its graded support is cut off by `hN`, and its chain-group ranks are the cell
counts. -/
theorem wholeSpaceCellCountingComplexSpec
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    let K := wholeSpaceCellCountingComplex (Z := Z) k
    HomologicalComplex.eulerChar K = HomologicalComplex.homologyEulerChar K ∧
      GradedObject.finrankSupport K.X ⊆ Finset.range N ∧
      (∀ n : ℕ,
        Module.finrank k (K.X n) =
          Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n)) := by
  let K := wholeSpaceCellCountingComplex (Z := Z) k
  -- The three independent algebraic ingredients are already isolated above.
  refine ⟨?_, ?_, ?_⟩
  · simpa [K] using wholeSpaceCellCountingComplexEulerChar_eq_homologyEulerChar
      (Z := Z) (k := k)
  · simpa [K] using wholeSpaceCellCountingComplex_finrankSupport_subset_range
      (Z := Z) (k := k) hN
  · simpa [K] using wholeSpaceCellCountingComplex_finrank_eq_cellCard (Z := Z) (k := k)
