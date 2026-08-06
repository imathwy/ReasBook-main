import Mathlib.Topology.CWComplex.Classical.Subcomplex

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Topology

-- Semantic recall via `lean_leansearch`: no dedicated colimit owner for increasing sequences of
-- CW subcomplexes surfaced in the local API. The canonical surface here is
-- `Topology.CWComplex.Subcomplex`, built using `Topology.CWComplex.Subcomplex.mk'`, together with
-- the inherited instance `Topology.CWComplex.Subcomplex.instCWComplex`.

/-- Lemma 10.2.5: the sequential colimit of an increasing sequence of subcomplexes of a CW complex
`C` is formalized by the union subcomplex of the family. The monotonicity assumption is part of
the source context, but the union subcomplex itself depends only on the underlying family `Xn`. Its
underlying set is `⋃ n, (Xn n : Set X)`, and it carries the canonical inherited CW-complex
structure. -/
def sequentialSubcomplexColimit
    {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [Topology.CWComplex C]
    (Xn : ℕ → CWComplex.Subcomplex C) :
    CWComplex.Subcomplex C :=
  CWComplex.Subcomplex.mk' C
    (⋃ n : ℕ, (Xn n : Set X))
    (fun m : ℕ ↦ {i : Topology.CWComplex.cell C m | ∃ n : ℕ, i ∈ (Xn n).I m})
    (by
      intro m i
      rcases i.2 with ⟨n, hi⟩
      exact Set.Subset.trans
        ((Xn n).closedCell_subset_of_mem hi)
        (Set.subset_iUnion (fun k : ℕ ↦ (Xn k : Set X)) n))
    (by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨m, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
        rcases i.2 with ⟨n, hi⟩
        exact Set.mem_iUnion.mpr ⟨n, (Xn n).openCell_subset_of_mem hi hx⟩
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
        rw [← CWComplex.Subcomplex.union (Xn n)] at hx
        have hx' :
            ∃ m, ∃ i : (Xn n).I m,
              x ∈ RelCWComplex.openCell m (i : Topology.CWComplex.cell C m) := by
          simpa [Set.mem_iUnion] using hx
        rcases hx' with ⟨m, i, hx⟩
        exact Set.mem_iUnion.mpr
          ⟨m, Set.mem_iUnion.mpr ⟨⟨(i : Topology.CWComplex.cell C m), ⟨n, i.2⟩⟩, hx⟩⟩)

@[simp] theorem coe_sequentialSubcomplexColimit
    {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [Topology.CWComplex C]
    (Xn : ℕ → CWComplex.Subcomplex C) :
    (sequentialSubcomplexColimit Xn : Set X) = ⋃ n : ℕ, (Xn n : Set X) :=
  rfl

theorem mem_sequentialSubcomplexColimit
    {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [Topology.CWComplex C]
    (Xn : ℕ → CWComplex.Subcomplex C) {x : X} :
    x ∈ sequentialSubcomplexColimit Xn ↔ ∃ n : ℕ, x ∈ Xn n := by
  change x ∈ (⋃ n : ℕ, (Xn n : Set X)) ↔ ∃ n : ℕ, x ∈ Xn n
  simp [Set.mem_iUnion]

/-- Each term of the sequence is contained in the union subcomplex representing the sequential
colimit. -/
theorem le_sequentialSubcomplexColimit
    {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [Topology.CWComplex C]
    (Xn : ℕ → CWComplex.Subcomplex C) (n : ℕ) :
    Xn n ≤ sequentialSubcomplexColimit Xn := by
  simpa [coe_sequentialSubcomplexColimit] using
    (Set.subset_iUnion (fun k : ℕ ↦ (Xn k : Set X)) n)
