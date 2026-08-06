import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.CompletelyRegular
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Semantic search hits: `T35Space`, `Pi.compactSpace`, `Function.compactSpace`; local precedent:
-- `Definition_5_1_9` uses `UCompactlyGeneratedSpace` for the textbook notion of a `k`-space`,
-- while `Convention_5_1_3` separates compactness and Hausdorffness into `CompactSpace` and
-- `T2Space`.

/-- Helper for Problem 5.3.5: the `n`-th level slice in `ι → ℕ` consists of functions taking only
the values `0` and `n`, with at most `n` zero-coordinates. -/
def levelSlice (ι : Type u) (n : ℕ+) : Set (ι → ℕ) :=
  {f | (∀ i, f i = 0 ∨ f i = n) ∧
      ∀ t : Finset ι, (∀ i ∈ t, f i = 0) → t.card ≤ n}

/-- Helper for Problem 5.3.5: the union of all positive level slices is the compactly-closed but
nonclosed subset used to refute the `k`-space condition. -/
def levelCounterexample (ι : Type u) : Set (ι → ℕ) :=
  ⋃ n : ℕ+, levelSlice ι n

/-- Helper for Problem 5.3.5: a function in a level slice has only finitely many zero-coordinates.
-/
lemma zeroSetFinite_of_mem_levelSlice {ι : Type u} {n : ℕ+} {f : ι → ℕ}
    (hf : f ∈ levelSlice ι n) : Set.Finite {i | f i = 0} := by
  classical
  -- If there were infinitely many zeros, we could choose `n + 1` of them and violate the bound.
  by_contra hfinite
  have hinf : Set.Infinite {i | f i = 0} := by
    simpa only [Set.Infinite] using hfinite
  obtain ⟨t, htsubset, htcard⟩ := hinf.exists_subset_card_eq ((n : ℕ) + 1)
  have hle := hf.2 t fun i hi ↦ htsubset hi
  rw [htcard] at hle
  exact Nat.not_succ_le_self _ hle

/-- Helper for Problem 5.3.5: the function that is `0` on a finite set and `s.card + 1`
elsewhere lies in the corresponding positive level slice. -/
lemma finsetPiecewiseZero_mem_levelSlice {ι : Type u} [DecidableEq ι] (s : Finset ι) :
    let n : ℕ+ := ⟨s.card + 1, Nat.succ_pos _⟩
    s.piecewise (fun _ : ι ↦ 0) (fun _ : ι ↦ (n : ℕ)) ∈ levelSlice ι n := by
  let n : ℕ+ := ⟨s.card + 1, Nat.succ_pos _⟩
  -- The only zero-coordinates are those in `s`, so every zero-set witness is bounded by `s.card`.
  refine ⟨?_, ?_⟩
  · intro i
    by_cases hi : i ∈ s
    · left
      simp [Finset.piecewise, hi]
    · right
      simp [Finset.piecewise, hi]
  · intro t ht
    have hsubset : t ⊆ s := by
      intro i hi
      by_contra his
      have hzero := ht i hi
      simp [Finset.piecewise, his] at hzero
    exact le_trans (Finset.card_le_card hsubset) (Nat.le_succ _)

/-- Helper for Problem 5.3.5: every level slice is closed in the product topology on `ι → ℕ`.
-/
lemma levelSliceIsClosed {ι : Type u} (n : ℕ+) : IsClosed (levelSlice ι n) := by
  classical
  rw [← isOpen_compl_iff]
  let badValues : Set (ι → ℕ) := {f | ∃ i, f i ≠ 0 ∧ f i ≠ n}
  let tooManyZeros : Set (ι → ℕ) :=
    ⋃ t : {t : Finset ι // (n : ℕ) < t.1.card}, {f | ∀ i ∈ (t : Finset ι), f i = 0}
  have hbadValues : IsOpen badValues := by
    -- A forbidden coordinate value is detected on a single coordinate, hence by an open cylinder.
    rw [show badValues = ⋃ i : ι, {f : ι → ℕ | f i ≠ 0 ∧ f i ≠ n} by
      ext f
      simp [badValues]]
    refine isOpen_iUnion fun i ↦ ?_
    exact IsOpen.preimage (f := fun f : ι → ℕ ↦ f i)
      (t := ({m : ℕ | m ≠ 0 ∧ m ≠ n} : Set ℕ))
      (continuous_apply i) (isOpen_discrete ({m : ℕ | m ≠ 0 ∧ m ≠ n} : Set ℕ))
  have htooManyZeros : IsOpen tooManyZeros := by
    -- A witness finite set of zero-coordinates also defines an open cylinder in the product.
    refine isOpen_iUnion fun t ↦ ?_
    simpa [tooManyZeros, Set.pi, Finset.mem_coe] using
      isOpen_set_pi (i := ((t : Finset ι) : Set ι)) (s := fun _ ↦ ({0} : Set ℕ))
        t.1.finite_toSet (fun _ _ ↦ isOpen_discrete ({0} : Set ℕ))
  have hcompl :
      (levelSlice ι n)ᶜ = badValues ∪ tooManyZeros := by
    ext f
    constructor
    · intro hf
      by_cases hvals : ∀ i, f i = 0 ∨ f i = n
      · right
        have hbound : ¬ ∀ t : Finset ι, (∀ i ∈ t, f i = 0) → t.card ≤ n := by
          exact fun hcount ↦ hf ⟨hvals, hcount⟩
        push Not at hbound
        rcases hbound with ⟨t, htzero, htcard⟩
        exact Set.mem_iUnion.2 ⟨⟨t, htcard⟩, htzero⟩
      · left
        push Not at hvals
        rcases hvals with ⟨i, hi0, hin⟩
        exact ⟨i, hi0, hin⟩
    · intro hf
      rcases hf with hbad | hzeros
      · intro hslice
        rcases hbad with ⟨i, hi0, hin⟩
        rcases hslice.1 i with hzero | hlevel
        · exact hi0 hzero
        · exact hin hlevel
      · rcases Set.mem_iUnion.1 hzeros with ⟨t, htzero⟩
        intro hslice
        exact (Nat.not_lt_of_ge (hslice.2 t htzero)) t.2
  simpa [hcompl] using hbadValues.union htooManyZeros

/-- Helper for Problem 5.3.5: the zero function lies in the closure of the level counterexample,
but it does not belong to the counterexample itself. -/
lemma zeroFunction_mem_closure_levelCounterexample {ι : Type u} [Uncountable ι] :
    (fun _ : ι ↦ 0) ∈ closure (levelCounterexample ι) ∧
      (fun _ : ι ↦ 0) ∉ levelCounterexample ι := by
  classical
  constructor
  · -- Every neighborhood of the zero function contains one of the finite-support approximants.
    rw [mem_closure_iff_nhds]
    intro s hs
    rcases mem_nhds_iff.1 hs with ⟨u, hu_subset, hu_open, hzero_mem⟩
    rcases (isOpen_pi_iff.1 hu_open) (fun _ : ι ↦ 0) hzero_mem with ⟨I, v, hv, hIv⟩
    let n : ℕ+ := ⟨I.card + 1, Nat.succ_pos _⟩
    refine ⟨I.piecewise (fun _ : ι ↦ 0) (fun _ : ι ↦ (n : ℕ)), hu_subset ?_, ?_⟩
    · exact hIv fun i hi ↦ by
        have hi' : i ∈ I := Finset.mem_coe.mp hi
        have hvalue : I.piecewise (fun _ : ι ↦ 0) (fun _ : ι ↦ (n : ℕ)) i = 0 := by
          simp [Finset.piecewise, hi']
        simpa [hvalue] using (hv i hi).2
    · exact Set.mem_iUnion.2 ⟨n, by simpa [n] using finsetPiecewiseZero_mem_levelSlice I⟩
  · -- The zero function has infinitely many zero-coordinates, so it cannot sit in any level slice.
    intro hz
    rcases Set.mem_iUnion.1 hz with ⟨n, hn⟩
    have hfinite : Set.Finite ({i : ι | (fun _ : ι ↦ 0) i = 0}) :=
      zeroSetFinite_of_mem_levelSlice (ι := ι) hn
    have : Finite ι := by
      simpa [Set.finite_univ_iff] using hfinite
    exact Finite.false this

/-- Helper for Problem 5.3.5: the coordinates that never attain the value `n` on the image of `g`.
-/
def badCoordinates {ι : Type u} {K : Type*} [TopologicalSpace K] (g : C(K, ι → ℕ)) (n : ℕ+) :
    Set ι :=
  {i | (n : ℕ) ∉ Set.range fun x : K ↦ g x i}

/-- Helper for Problem 5.3.5: the positive levels that actually occur on the image of `g`. -/
def relevantLevels {ι : Type u} {K : Type*} [TopologicalSpace K] (g : C(K, ι → ℕ)) : Set ℕ+ :=
  {n | ∃ x : K, g x ∈ levelSlice ι n}

/-- Helper for Problem 5.3.5: a compact image in `ι → ℕ` meets only finitely many positive level
slices when `ι` is uncountable. -/
lemma relevantLevelsFiniteOfCompact {ι : Type u} [Uncountable ι] {K : Type*} [TopologicalSpace K]
    [CompactSpace K] (g : C(K, ι → ℕ)) : Set.Finite (relevantLevels (ι := ι) g) := by
  classical
  let R : Set ℕ+ := relevantLevels (ι := ι) g
  let U : Set ι := ⋃ n ∈ R, badCoordinates g n
  have hUcount : U.Countable := by
    -- Each relevant level has only finitely many bad coordinates, and there are countably many
    -- positive levels to begin with.
    refine Set.Countable.biUnion (Set.to_countable R) ?_
    intro n hn
    rcases hn with ⟨x, hx⟩
    refine (zeroSetFinite_of_mem_levelSlice (ι := ι) hx).countable.mono ?_
    intro i hi
    have hnot : g x i ≠ n := by
      intro hgi
      exact hi ⟨x, hgi⟩
    rcases hx.1 i with hzero | hlevel
    · exact hzero
    · exact (hnot hlevel).elim
  have hnotall : ¬ ∀ i : ι, i ∈ U := by
    intro hall
    have hUeq : U = Set.univ := by
      ext i
      simp [hall i]
    exact Set.not_countable_univ (hUeq ▸ hUcount)
  push Not at hnotall
  rcases hnotall with ⟨i, hiU⟩
  have hcoordFinite : Set.Finite (Set.range fun x : K ↦ g x i) := by
    exact (isCompact_range ((continuous_apply i).comp g.continuous)).finite_of_discrete
  have himageFinite : Set.Finite ((fun n : ℕ+ ↦ (n : ℕ)) '' R) := by
    refine hcoordFinite.subset ?_
    rintro m ⟨n, hnR, rfl⟩
    have hnotBad : i ∉ badCoordinates g n := by
      intro hiBad
      exact hiU <| Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨hnR, hiBad⟩⟩
    simpa [badCoordinates] using hnotBad
  exact himageFinite.of_finite_image fun a ha b hb hab ↦ PNat.coe_injective hab

/-- Helper for Problem 5.3.5: the union of the positive level slices is compactly closed. -/
lemma levelCounterexampleIsCompactlyClosed {ι : Type u} [Uncountable ι] :
    IsCompactlyClosed (levelCounterexample ι) := by
  intro K _ _ g
  classical
  let R : Set ℕ+ := relevantLevels (ι := ι) g
  have hRfinite : R.Finite := relevantLevelsFiniteOfCompact (ι := ι) g
  have hpreimage :
      g ⁻¹' levelCounterexample ι = ⋃ n ∈ R, g ⁻¹' levelSlice ι n := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨n, hnx⟩
      exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨⟨x, hnx⟩, hnx⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨n, hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨_, hnx⟩
      exact Set.mem_iUnion.2 ⟨n, hnx⟩
  -- On a compact source, only finitely many levels matter, so the preimage is a finite union.
  rw [hpreimage]
  exact hRfinite.isClosed_biUnion fun n hn ↦ (levelSliceIsClosed (ι := ι) n).preimage g.continuous

/-- Problem 5.3.5 (1): there exists a Tychonoff space that is not a `k`-space. -/
theorem exists_tychonoffSpace_not_kSpace :
    ∃ X : TopCat, T35Space X ∧ ¬ UCompactlyGeneratedSpace X := by
  -- Use the universe-lifted uncountable product `ULift (ℝ → ℕ)`, which is homeomorphic to
  -- `ℝ → ℕ` and therefore inherits the same Tychonoff/non-`k` behavior.
  refine ⟨TopCat.of (ULift (ℝ → ℕ)), ?_, ?_⟩
  · let _ : T35Space (ℝ → ℕ) := inferInstance
    have hEmbedding :
        Topology.IsEmbedding (fun x : ↑(TopCat.of (ULift (ℝ → ℕ))) ↦ x.down) := by
      simpa using Homeomorph.ulift.isEmbedding
    let _ : T35Space ↑(TopCat.of (ULift (ℝ → ℕ))) := hEmbedding.t35Space
    exact inferInstance
  intro hk
  let A : Set ↑(TopCat.of (ULift (ℝ → ℕ))) := (fun x ↦ x.down) ⁻¹' levelCounterexample ℝ
  have hAcompact : IsCompactlyClosed A := by
    exact (levelCounterexampleIsCompactlyClosed (ι := ℝ)).preimage continuous_uliftDown
  have hAclosed : IsClosed A := by
    let _ : UCompactlyGeneratedSpace ↑(TopCat.of (ULift (ℝ → ℕ))) := hk
    exact IsCompactlyClosed.isClosed hAcompact
  have hBaseClosed : IsClosed (levelCounterexample ℝ) := by
    simpa [A] using hAclosed.preimage continuous_uliftUp
  have hzero := zeroFunction_mem_closure_levelCounterexample (ι := ℝ)
  exact hzero.2 <| by
    simpa [hBaseClosed.closure_eq] using hzero.1

variable (ι : Type u)

/- Problem 5.3.5 (2): every cube `ι → Set.Icc (0 : ℝ) 1` is compact. -/
#check (inferInstance : CompactSpace (ι → Set.Icc (0 : ℝ) 1))

/- Problem 5.3.5 (3): every cube `ι → Set.Icc (0 : ℝ) 1` is Hausdorff. -/
#check (inferInstance : T2Space (ι → Set.Icc (0 : ℝ) 1))
