module

public import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.FundamentalGroupoidOpenCover
public import Mathlib.Topology.Subpath
public import Mathlib.Topology.UnitInterval

-- Declarations for this item will be appended below by the statement pipeline.

@[expose] public section

universe u v

open unitInterval

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- A finite strictly increasing subdivision of `I` together with cover labels for its
nondegenerate subintervals. This is an internal bridge from the monotone `ℕ`-indexed subdivision
returned by mathlib to the source-facing finite subdivision API used in this chapter. -/
private structure IntervalSubdivision (c : ι → Set I) (a b : I) where
  n : ℕ
  points : Fin (n + 1) → I
  labels : Fin n → ι
  start : points 0 = a
  finish : points (Fin.last n) = b
  strict : StrictMono points
  cover : ∀ k : Fin n, Set.Icc (points k.castSucc) (points k.succ) ⊆ c (labels k)

/-- The trivial subdivision whose only breakpoint is `a`. -/
private def IntervalSubdivision.nil (c : ι → Set I) (a : I) : IntervalSubdivision c a a where
  n := 0
  points := fun _ ↦ a
  labels := Fin.elim0
  start := rfl
  finish := rfl
  strict := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    exact Fin.elim0 k
  cover := by
    intro k
    exact Fin.elim0 k

/-- Appending a genuinely new endpoint to a strict subdivision extends it by one cover-controlled
subinterval. -/
private def IntervalSubdivision.snoc
    {c : ι → Set I} {a b : I}
    (S : IntervalSubdivision c a b) (d : I) (i : ι)
    (hbd : b < d) (hcover : Set.Icc b d ⊆ c i) :
    IntervalSubdivision c a d where
  n := S.n + 1
  points := Fin.snoc S.points d
  labels := Fin.snoc S.labels i
  start := by simpa [Fin.snoc_castSucc] using S.start
  finish := by simp
  strict := by
    intro x y hxy
    rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
    · have hx_ne_last : x ≠ Fin.last (S.n + 1) := by
        exact Fin.ne_of_lt (lt_of_lt_of_le hxy y'.castSucc_lt_last.le)
      obtain ⟨x', rfl⟩ := Fin.eq_castSucc_of_ne_last hx_ne_last
      simpa [Fin.snoc_castSucc] using S.strict (Fin.castSucc_lt_castSucc_iff.mp hxy)
    · obtain ⟨x', rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_of_lt hxy)
      rcases Fin.eq_castSucc_or_eq_last x' with ⟨x'', rfl⟩ | rfl
      · have hx_lt_b : S.points x''.castSucc < b := by
          exact lt_of_lt_of_eq (S.strict x''.castSucc_lt_last) S.finish
        simpa [Fin.snoc_castSucc, Fin.snoc_last] using lt_trans hx_lt_b hbd
      · simpa [Fin.snoc_last, S.finish] using hbd
  cover := by
    intro k
    rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
    · have hsucc : j.castSucc.succ = j.succ.castSucc := by
        ext
        rfl
      simpa only [Fin.snoc_castSucc, hsucc] using S.cover j
    · simpa [Fin.snoc_last, S.finish] using hcover

/-- Compress the finite prefix `t 0, …, t N` of a monotone subdivision by discarding only repeated
consecutive breakpoints. The surviving points remain strictly increasing, and each surviving
subinterval is one of the original cover-controlled subintervals. -/
private noncomputable def intervalSubdivisionPrefix
    {c : ι → Set I} (t : ℕ → I)
    (hmono : Monotone t)
    (hsub : ∀ n, ∃ i, Set.Icc (t n) (t (n + 1)) ⊆ c i) :
    ∀ N, IntervalSubdivision c (t 0) (t N)
  | 0 => IntervalSubdivision.nil c (t 0)
  | N + 1 =>
      let S := intervalSubdivisionPrefix t hmono hsub N
      let i := Classical.choose (hsub N)
      let hi := Classical.choose_spec (hsub N)
      if hEq : t N = t (N + 1) then
        { n := S.n
          points := S.points
          labels := S.labels
          start := S.start
          finish := by simpa [hEq] using S.finish
          strict := S.strict
          cover := S.cover }
      else
        S.snoc (t (N + 1)) i (lt_of_le_of_ne (hmono (Nat.le_succ N)) hEq) hi

/-- If the image of a closed interval lies in one cover member, then the corresponding subpath lies
in that cover member. -/
private theorem subpathSubordinateOfIntervalSubset
    {x y : X} (γ : Path x y) (O : ι → TopologicalSpace.Opens X) {i : ι} {a b : I}
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ (fun s : I ↦ γ s) ⁻¹' (O i : Set X)) :
    Set.range (γ.subpath a b) ⊆ O i := by
  rw [Path.range_subpath_of_le γ a b hab]
  rintro _ ⟨s, hs, rfl⟩
  exact hsub hs

/-- ProofStep 2.7.3: every path in `X` admits a finite subdivision whose successive subpaths lie
in members of an open cover `O`; this is the geometric input showing that compatible data on the
fundamental groupoids `Π(U)` determine a value on each path class in `Π(X)`. -/
-- Proof sketch: pull back the cover `O` along `γ : I → X`, apply the canonical mathlib theorem
-- `exists_monotone_Icc_subset_open_cover_unitInterval` to obtain a monotone subdivision of `I`,
-- then compress the finite prefix up to the first breakpoint equal to `1` by deleting only repeated
-- consecutive breakpoints. The pulled-back interval-containment statement then translates to the
-- desired subpath-containment statement by `Path.range_subpath_of_le`.
theorem path_subdivision_subordinate_to_open_cover
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    ∃ n : ℕ, ∃ t : Fin (n + 1) → I,
      t 0 = 0 ∧
      t (Fin.last n) = 1 ∧
      StrictMono t ∧
      ∃ i : Fin n → TopologicalSpace.IsOpenCover.Index O,
        ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (i k) := by
  classical
  let c : ι → Set I := fun i ↦ (fun s : I ↦ γ s) ⁻¹' (O i : Set X)
  have hcOpen : ∀ i, IsOpen (c i) := by
    intro i
    exact (O i).isOpen.preimage γ.continuous
  have hcCover : Set.univ ⊆ ⋃ i, c i := by
    intro s _
    obtain ⟨i, hi⟩ := hO.exists_mem (γ s)
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨tNat, ht0Nat, hmonoNat, ⟨N, hN⟩, hsubNat⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcOpen hcCover
  let S := intervalSubdivisionPrefix tNat hmonoNat hsubNat N
  refine ⟨S.n, S.points, ?_, ?_, S.strict, S.labels, ?_⟩
  · exact S.start.trans ht0Nat
  · simpa [S, hN N le_rfl] using S.finish
  · intro k
    have hle : S.points k.castSucc ≤ S.points k.succ := S.strict.monotone k.castSucc_le_succ
    exact subpathSubordinateOfIntervalSubset γ O hle <| by
      simpa [S, c] using S.cover k
