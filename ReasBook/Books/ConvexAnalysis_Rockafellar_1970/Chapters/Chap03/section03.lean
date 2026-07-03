

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_3 (from Chap01) -/
open scoped BigOperators Pointwise
open scoped Rockafellar

universe u v

/-
Source/core/bridge triage:
- `core/canonical`: the primary owner is `convexHull 𝕜 (⋃ i, C i)` with simplex coefficients owned
  by `StdSimplex 𝕜 κ`; the canonical statement layer is an indexed simplex-sum existence surface
  over index types `κ` with finitely supported simplex coefficients and index maps `idx : κ → ι`.
- `source-facing bridge`: the textbook finite-support display over `s : Finset ι` and
  `w : StdSimplex 𝕜 s` is retained as a convex-family bridge theorem, derived through
  `convexHull_eq_union_convexHull_finite_subsets` plus the finite-support simplex rewrite.
- Primitive data vs derived API: primitive input for the owner theorem is only the family
  `C : ι → Set E`; convexity of each `C i` is needed only for the finite-support bridge theorem.
- Domain-style sampling: this item uses `Set.mem_conv_iff_exists_stdSimplex`,
  `mem_convexHull_of_exists_fintype`, `convexHull_eq_union_convexHull_finite_subsets`,
  `StdSimplex`, and the set-level simplex-sum lemmas from Text 3.1.4.
- Layer target: canonical owner first (`indexed simplex`), with the textbook finite-support form as
  an explicit downstream bridge.
-/

section

variable {ι : Type u} {E : Type v} {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-- Finite-support bridge to the owner-side simplex-sum surface used by the public theorem. -/
private theorem convexHull_iUnion_finset_eq_iUnion_simplex_sum
    (C : ι → Set E) (s : Finset ι)
    (hconv : ∀ i ∈ s, Convex 𝕜 (C i))
    (hnonempty : ∀ i ∈ s, (C i).Nonempty) :
    convexHull 𝕜 (⋃ i ∈ s, C i) = ⋃ w : StdSimplex 𝕜 s, w.sum (fun i a ↦ a • C i) := by
  have hweighted :
      convexHull 𝕜 (⋃ i ∈ s, C i) = ⋃ w : StdSimplex 𝕜 s, ∑ i : s, w.weights i • C i := by
    classical
    refine (convexHull_min ?_ ?_).antisymm ?_
    · intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨hi, hx⟩
      let j : s := ⟨i, hi⟩
      refine Set.mem_iUnion.2 ⟨StdSimplex.single j, ?_⟩
      refine (Set.mem_fintype_sum (fun k : s ↦ (StdSimplex.single j).weights k • C k) x).2 ?_
      refine ⟨Function.update (fun _ : s ↦ 0) j x, ?_, ?_⟩
      · intro k
        by_cases hk : k = j
        · subst hk
          have hx' : x ∈ (1 : 𝕜) • C j := Set.mem_smul_set.2 ⟨x, hx, by simp⟩
          simpa [Function.update, StdSimplex.single] using hx'
        · have hkw : (StdSimplex.single j).weights k = 0 := by
            simp [StdSimplex.single, hk]
          have hk0 : (0 : E) ∈ (0 : 𝕜) • C k := by
            rw [Set.zero_smul_set (hnonempty k k.property)]
            simp
          simpa [Function.update, hk, hkw] using hk0
      · simp [j, Function.update]
    · intro x hx y hy p q hp hq hpq
      rcases Set.mem_iUnion.1 hx with ⟨w₁, hx⟩
      rcases Set.mem_iUnion.1 hy with ⟨w₂, hy⟩
      rcases (Set.mem_fintype_sum (fun i : s ↦ w₁.weights i • C i) x).1 hx with ⟨g₁, hg₁, rfl⟩
      rcases (Set.mem_fintype_sum (fun i : s ↦ w₂.weights i • C i) y).1 hy with ⟨g₂, hg₂, rfl⟩
      let w : StdSimplex 𝕜 s :=
        { weights := p • w₁.weights + q • w₂.weights
          nonneg := by
            intro i
            exact add_nonneg (mul_nonneg hp (w₁.nonneg i)) (mul_nonneg hq (w₂.nonneg i))
          total := by
            rw [Finsupp.sum_add_index (by intro i _; rfl) (by intro i _ a b; rfl),
              Finsupp.sum_smul_index (by intro i; simp), Finsupp.sum_smul_index (by intro i; simp)]
            rw [← Finsupp.mul_sum, ← Finsupp.mul_sum, w₁.total, w₂.total]
            simpa using hpq }
      refine Set.mem_iUnion.2 ⟨w, ?_⟩
      refine (Set.mem_fintype_sum (fun i : s ↦ w.weights i • C i) _).2 ?_
      refine ⟨fun i ↦ p • g₁ i + q • g₂ i, ?_, by
        simp [Finset.smul_sum, Finset.sum_add_distrib]⟩
      intro i
      rcases Set.mem_smul_set.1 (hg₁ i) with ⟨x₁, hx₁, hx₁eq⟩
      rcases Set.mem_smul_set.1 (hg₂ i) with ⟨x₂, hx₂, hx₂eq⟩
      have hxy :
          p • g₁ i + q • g₂ i = ((p * w₁.weights i) • x₁) + ((q * w₂.weights i) • x₂) := by
        simp [hx₁eq, hx₂eq, mul_smul]
      simpa [hxy, w] using
        (show ((p * w₁.weights i) • x₁) + ((q * w₂.weights i) • x₂) ∈
            (p * w₁.weights i + q * w₂.weights i) • C i from by
          rw [(hconv i i.property).add_smul
            (mul_nonneg hp (w₁.nonneg i)) (mul_nonneg hq (w₂.nonneg i))]
          exact Set.mem_add.2
            ⟨(p * w₁.weights i) • x₁, Set.mem_smul_set.2 ⟨x₁, hx₁, by rw [mul_smul]⟩,
              (q * w₂.weights i) • x₂, Set.mem_smul_set.2 ⟨x₂, hx₂, by rw [mul_smul]⟩,
              by abel_nf⟩)
    · intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨w, hx⟩
      rcases (Set.mem_fintype_sum (fun i : s ↦ w.weights i • C i) x).1 hx with ⟨g, hg, hsum⟩
      choose z hzC hzEq using fun i : s ↦ Set.mem_smul_set.1 (hg i)
      have hzmem : ∀ i : s, z i ∈ ⋃ j ∈ s, C j := by
        intro i
        exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨i.property, hzC i⟩⟩
      have hx' : ∑ i : s, w.weights i • z i = x := by
        simpa [hzEq] using hsum
      have hwtotal : ∑ i : s, w.weights i = (1 : 𝕜) := by
        rw [← Finsupp.sum_fintype w.weights (fun _ r ↦ r) (by simp)]
        exact w.total
      exact
        (convexHull_mono fun y hy ↦ by
          rcases Set.mem_range.1 hy with ⟨i, rfl⟩
          exact hzmem i)
          (mem_convexHull_of_exists_fintype w.weights z (fun i ↦ w.nonneg i)
            hwtotal
            (fun i ↦ Set.mem_range_self i) hx')
  rw [hweighted]
  apply Set.iUnion_congr
  intro w
  ext x
  have hsum_eq : w.sum (fun i a ↦ a • C i) = ∑ i : s, w.weights i • C i := by
    simpa using
      (StdSimplex.sum_smul_set_eq_sum_weights_of_nonempty (w := w) (C := fun i : s ↦ C i)
        (fun i : s ↦ hnonempty i i.property))
  constructor <;> intro hx <;> simpa [hsum_eq] using hx

/-- Any point in the owner-side simplex sum over a finite support belongs to the convex hull of
the corresponding finite union. -/
private theorem mem_convexHull_iUnion_of_mem_simplex_sum
    {κ : Type*} (C : ι → Set E) (idx : κ → ι) (w : StdSimplex 𝕜 κ) {x : E}
    (hx : x ∈ w.sum (fun i a ↦ a • C (idx i))) :
    x ∈ convexHull 𝕜 (⋃ i, C i) := by
  have hx_support : x ∈ ∑ i ∈ w.weights.support, w.weights i • C (idx i) := by
    simpa [Finsupp.sum] using hx
  rcases (Set.mem_finset_sum w.weights.support (fun i : κ ↦ w.weights i • C (idx i)) x).1 hx_support
    with ⟨g, hg, hsum⟩
  let J := {i : κ // i ∈ w.weights.support}
  have hsum_support :
      (∑ i ∈ w.weights.support, w.weights i) = (1 : 𝕜) := by
    simpa [Finsupp.sum] using w.total
  have hsum_subtype :
      (∑ i ∈ w.weights.support, w.weights i) = ∑ i : J, w.weights i.1 := by
    classical
    simpa [J] using
      (Finset.sum_subtype (s := w.weights.support)
        (h := fun i : κ ↦ by simp)
        (f := fun i : κ ↦ w.weights i))
  have htotal : ∑ i : J, w.weights i.1 = (1 : 𝕜) := by
    exact hsum_subtype.symm.trans hsum_support
  have hsum_g_subtype : ∑ i : J, g i.1 = x := by
    have hsum_g :
        (∑ i ∈ w.weights.support, g i) = ∑ i : J, g i.1 := by
      classical
      simpa [J] using
        (Finset.sum_subtype (s := w.weights.support)
          (h := fun i : κ ↦ by simp)
          (f := fun i : κ ↦ g i))
    exact hsum_g.symm.trans hsum
  have hz_exists : ∀ i : J, ∃ z : E, z ∈ C (idx i.1) ∧ w.weights i.1 • z = g i.1 := by
    intro i
    rcases Set.mem_smul_set.1 (hg i.2) with ⟨z, hz, hzEq⟩
    exact ⟨z, hz, hzEq⟩
  choose z hzC hzEq using hz_exists
  have hzmem : ∀ i : J, z i ∈ ⋃ j, C j := by
    intro i
    exact Set.mem_iUnion.2 ⟨idx i.1, hzC i⟩
  have hx_subtype : ∑ i : J, w.weights i.1 • z i = x := by
    calc
      ∑ i : J, w.weights i.1 • z i = ∑ i : J, g i.1 := by
        refine Fintype.sum_congr (f := fun i : J ↦ w.weights i.1 • z i)
          (g := fun i : J ↦ g i.1) (fun i ↦ ?_)
        exact hzEq i
      _ = x := hsum_g_subtype
  exact
    mem_convexHull_of_exists_fintype (fun i : J ↦ w.weights i.1) z
      (fun i ↦ w.nonneg i.1) htotal hzmem hx_subtype

/-- Any point in the owner-side simplex sum over a finite support belongs to the convex hull of
the corresponding finite union. -/
private theorem mem_convexHull_iUnion_finset_of_mem_simplex_sum
    (C : ι → Set E) (s : Finset ι) (w : StdSimplex 𝕜 s) {x : E}
    (hx : x ∈ w.sum (fun i a ↦ a • C i)) :
    x ∈ convexHull 𝕜 (⋃ i ∈ s, C i) := by
  have hx' :
      x ∈ convexHull 𝕜 (⋃ i : s, C i) :=
    mem_convexHull_iUnion_of_mem_simplex_sum (C := fun i : s ↦ C i) (idx := fun i : s ↦ i)
      (w := w) (x := x) hx
  have hset : (⋃ i : s, C i) = ⋃ i ∈ s, C i := by
    ext y
    constructor
    · intro hy
      rcases Set.mem_iUnion.1 hy with ⟨i, hy⟩
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨i.property, hy⟩⟩
    · intro hy
      rcases Set.mem_iUnion.1 hy with ⟨i, hy⟩
      rcases Set.mem_iUnion.1 hy with ⟨hi, hy⟩
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩
  simpa [hset] using hx'

-- Bridge proof sketch for the finite-support convex-family surface:
-- first apply the canonical hull theorem
-- `convexHull_eq_union_convexHull_finite_subsets` directly to reduce to a finite subset of points
-- in the union, then record the indices of those points to obtain a finite support `s`. Rewrite
-- the resulting hull
-- `convexHull 𝕜 (⋃ i ∈ s, C i)` as the union of source-facing finite weighted set sums, then
-- pass to the owner-side simplex sum `w.sum (fun i a ↦ a • C i)`. For the reverse inclusion,
-- read `w.sum` on `w.weights.support`, and apply `mem_convexHull_of_exists_fintype`.
namespace Set

/-- Primitive indexed-owner form of Theorem 3.3: membership in `conv[𝕜] (⋃ i, C i)` is equivalent
to belonging to some finite indexed simplex-weighted sum of the family `C`, where the index map
`idx : κ → ι` is part of the owner data (so no convexity hypotheses on `C i` are needed at this
layer). This is the canonical owner-level API; the set-equality theorem
`conv_iUnion_eq_iUnion_simplex_sum` is its `iUnion` packaging. -/
theorem mem_conv_iUnion_iff_exists_simplex_sum
    (C : ι → Set E) {x : E} :
    x ∈ (conv[𝕜] (⋃ i, C i)) ↔
      ∃ (κ : Type) (w : StdSimplex 𝕜 κ) (idx : κ → ι),
        x ∈ w.sum (fun i a ↦ a • C (idx i)) := by
  classical
  constructor
  · intro hx
    rcases (mem_conv_iff_exists_fintype (s := ⋃ i, C i) (x := x)).1 hx with
      ⟨κ, _, a, z, ha₀, ha₁, hzUnion, hxsum⟩
    let w : StdSimplex 𝕜 κ :=
      { weights := Finsupp.equivFunOnFinite.symm a
        nonneg := by
          intro i
          simpa using ha₀ i
        total := by
          simpa [Finsupp.sum_fintype] using ha₁ }
    let idx : κ → ι := fun i ↦
      Classical.choose (Set.mem_iUnion.1 (hzUnion i))
    have hz : ∀ i, z i ∈ C (idx i) := by
      intro i
      exact Classical.choose_spec (Set.mem_iUnion.1 (hzUnion i))
    have hxsum' : w.sum (fun i r ↦ r • z i) = x := by
      simpa [w, Finsupp.sum_fintype] using hxsum
    have hx' : x ∈ w.sum (fun i a ↦ a • C (idx i)) := by
      have hx_support : x ∈ ∑ i ∈ w.weights.support, w.weights i • C (idx i) := by
        refine (Set.mem_finset_sum w.weights.support
          (fun i : κ ↦ w.weights i • C (idx i)) x).2 ?_
        refine ⟨fun i ↦ w.weights i • z i, ?_, ?_⟩
        · intro i hi
          exact Set.mem_smul_set.2 ⟨z i, hz i, rfl⟩
        · simpa [Finsupp.sum] using hxsum'
      simpa [StdSimplex.sum_smul_eq_sum_support (w := w) (z := fun i : κ ↦ C (idx i))]
        using hx_support
    exact ⟨κ, w, idx, hx'⟩
  · rintro ⟨κ, w, idx, hxw⟩
    simpa using
      (mem_convexHull_iUnion_of_mem_simplex_sum (C := C) (idx := idx) (w := w) (x := x) hxw)

/-- Primitive indexed-owner form of Theorem 3.3: membership in `conv[𝕜] (⋃ i, C i)` is equivalent
to belonging to some finite indexed simplex-weighted sum of the family `C`, where the index map
`idx : κ → ι` is part of the owner data (so no convexity hypotheses on `C i` are needed at this
layer). -/
theorem conv_iUnion_eq_iUnion_simplex_sum
    (C : ι → Set E) :
    (conv[𝕜] (⋃ i, C i)) =
      ⋃ (κ : Type) (w : StdSimplex 𝕜 κ) (idx : κ → ι),
        w.sum (fun i a ↦ a • C (idx i)) := by
  ext x
  simpa [Set.mem_iUnion] using (mem_conv_iUnion_iff_exists_simplex_sum (C := C) (x := x))

/-- Primitive indexed-owner refinement of Theorem 3.3: without any convexity hypothesis on the
family `C`, convexifying each fiber gives an exact indexed-simplex owner surface. -/
theorem conv_iUnion_eq_iUnion_simplex_sum_convexHull
    (C : ι → Set E) :
    (conv[𝕜] (⋃ i, C i)) =
      ⋃ (κ : Type) (w : StdSimplex 𝕜 κ) (idx : κ → ι),
        w.sum (fun i a ↦ a • conv[𝕜] (C (idx i))) := by
  have hmono :
      (⋃ i, C i) ⊆ ⋃ i, conv[𝕜] (C i) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
    exact Set.mem_iUnion.2 ⟨i, subset_convexHull 𝕜 (C i) hxi⟩
  have hconv :
      (⋃ i, conv[𝕜] (C i)) ⊆ conv[𝕜] (⋃ i, C i) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
    exact (convexHull_mono fun y hy ↦ Set.mem_iUnion.2 ⟨i, hy⟩) hxi
  calc
    (conv[𝕜] (⋃ i, C i)) = conv[𝕜] (⋃ i, conv[𝕜] (C i)) := by
      refine (convexHull_mono hmono).antisymm ?_
      exact convexHull_min hconv (convex_convexHull 𝕜 (⋃ i, C i))
    _ =
        ⋃ (κ : Type) (w : StdSimplex 𝕜 κ) (idx : κ → ι),
          w.sum (fun i a ↦ a • conv[𝕜] (C (idx i))) := by
      simpa using (conv_iUnion_eq_iUnion_simplex_sum (C := fun i ↦ conv[𝕜] (C i)))

/-- Primitive finite-support bridge form of Theorem 3.3: without any convexity hypothesis on the
family `C`, the finite-support simplex-sum surface is obtained by convexifying each fiber
`C i`. -/
theorem conv_iUnion_eq_iUnion_finset_simplex_sum_convexHull
    (C : ι → Set E) :
    (conv[𝕜] (⋃ i, C i)) =
      ⋃ s : Finset ι, ⋃ w : StdSimplex 𝕜 s, w.sum (fun i a ↦ a • conv[𝕜] (C i)) := by
  ext x
  classical
  constructor
  · intro hx
    have hx : x ∈ convexHull 𝕜 (⋃ i, C i) := by
      simpa using hx
    have hx :
        x ∈ ⋃ (t : Finset E) (_ : ↑t ⊆ ⋃ i, C i), convexHull 𝕜 ↑t := by
      simpa [convexHull_eq_union_convexHull_finite_subsets (⋃ i, C i : Set E), Set.mem_iUnion]
        using hx
    rcases Set.mem_iUnion.1 hx with ⟨t, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨ht, hx⟩
    choose idx hidx using fun y : {y // y ∈ t} ↦ by
      have hy : (y : E) ∈ ⋃ i, C i := ht y.property
      simpa [Set.mem_iUnion] using hy
    let s : Finset ι := t.attach.image idx
    have hs_nonempty : ∀ i ∈ s, (conv[𝕜] (C i)).Nonempty := by
      intro i hi
      rcases Finset.mem_image.1 hi with ⟨y, _, rfl⟩
      exact ⟨(y : E), (subset_convexHull 𝕜 (C (idx y))) (hidx y)⟩
    have hsubfamily : (↑t : Set E) ⊆ ⋃ i ∈ s, conv[𝕜] (C i) := by
      intro y hy
      have hy' : y ∈ conv[𝕜] (C (idx ⟨y, hy⟩)) :=
        (subset_convexHull 𝕜 (C (idx ⟨y, hy⟩))) (hidx ⟨y, hy⟩)
      have hs : idx ⟨y, hy⟩ ∈ s := by
        refine Finset.mem_image.2 ?_
        exact ⟨⟨y, hy⟩, by simp, rfl⟩
      exact Set.mem_iUnion.2 ⟨idx ⟨y, hy⟩, Set.mem_iUnion.2 ⟨hs, hy'⟩⟩
    have hx' : x ∈ convexHull 𝕜 (⋃ i ∈ s, conv[𝕜] (C i)) := (convexHull_mono hsubfamily) hx
    rw [convexHull_iUnion_finset_eq_iUnion_simplex_sum (C := fun i ↦ conv[𝕜] (C i)) s
      (fun i _ ↦ convex_convexHull 𝕜 (C i)) hs_nonempty] at hx'
    exact Set.mem_iUnion.2 ⟨s, hx'⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨w, hxw⟩
    have hx' : x ∈ convexHull 𝕜 (⋃ i ∈ s, conv[𝕜] (C i)) :=
      mem_convexHull_iUnion_finset_of_mem_simplex_sum (C := fun i ↦ conv[𝕜] (C i)) s w hxw
    have hsubfamily :
        (⋃ i ∈ s, conv[𝕜] (C i)) ⊆ convexHull 𝕜 (⋃ i, C i) := by
      intro y hy
      rcases Set.mem_iUnion.1 hy with ⟨i, hy⟩
      rcases Set.mem_iUnion.1 hy with ⟨_, hy⟩
      exact (convexHull_mono fun z hz ↦ Set.mem_iUnion.2 ⟨i, hz⟩) hy
    have hx'' : x ∈ convexHull 𝕜 (⋃ i, C i) :=
      (convexHull_min hsubfamily (convex_convexHull 𝕜 (⋃ i, C i))) hx'
    simpa using hx''

/-- Theorem 3.3 on the chapter finite-support surface: if each `C i` is convex, then the convex
hull of the union equals the union of finite simplex-weighted sums indexed by finite supports
`s : Finset ι`. This is the convex-family specialization of
`Set.conv_iUnion_eq_iUnion_finset_simplex_sum_convexHull`. -/
theorem conv_iUnion_eq_iUnion_simplex_sum_of_convex
    (C : ι → Set E) (hconv : ∀ i, Convex 𝕜 (C i)) :
    (conv[𝕜] (⋃ i, C i)) =
      ⋃ s : Finset ι, ⋃ w : StdSimplex 𝕜 s, w.sum (fun i a ↦ a • C i) := by
  have hC : ∀ i : ι, convexHull 𝕜 (C i) = C i := fun i ↦ (hconv i).convexHull_eq
  simpa [hC] using
    (conv_iUnion_eq_iUnion_finset_simplex_sum_convexHull (𝕜 := 𝕜) (C := C))

end Set

end
