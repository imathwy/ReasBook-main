import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_4_2

open scoped unitInterval

universe u v

variable {ι : Type u} {B : Type v} [TopologicalSpace B]

-- Semantic recall via `lean_leansearch` did not surface a pre-existing patching-neighborhood API;
-- the textbook `B^I` is therefore modeled directly by `C(I, B)`, with the ordered finite
-- subfamilies represented by lists of cover indices and the refined step carrying explicit finite
-- predecessor data.

namespace NumerableOpenCover

/-- An ordered finite subfamily of the cover, encoded by a nodup list of indices. -/
abbrev OrderedSubfamily (ι : Type u) := { T : List ι // T.Nodup }

namespace OrderedSubfamily

/-- The underlying list of indices. -/
def toList (T : OrderedSubfamily ι) : List ι := T.1

instance : Coe (OrderedSubfamily ι) (List ι) where
  coe := toList

/-- The size of an ordered finite subfamily. -/
def length (T : OrderedSubfamily ι) : ℕ := T.toList.length

/-- The `j`th member of an ordered finite subfamily. -/
def get (T : OrderedSubfamily ι) (j : Fin T.length) : ι :=
  T.toList.get ⟨j.1, j.2⟩

/-- The ordered sublists of an ordered finite subfamily. -/
def sublists (T : OrderedSubfamily ι) : List (List ι) := T.toList.sublists

end OrderedSubfamily

/-- The `j`th closed subinterval in the `T.length`-piece subdivision of `I`. -/
def patchingSlot (T : List ι) (j : Fin T.length) : Set I :=
  { t | ((j : ℕ) : ℝ) / T.length ≤ (t : ℝ) ∧
      (t : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / T.length }

namespace OrderedSubfamily

/-- The `j`th closed subinterval in the subdivision attached to an ordered finite subfamily. -/
def patchingSlot (T : OrderedSubfamily ι) (j : Fin T.length) : Set I :=
  _root_.NumerableOpenCover.patchingSlot T.toList ⟨j.1, j.2⟩

end OrderedSubfamily

/-- The raw real-valued patching weight attached to the ordered finite subfamily `T`. For the
empty list it is defined to be `0`, since the textbook construction only applies to nonempty
ordered subfamilies. -/
noncomputable def patchingWeightReal (𝒰 : NumerableOpenCover ι B) (T : OrderedSubfamily ι) :
    C(I, B) → ℝ := by
  classical
  exact fun β ↦
    if hT : 0 < T.length then
      sInf <| Set.range fun x : Fin T.length × I ↦
        if x.2 ∈ T.patchingSlot x.1 then
          (𝒰 (T.get x.1) (β x.2) : ℝ)
        else
          1
    else
      0

/-- Helper for Construction 7.4.4: each subdivision slot is nonempty. -/
theorem patchingSlot_nonempty (T : OrderedSubfamily ι) (j : Fin T.length) :
    (T.patchingSlot j).Nonempty := by
  -- Use the left endpoint of the `j`th interval as a canonical point in the slot.
  have hlenNat : 0 < T.length := by
    have hsucc : 1 ≤ T.length := by
      exact le_trans (Nat.succ_le_of_lt (Nat.zero_lt_succ (j : ℕ))) (Nat.succ_le_of_lt j.2)
    exact Nat.succ_le_iff.mp hsucc
  have hlen : (0 : ℝ) < T.length := by
    exact_mod_cast hlenNat
  have hleft_le_one : (((j : ℕ) : ℝ) / T.length) ≤ 1 := by
    have hj_le : ((j : ℕ) : ℝ) ≤ T.length := by
      exact_mod_cast Nat.le_of_lt j.2
    calc
      (((j : ℕ) : ℝ) / T.length) ≤ (T.length : ℝ) / T.length := by
        exact div_le_div_of_nonneg_right hj_le (le_of_lt hlen)
      _ = 1 := by rw [div_self (show (T.length : ℝ) ≠ 0 by positivity)]
  refine ⟨⟨((j : ℕ) : ℝ) / T.length, ⟨by positivity, hleft_le_one⟩⟩, ?_⟩
  -- The left endpoint obviously satisfies the left inequality, and it lies below the right one.
  rw [OrderedSubfamily.patchingSlot, patchingSlot]
  constructor
  · exact le_rfl
  · have hj_succ : (((j : ℕ) : ℝ) : ℝ) ≤ ((((j : ℕ) + 1 : ℕ) : ℝ) : ℝ) := by
      exact_mod_cast Nat.le_succ (j : ℕ)
    exact div_le_div_of_nonneg_right hj_succ (le_of_lt hlen)

/-- Helper for Construction 7.4.4: each subdivision slot is a compact subset of `I`. -/
theorem isCompact_patchingSlot (T : OrderedSubfamily ι) (j : Fin T.length) :
    IsCompact (T.patchingSlot j) := by
  -- Each slot is cut out by closed order conditions inside the compact interval `I`.
  rw [OrderedSubfamily.patchingSlot, patchingSlot]
  have hclosedLeft :
      IsClosed { t : I | ((j : ℕ) : ℝ) / T.length ≤ (t : ℝ) } :=
    isClosed_le continuous_const continuous_subtype_val
  have hclosedRight :
      IsClosed { t : I | (t : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / T.length } :=
    isClosed_le continuous_subtype_val continuous_const
  simpa [Set.setOf_and] using (hclosedLeft.inter hclosedRight).isCompact

/-- Helper for Construction 7.4.4: the `j`th slot contributes the minimum cover weight along that
closed subinterval. -/
noncomputable def slotWeightReal (𝒰 : NumerableOpenCover ι B) (T : OrderedSubfamily ι)
    (j : Fin T.length) : C(I, B) → ℝ :=
  fun β ↦ sInf ((fun t : I ↦ (𝒰 (T.get j) (β t) : ℝ)) '' T.patchingSlot j)

/-- Helper for Construction 7.4.4: each slot minimum lies in `[0, 1]`. -/
theorem slotWeightReal_mem_unitInterval (𝒰 : NumerableOpenCover ι B) (T : OrderedSubfamily ι)
    (j : Fin T.length) (β : C(I, B)) :
    slotWeightReal 𝒰 T j β ∈ Set.Icc (0 : ℝ) 1 := by
  -- The slot image is nonempty and every value of the numerating function already lies in `I`.
  let slotImage : Set ℝ := (fun t : I ↦ (𝒰 (T.get j) (β t) : ℝ)) '' T.patchingSlot j
  have hslotNonempty : slotImage.Nonempty := by
    rcases patchingSlot_nonempty T j with ⟨t, ht⟩
    exact ⟨(𝒰 (T.get j) (β t) : ℝ), ⟨t, ht, rfl⟩⟩
  have hslotBddBelow : BddBelow slotImage := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨t, -, rfl⟩
    exact (𝒰 (T.get j) (β t)).2.1
  constructor
  · -- The infimum is bounded below by `0` because every slot value is nonnegative.
    apply le_csInf hslotNonempty
    intro y hy
    rcases hy with ⟨t, -, rfl⟩
    exact (𝒰 (T.get j) (β t)).2.1
  · -- A concrete slot point witnesses the upper bound by `1`.
    rcases patchingSlot_nonempty T j with ⟨t, ht⟩
    have ht_mem : (𝒰 (T.get j) (β t) : ℝ) ∈ slotImage := ⟨t, ht, rfl⟩
    exact le_trans (csInf_le hslotBddBelow ht_mem) (𝒰 (T.get j) (β t)).2.2

/-- Helper for Construction 7.4.4: the slot minimum depends continuously on the path. -/
theorem continuousSlotWeightReal (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (T : OrderedSubfamily ι) (j : Fin T.length) :
    Continuous (slotWeightReal 𝒰 T j) := by
  -- The evaluation map is continuous on `C(I, B) × I`, so compact-slot infima vary continuously.
  let f : C(I, B) → I → ℝ := fun β t ↦ (𝒰 (T.get j) (β t) : ℝ)
  have hf : Continuous ↿f := by
    have hEval : Continuous fun z : C(I, B) × I ↦ z.1 z.2 :=
      continuous_fst.eval continuous_snd
    exact continuous_subtype_val.comp ((hcont (T.get j)).comp hEval)
  simpa [slotWeightReal, f] using (isCompact_patchingSlot T j).continuous_sInf hf

/-- Helper for Construction 7.4.4: for nonempty `T`, the raw patching weight is the finite infimum
of the slot minima. -/
theorem patchingWeightReal_eq_finsetInfSlotWeights (𝒰 : NumerableOpenCover ι B)
    (T : OrderedSubfamily ι) (hT : 0 < T.length) (β : C(I, B)) :
    patchingWeightReal 𝒰 T β =
      (Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨0, hT⟩)
        fun j : Fin T.length ↦ slotWeightReal 𝒰 T j β) := by
  classical
  let rawSet : Set ℝ :=
    Set.range fun x : Fin T.length × I ↦
      if x.2 ∈ T.patchingSlot x.1 then
        (𝒰 (T.get x.1) (β x.2) : ℝ)
      else
        1
  let hne : (Finset.univ : Finset (Fin T.length)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨0, hT⟩
  have hrawBddBelow : BddBelow rawSet := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨x, rfl⟩
    by_cases hx : x.2 ∈ T.patchingSlot x.1
    · simpa [hx] using (𝒰 (T.get x.1) (β x.2)).2.1
    · simp [hx]
  have hrawLeSlot :
      ∀ j : Fin T.length, sInf rawSet ≤ slotWeightReal 𝒰 T j β := by
    intro j
    let slotImage : Set ℝ := (fun t : I ↦ (𝒰 (T.get j) (β t) : ℝ)) '' T.patchingSlot j
    have hslotBddBelow : BddBelow slotImage := by
      refine ⟨0, ?_⟩
      intro y hy
      rcases hy with ⟨t, -, rfl⟩
      exact (𝒰 (T.get j) (β t)).2.1
    apply le_csInf
    · rcases patchingSlot_nonempty T j with ⟨t, ht⟩
      exact ⟨(𝒰 (T.get j) (β t) : ℝ), ⟨t, ht, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨t, ht, rfl⟩
      have hrawMem :
          (𝒰 (T.get j) (β t) : ℝ) ∈ rawSet := by
        refine ⟨(j, t), ?_⟩
        simp [ht]
      exact csInf_le hrawBddBelow hrawMem
  have hrawLeFinset :
      sInf rawSet ≤
        (Finset.univ.inf' hne fun j : Fin T.length ↦ slotWeightReal 𝒰 T j β) := by
    rw [Finset.le_inf'_iff hne]
    intro j hj
    exact hrawLeSlot j
  have hfinsetLeRaw :
      (Finset.univ.inf' hne fun j : Fin T.length ↦ slotWeightReal 𝒰 T j β) ≤ sInf rawSet := by
    apply le_csInf
    · rcases hne with ⟨j⟩
      rcases patchingSlot_nonempty T j with ⟨t, ht⟩
      refine ⟨(𝒰 (T.get j) (β t) : ℝ), ?_⟩
      refine ⟨(j, t), ?_⟩
      simp [ht]
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      by_cases hx : x.2 ∈ T.patchingSlot x.1
      · have hslot :
            slotWeightReal 𝒰 T x.1 β ≤ (𝒰 (T.get x.1) (β x.2) : ℝ) := by
          let slotImage : Set ℝ := (fun t : I ↦ (𝒰 (T.get x.1) (β t) : ℝ)) '' T.patchingSlot x.1
          have hslotBddBelow : BddBelow slotImage := by
            refine ⟨0, ?_⟩
            intro z hz
            rcases hz with ⟨t, -, rfl⟩
            exact (𝒰 (T.get x.1) (β t)).2.1
          have hxMem : (𝒰 (T.get x.1) (β x.2) : ℝ) ∈ slotImage := ⟨x.2, hx, rfl⟩
          exact csInf_le hslotBddBelow hxMem
        simpa [rawSet, hx] using
          le_trans (Finset.inf'_le (fun j : Fin T.length ↦ slotWeightReal 𝒰 T j β)
            (Finset.mem_univ x.1)) hslot
      · rcases hne with ⟨j₀⟩
        have hslotLeOne : slotWeightReal 𝒰 T j₀ β ≤ 1 :=
          (slotWeightReal_mem_unitInterval 𝒰 T j₀ β).2
        simpa [rawSet, hx] using
          le_trans
            (Finset.inf'_le (fun j : Fin T.length ↦ slotWeightReal 𝒰 T j β)
              (Finset.mem_univ j₀))
            hslotLeOne
  -- Compare the original `if`-based infimum with the finite slot infimum in both directions.
  have hraw :
      patchingWeightReal 𝒰 T β = sInf rawSet := by
    simp [patchingWeightReal, rawSet, hT]
  rw [hraw]
  exact le_antisymm hrawLeFinset hfinsetLeRaw

/-- `patchingWeightReal 𝒰 T β` takes values in `I`. -/
theorem patchingWeightReal_mem_unitInterval (𝒰 : NumerableOpenCover ι B)
    (T : OrderedSubfamily ι) (β : C(I, B)) :
  patchingWeightReal 𝒰 T β ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hT : 0 < T.length
  · -- For nonempty `T`, rewrite to the finite slot infimum and bound each slot separately.
    let hne : (Finset.univ : Finset (Fin T.length)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨0, hT⟩
    rw [patchingWeightReal_eq_finsetInfSlotWeights 𝒰 T hT β]
    constructor
    · rw [Finset.le_inf'_iff hne]
      intro j hj
      exact (slotWeightReal_mem_unitInterval 𝒰 T j β).1
    · rcases hne with ⟨j⟩
      exact le_trans
        (Finset.inf'_le (fun j : Fin T.length ↦ slotWeightReal 𝒰 T j β) (Finset.mem_univ j))
        (slotWeightReal_mem_unitInterval 𝒰 T j β).2
  · -- The empty ordered subfamily uses the definitional zero branch.
    simp [patchingWeightReal, hT]

/-- The `I`-valued patching weight varies continuously with the path. -/
theorem continuous_patchingWeight (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (T : OrderedSubfamily ι) :
    Continuous fun β ↦
      (⟨patchingWeightReal 𝒰 T β, patchingWeightReal_mem_unitInterval 𝒰 T β⟩ : I) := by
  classical
  by_cases hT : 0 < T.length
  · -- After rewriting to a finite infimum of slot minima, continuity is inherited slotwise.
    let hne : (Finset.univ : Finset (Fin T.length)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨0, hT⟩
    have hreal : Continuous fun β ↦ patchingWeightReal 𝒰 T β := by
      have hEq :
          (fun β ↦ patchingWeightReal 𝒰 T β) =
            fun β ↦
              Finset.univ.inf' hne (fun j : Fin T.length ↦ slotWeightReal 𝒰 T j β) := by
        funext β
        exact patchingWeightReal_eq_finsetInfSlotWeights 𝒰 T hT β
      rw [hEq]
      exact Continuous.finset_inf'_apply hne fun j _ ↦ continuousSlotWeightReal 𝒰 hcont T j
    exact hreal.subtype_mk fun β ↦ patchingWeightReal_mem_unitInterval 𝒰 T β
  · -- The empty ordered subfamily gives the constant zero function.
    have hEq :
        (fun β ↦ (⟨patchingWeightReal 𝒰 T β, patchingWeightReal_mem_unitInterval 𝒰 T β⟩ : I)) =
          fun _ : C(I, B) ↦ (0 : I) := by
      funext β
      apply Subtype.ext
      simp [patchingWeightReal, hT]
    rw [hEq]
    exact continuous_const

/-- For an ordered finite subfamily `T` of members of the numerable cover `𝒰`, the extra
hypothesis `hcont : ∀ i, Continuous (𝒰 i)` lets `patchingWeight 𝒰 hcont T : C(I, B) → I` package
May's path-space function `λ_T`. -/
noncomputable def patchingWeight (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    (T : OrderedSubfamily ι) :
    C(C(I, B), I) where
  toFun β := ⟨patchingWeightReal 𝒰 T β, patchingWeightReal_mem_unitInterval 𝒰 T β⟩
  continuous_toFun := continuous_patchingWeight 𝒰 hcont T

/-- Coercing `patchingWeight 𝒰 hcont T β` to `ℝ` recovers the underlying raw patching weight. -/
theorem coe_patchingWeight_apply (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    (T : OrderedSubfamily ι) (β : C(I, B)) :
    (patchingWeight 𝒰 hcont T β : ℝ) = patchingWeightReal 𝒰 T β := by
  -- `patchingWeight` is defined by packaging the raw real weight into `I`.
  rfl

/-- The positivity locus of `patchingWeight 𝒰 hcont T` is open. -/
theorem isOpen_patchingOpen (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    (T : OrderedSubfamily ι) :
    IsOpen { β | 0 < patchingWeight 𝒰 hcont T β } := by
  -- Positivity is the preimage of an open order interval under a continuous `I`-valued map.
  simpa using isOpen_lt continuous_const (patchingWeight 𝒰 hcont T).continuous

/-- The basic patching neighborhood `W_T ⊆ C(I, B)` from Construction 7.4.4 (1), cut out by the
positivity of `patchingWeight 𝒰 hcont T` for an ordered finite subfamily `T` of members of the
numerable cover `𝒰`. -/
noncomputable def patchingOpen (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    (T : OrderedSubfamily ι) :
    TopologicalSpace.Opens (C(I, B)) where
  carrier := { β | 0 < patchingWeight 𝒰 hcont T β }
  is_open' := isOpen_patchingOpen 𝒰 hcont T

/-- A finite ordered predecessor family used to define the refined neighborhood attached to the
ordered finite subset `T`. -/
structure PatchingRefinement (T : List ι) where
  /-- A finite indexing type for the predecessor lists entering the refinement step. -/
  predecessor : Type u
  /-- The predecessor indexing type is finite. -/
  [finite_predecessor : Fintype predecessor]
  /-- The predecessor ordered subfamilies used in the refinement step. -/
  predecessorList : predecessor → List ι
  /-- The source family `T` is an ordered finite subset of the cover. -/
  nodup : T.Nodup
  /-- Each predecessor family is an ordered subfamily of `T`. -/
  predecessor_sublist : ∀ a, List.Sublist (predecessorList a) T
  /-- Each predecessor family is shorter than `T`. -/
  shorter : ∀ a, (predecessorList a).length < T.length
  /-- Each predecessor family is itself an ordered finite subset. -/
  predecessor_nodup : ∀ a, (predecessorList a).Nodup

/-- The ordered finite subfamily underlying a refinement datum. -/
def PatchingRefinement.orderedSubfamily {T : List ι} (refinement : PatchingRefinement T) :
    OrderedSubfamily ι :=
  ⟨T, refinement.nodup⟩

/-- A predecessor list viewed as an ordered finite subfamily. -/
def PatchingRefinement.predecessorSubfamily {T : List ι} (refinement : PatchingRefinement T)
    (a : refinement.predecessor) : OrderedSubfamily ι :=
  ⟨refinement.predecessorList a, refinement.predecessor_nodup a⟩

/-- The raw real-valued trimmed patching weight `γ_T` attached to the ordered subfamily `T` and
an explicit finite predecessor family driving the refinement step. -/
noncomputable def patchingRefinedWeightRealFrom (𝒰 : NumerableOpenCover ι B) {T : List ι}
    (refinement : PatchingRefinement T) :
    C(I, B) → ℝ :=
  fun β ↦
    let _ := refinement.finite_predecessor
    max 0 <|
      patchingWeightReal 𝒰 refinement.orderedSubfamily β -
        (T.length : ℝ) * ∑ a : refinement.predecessor,
          patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β

/-- `patchingRefinedWeightRealFrom 𝒰 refinement β` takes values in `I`. -/
theorem patchingRefinedWeightRealFrom_mem_unitInterval (𝒰 : NumerableOpenCover ι B) {T : List ι}
    (refinement : PatchingRefinement T) (β : C(I, B)) :
    patchingRefinedWeightRealFrom 𝒰 refinement β ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  let _ := refinement.finite_predecessor
  let predecessorWeight : refinement.predecessor → ℝ :=
    fun a ↦ patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β
  have hmain :
      patchingWeightReal 𝒰 refinement.orderedSubfamily β ≤ 1 :=
    (patchingWeightReal_mem_unitInterval 𝒰 refinement.orderedSubfamily β).2
  have hsumNonneg : 0 ≤ ∑ a : refinement.predecessor, predecessorWeight a := by
    apply Finset.sum_nonneg
    intro a ha
    exact (patchingWeightReal_mem_unitInterval 𝒰 (refinement.predecessorSubfamily a) β).1
  have hinnerLeOne :
      patchingWeightReal 𝒰 refinement.orderedSubfamily β -
          (T.length : ℝ) * ∑ a : refinement.predecessor, predecessorWeight a ≤ 1 := by
    have hscaledNonneg :
        0 ≤ (T.length : ℝ) * ∑ a : refinement.predecessor, predecessorWeight a := by
      positivity
    linarith
  constructor
  · -- The outer `max 0` forces nonnegativity.
    simp [patchingRefinedWeightRealFrom]
  · -- The outer `max 0` preserves the bound by `1`.
    change max 0
        (patchingWeightReal 𝒰 refinement.orderedSubfamily β -
          (T.length : ℝ) * ∑ a : refinement.predecessor, predecessorWeight a) ≤ 1
    exact max_le_iff.mpr ⟨by norm_num, hinnerLeOne⟩

/-- The `I`-valued refined patching weight varies continuously with the path. -/
theorem continuous_patchingRefinedWeightFrom (𝒰 : NumerableOpenCover ι B) {T : List ι}
    (hcont : ∀ i, Continuous (𝒰 i)) (refinement : PatchingRefinement T) :
    Continuous fun β ↦
      (⟨patchingRefinedWeightRealFrom 𝒰 refinement β,
        patchingRefinedWeightRealFrom_mem_unitInterval 𝒰 refinement β⟩ : I) := by
  classical
  let _ := refinement.finite_predecessor
  have hmain :
      Continuous fun β ↦ patchingWeightReal 𝒰 refinement.orderedSubfamily β := by
    exact continuous_subtype_val.comp
      (continuous_patchingWeight 𝒰 hcont refinement.orderedSubfamily)
  have hpred :
      Continuous fun β ↦
        ∑ a : refinement.predecessor,
          patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β := by
    apply continuous_finset_sum
    intro a ha
    exact continuous_subtype_val.comp
      (continuous_patchingWeight 𝒰 hcont (refinement.predecessorSubfamily a))
  have hreal : Continuous fun β ↦ patchingRefinedWeightRealFrom 𝒰 refinement β := by
    -- The refined weight is built from continuous arithmetic operations on the basic weights.
    have hinner :
        Continuous fun β ↦
          patchingWeightReal 𝒰 refinement.orderedSubfamily β -
            (T.length : ℝ) *
              ∑ a : refinement.predecessor,
                patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β := by
      continuity
    simpa [patchingRefinedWeightRealFrom] using (continuous_const.max hinner)
  exact hreal.subtype_mk fun β ↦ patchingRefinedWeightRealFrom_mem_unitInterval 𝒰 refinement β

/-- The bridge-form `I`-valued trimmed patching function `γ_T : C(I, B) → I` defined from explicit
finite predecessor data for the ordered subfamily `T`. -/
noncomputable def patchingRefinedWeightFrom (𝒰 : NumerableOpenCover ι B) {T : List ι}
    (hcont : ∀ i, Continuous (𝒰 i)) (refinement : PatchingRefinement T) :
    C(C(I, B), I) where
  toFun β := ⟨patchingRefinedWeightRealFrom 𝒰 refinement β,
    patchingRefinedWeightRealFrom_mem_unitInterval 𝒰 refinement β⟩
  continuous_toFun := continuous_patchingRefinedWeightFrom 𝒰 hcont refinement

/-- The bridge-form refined open set `V_T ⊆ C(I, B)` cut out by the positivity of
`patchingRefinedWeightFrom 𝒰 hcont refinement`. -/
theorem isOpen_patchingRefinedOpenFrom (𝒰 : NumerableOpenCover ι B) {T : List ι}
    (hcont : ∀ i, Continuous (𝒰 i)) (refinement : PatchingRefinement T) :
    IsOpen { β | 0 < patchingRefinedWeightFrom 𝒰 hcont refinement β } := by
  -- Positivity is the preimage of an open order interval under the refined continuous map.
  simpa using isOpen_lt continuous_const (patchingRefinedWeightFrom 𝒰 hcont refinement).continuous

/-- The refined open set cut out by the positivity of
`patchingRefinedWeightFrom 𝒰 hcont refinement`. -/
noncomputable def patchingRefinedOpenFrom (𝒰 : NumerableOpenCover ι B) {T : List ι}
    (hcont : ∀ i, Continuous (𝒰 i)) (refinement : PatchingRefinement T) :
    TopologicalSpace.Opens (C(I, B)) where
  carrier := { β | 0 < patchingRefinedWeightFrom 𝒰 hcont refinement β }
  is_open' := isOpen_patchingRefinedOpenFrom 𝒰 hcont refinement

/-- The canonical finite predecessor family attached to the ordered finite subfamily `T`, indexed
by the proper ordered subfamilies appearing in `T.sublists`. -/
noncomputable def patchingRefinement (T : OrderedSubfamily ι) : PatchingRefinement T.toList where
  predecessor := ULift.{u} { a : Fin T.sublists.length // (T.sublists.get a).length < T.length }
  finite_predecessor := inferInstance
  predecessorList a := T.sublists.get a.down.1
  nodup := T.2
  predecessor_sublist := by
    intro a
    -- Every entry of `T.sublists` is, by construction, a sublist of `T`.
    have hmem : T.sublists.get a.down.1 ∈ T.sublists := List.get_mem T.sublists a.down.1
    exact (List.mem_sublists.mp hmem)
  shorter := fun a ↦ a.down.2
  predecessor_nodup := by
    intro a
    -- A sublist of a nodup list is again nodup.
    have hmem : T.sublists.get a.down.1 ∈ T.sublists := List.get_mem T.sublists a.down.1
    exact List.Sublist.nodup (List.mem_sublists.mp hmem) T.2

/-- Helper for Construction 7.4.4: coercing the bridge-form refined patching function back to `ℝ`
recovers the underlying raw refined weight. -/
theorem coe_patchingRefinedWeightFrom_apply (𝒰 : NumerableOpenCover ι B) {T : List ι}
    (hcont : ∀ i, Continuous (𝒰 i)) (refinement : PatchingRefinement T) (β : C(I, B)) :
    (patchingRefinedWeightFrom 𝒰 hcont refinement β : ℝ) =
      patchingRefinedWeightRealFrom 𝒰 refinement β := by
  -- `patchingRefinedWeightFrom` is defined by packaging the raw refined weight into `I`.
  rfl

/-- The canonical raw refined patching weight `γ_T` attached to the ordered finite subfamily `T`. -/
noncomputable def patchingRefinedWeightReal (𝒰 : NumerableOpenCover ι B)
    (T : OrderedSubfamily ι) :
    C(I, B) → ℝ :=
  patchingRefinedWeightRealFrom 𝒰 (patchingRefinement T)

/-- The canonical raw refined patching weight is the bridge-form refined weight built from
`patchingRefinement T`. -/
@[simp] theorem patchingRefinedWeightReal_eq_from (𝒰 : NumerableOpenCover ι B)
    (T : OrderedSubfamily ι) :
    patchingRefinedWeightReal 𝒰 T = patchingRefinedWeightRealFrom 𝒰 (patchingRefinement T) := rfl

/-- `patchingRefinedWeightReal 𝒰 T β` takes values in `I`. -/
theorem patchingRefinedWeightReal_mem_unitInterval (𝒰 : NumerableOpenCover ι B)
    (T : OrderedSubfamily ι) (β : C(I, B)) :
    patchingRefinedWeightReal 𝒰 T β ∈ Set.Icc (0 : ℝ) 1 :=
  patchingRefinedWeightRealFrom_mem_unitInterval 𝒰 (patchingRefinement T) β

/-- The canonical refined patching weight varies continuously with the path. -/
theorem continuous_patchingRefinedWeight (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (T : OrderedSubfamily ι) :
    Continuous fun β ↦
      (⟨patchingRefinedWeightReal 𝒰 T β, patchingRefinedWeightReal_mem_unitInterval 𝒰 T β⟩ : I) :=
  continuous_patchingRefinedWeightFrom 𝒰 hcont (patchingRefinement T)

/-- The canonical `I`-valued trimmed patching function from Construction 7.4.4 (2),
`γ_T : C(I, B) → I`, attached to the ordered finite subfamily `T`. -/
noncomputable def patchingRefinedWeight (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (T : OrderedSubfamily ι) :
    C(C(I, B), I) where
  toFun β := ⟨patchingRefinedWeightReal 𝒰 T β, patchingRefinedWeightReal_mem_unitInterval 𝒰 T β⟩
  continuous_toFun := continuous_patchingRefinedWeight 𝒰 hcont T

/-- The canonical refined patching function is the bridge-form refined weight built from
`patchingRefinement T`. -/
@[simp] theorem patchingRefinedWeight_eq_from (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (T : OrderedSubfamily ι) :
    patchingRefinedWeight 𝒰 hcont T = patchingRefinedWeightFrom 𝒰 hcont (patchingRefinement T) :=
  rfl

/-- Coercing `patchingRefinedWeight 𝒰 hcont T β` to `ℝ` recovers the underlying raw refined
patching weight. -/
@[simp] theorem coe_patchingRefinedWeight_apply (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (T : OrderedSubfamily ι) (β : C(I, B)) :
    (patchingRefinedWeight 𝒰 hcont T β : ℝ) = patchingRefinedWeightReal 𝒰 T β := rfl

/-- The positivity locus of `patchingRefinedWeight 𝒰 hcont T` is open. -/
theorem isOpen_patchingRefinedOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (T : OrderedSubfamily ι) :
    IsOpen { β | 0 < patchingRefinedWeight 𝒰 hcont T β } := by
  simpa [patchingRefinedWeight_eq_from 𝒰 hcont T] using
    isOpen_patchingRefinedOpenFrom 𝒰 hcont (patchingRefinement T)

/-- Membership in `patchingOpen 𝒰 hcont T` means that on each subdivision interval the path lies
in the corresponding cover member from the ordered finite subfamily `T`. -/
theorem mem_patchingOpen_iff (𝒰 : NumerableOpenCover ι B) (hcont : ∀ i, Continuous (𝒰 i))
    {T : OrderedSubfamily ι} (hT_nonempty : 0 < T.length) (β : C(I, B)) :
    β ∈ patchingOpen 𝒰 hcont T ↔
      ∀ j : Fin T.length, ∀ t ∈ T.patchingSlot j, β t ∈ 𝒰.cover (T.get j) := by
  classical
  let hne : (Finset.univ : Finset (Fin T.length)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨0, hT_nonempty⟩
  change (0 : ℝ) < (patchingWeight 𝒰 hcont T β : ℝ) ↔
      ∀ j : Fin T.length, ∀ t ∈ T.patchingSlot j, β t ∈ 𝒰.cover (T.get j)
  rw [coe_patchingWeight_apply, patchingWeightReal_eq_finsetInfSlotWeights 𝒰 T hT_nonempty β]
  rw [Finset.lt_inf'_iff hne]
  constructor
  · intro hslot j t ht
    -- Slot positivity is exactly positivity of the numerating function on that interval.
    have hslot' : 0 < slotWeightReal 𝒰 T j β := hslot j (Finset.mem_univ j)
    have hcontOn :
        ContinuousOn (fun t : I ↦ (𝒰 (T.get j) (β t) : ℝ)) (T.patchingSlot j) := by
      exact (continuous_subtype_val.comp ((hcont (T.get j)).comp β.continuous)).continuousOn
    have hsInf :
        0 < sInf ((fun t : I ↦ (𝒰 (T.get j) (β t) : ℝ)) '' T.patchingSlot j) ↔
          ∀ x ∈ T.patchingSlot j, 0 < (𝒰 (T.get j) (β x) : ℝ) := by
      simpa using
        (isCompact_patchingSlot T j).lt_sInf_iff_of_continuous
          (patchingSlot_nonempty T j) hcontOn (0 : ℝ)
    exact (𝒰.mem_cover_iff_pos (T.get j) (β t)).2 ((hsInf.mp hslot') t ht)
  · intro hslot j hj
    have hcontOn :
        ContinuousOn (fun t : I ↦ (𝒰 (T.get j) (β t) : ℝ)) (T.patchingSlot j) := by
      exact (continuous_subtype_val.comp ((hcont (T.get j)).comp β.continuous)).continuousOn
    have hsInf :
        0 < sInf ((fun t : I ↦ (𝒰 (T.get j) (β t) : ℝ)) '' T.patchingSlot j) ↔
          ∀ x ∈ T.patchingSlot j, 0 < (𝒰 (T.get j) (β x) : ℝ) := by
      simpa using
        (isCompact_patchingSlot T j).lt_sInf_iff_of_continuous
          (patchingSlot_nonempty T j) hcontOn (0 : ℝ)
    exact hsInf.mpr fun t ht ↦ (𝒰.mem_cover_iff_pos (T.get j) (β t)).1 (hslot j t ht)

/-- Explicit predecessor data produces a refined neighborhood contained in the basic neighborhood
`W_T`. -/
theorem patchingRefinedOpenFrom_subset_patchingOpen (𝒰 : NumerableOpenCover ι B) {T : List ι}
    (hcont : ∀ i, Continuous (𝒰 i)) (refinement : PatchingRefinement T) :
    (patchingRefinedOpenFrom 𝒰 hcont refinement : Set (C(I, B))) ⊆
      patchingOpen 𝒰 hcont refinement.orderedSubfamily :=
  by
    let _ := refinement.finite_predecessor
    intro β hβ
    change (0 : ℝ) < (patchingRefinedWeightFrom 𝒰 hcont refinement β : ℝ) at hβ
    change (0 : ℝ) < (patchingWeight 𝒰 hcont refinement.orderedSubfamily β : ℝ)
    rw [coe_patchingRefinedWeightFrom_apply] at hβ
    rw [coe_patchingWeight_apply]
    have hsumNonneg :
        0 ≤ ∑ a : refinement.predecessor,
          patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β := by
      apply Finset.sum_nonneg
      intro a ha
      exact (patchingWeightReal_mem_unitInterval 𝒰 (refinement.predecessorSubfamily a) β).1
    have hinnerPos :
        0 <
          patchingWeightReal 𝒰 refinement.orderedSubfamily β -
            (T.length : ℝ) *
              ∑ a : refinement.predecessor,
                patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β := by
      -- Positivity of `max 0 (...)` forces positivity of the inner difference.
      simpa [patchingRefinedWeightRealFrom] using hβ
    have hscaledNonneg :
        0 ≤ (T.length : ℝ) *
          ∑ a : refinement.predecessor,
            patchingWeightReal 𝒰 (refinement.predecessorSubfamily a) β := by
      positivity
    linarith

/-- Construction 7.4.4: for each ordered finite subfamily `T` of members of the numerable cover
`𝒰`, the canonical refined patching neighborhood `V_T ⊆ C(I, B)` is obtained by applying the
refinement step to the finite family of proper ordered subfamilies of `T`. -/
noncomputable def patchingRefinedOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (T : OrderedSubfamily ι) :
    TopologicalSpace.Opens (C(I, B)) where
  carrier := { β | 0 < patchingRefinedWeight 𝒰 hcont T β }
  is_open' := isOpen_patchingRefinedOpen 𝒰 hcont T

/-- The canonical refined neighborhood is the bridge-form refined neighborhood built from
`patchingRefinement T`. -/
@[simp] theorem patchingRefinedOpen_eq_from (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (T : OrderedSubfamily ι) :
    patchingRefinedOpen 𝒰 hcont T = patchingRefinedOpenFrom 𝒰 hcont (patchingRefinement T) := rfl

/-- The canonical refined neighborhood `V_T` is contained in the basic patching neighborhood
`W_T`. -/
theorem patchingRefinedOpen_subset_patchingOpen (𝒰 : NumerableOpenCover ι B)
    (hcont : ∀ i, Continuous (𝒰 i)) (T : OrderedSubfamily ι) :
    (patchingRefinedOpen 𝒰 hcont T : Set (C(I, B))) ⊆ patchingOpen 𝒰 hcont T := by
  simpa [patchingRefinedOpen_eq_from 𝒰 hcont T] using
    patchingRefinedOpenFrom_subset_patchingOpen 𝒰 hcont (patchingRefinement T)

end NumerableOpenCover
