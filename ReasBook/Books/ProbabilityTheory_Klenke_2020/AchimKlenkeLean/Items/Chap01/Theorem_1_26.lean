import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_25
import ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_12

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

variable {Ω : Type u}

-- Proof sketch: `traceOn` is the pullback family along `Subtype.val`, while the measurable sets of
-- `m.comap Subtype.val` are definitionally the pullbacks of measurable sets of `m`.
/-- Theorem 1.26 (1): Restricting a σ-algebra to a subset `A` gives the σ-algebra on the subtype
`A` induced by `MeasurableSpace.comap`. -/
theorem traceOn_measurableSet_eq_comap (m : MeasurableSpace Ω) (A : Set Ω) :
    traceOn {s | MeasurableSet[m] s} A =
      {s | MeasurableSet[m.comap (Subtype.val : A → Ω)] s} := by
  ext s
  constructor
  · intro hs
    rcases mem_traceOn_iff.mp hs with ⟨t, ht, rfl⟩
    change MeasurableSet[m.comap (Subtype.val : A → Ω)] (Subtype.val ⁻¹' t)
    exact ⟨t, ht, rfl⟩
  · intro hs
    change MeasurableSet[m.comap (Subtype.val : A → Ω)] s at hs
    rcases hs with ⟨t, ht, hts⟩
    exact mem_traceOn_iff.mpr ⟨t, ht, hts.symm⟩

-- Proof sketch: pull back `∅`, complements, and binary unions along the subtype inclusion.
/-- Theorem 1.26 (2): Restricting an algebra of sets to a subset again yields an algebra of sets,
now on the subtype `A`. -/
theorem traceOn_isSetAlgebra (A : Set Ω) (C : Set (Set Ω)) (hC : IsSetAlgebra C) :
    IsSetAlgebra (traceOn C A) := by
  refine
    { empty_mem := ?_
      compl_mem := ?_
      union_mem := ?_ }
  · exact mem_traceOn_iff.mpr ⟨∅, hC.empty_mem, by ext x; simp⟩
  · intro s hs
    rcases mem_traceOn_iff.mp hs with ⟨t, ht, rfl⟩
    exact mem_traceOn_iff.mpr ⟨tᶜ, hC.compl_mem ht, by ext x; simp⟩
  · intro s t hs ht
    rcases mem_traceOn_iff.mp hs with ⟨u, hu, rfl⟩
    rcases mem_traceOn_iff.mp ht with ⟨v, hv, rfl⟩
    exact mem_traceOn_iff.mpr ⟨u ∪ v, hC.union_mem hu hv, by ext x; simp⟩

-- Proof sketch: pull back `∅`, differences, and unions along the subtype inclusion.
/-- Theorem 1.26 (3): Restricting a ring of sets to a subset again yields a ring of sets, now on
the subtype `A`. -/
theorem traceOn_isSetRing (A : Set Ω) (C : Set (Set Ω)) (hC : MeasureTheory.IsSetRing C) :
    MeasureTheory.IsSetRing (traceOn C A) := by
  refine
    { empty_mem := ?_
      diff_mem := ?_
      union_mem := ?_ }
  · exact mem_traceOn_iff.mpr ⟨∅, hC.empty_mem, by ext x; simp⟩
  · intro s t hs ht
    rcases mem_traceOn_iff.mp hs with ⟨u, hu, rfl⟩
    rcases mem_traceOn_iff.mp ht with ⟨v, hv, rfl⟩
    exact mem_traceOn_iff.mpr ⟨u ∪ v, hC.union_mem hu hv, by ext x; simp⟩
  · intro s t hs ht
    rcases mem_traceOn_iff.mp hs with ⟨u, hu, rfl⟩
    rcases mem_traceOn_iff.mp ht with ⟨v, hv, rfl⟩
    exact mem_traceOn_iff.mpr ⟨u \ v, hC.diff_mem hu hv, by ext x; simp⟩

-- Proof sketch: combine preservation of the ring-of-sets axioms under pullback with preservation
-- of countable unions.
/-- Theorem 1.26 (4): Restricting a sigma-ring of sets to a subset again yields a sigma-ring of
sets, now on the subtype `A`. -/
theorem traceOn_isSetSigmaRing (A : Set Ω) (C : Set (Set Ω)) (hC : IsSetSigmaRing C) :
    IsSetSigmaRing (traceOn C A) := by
  refine
    { traceOn_isSetRing A C hC.toIsSetRing with
      iUnion_mem := ?_ }
  intro s hs
  choose t htC hts using fun n ↦ mem_traceOn_iff.mp (hs n)
  exact mem_traceOn_iff.mpr ⟨⋃ n, t n, hC.iUnion_mem t htC, by
    ext x
    simp [hts]⟩

-- Proof sketch: semiring axioms are stable under pullback by any map, in particular by the
-- subtype inclusion.
/-- Theorem 1.26 (5): Restricting a semiring of sets to a subset again yields a semiring of sets,
now on the subtype `A`. -/
theorem traceOn_isSetSemiring (A : Set Ω) (C : Set (Set Ω))
    (hC : MeasureTheory.IsSetSemiring C) :
    MeasureTheory.IsSetSemiring (traceOn C A) := sorry

-- Proof sketch: this is the negative existence statement from the textbook: there is some ambient
-- space, some nonempty subset, and some Dynkin system whose restriction is not again a Dynkin
-- system on the subset.
/-- Theorem 1.26 (6): In contrast, restriction of a Dynkin system need not be a Dynkin system on
the subset, in general. -/
theorem exists_nonempty_subset_with_non_dynkin_trace :
    ∃ Ω' : Type u, ∃ A : Set Ω', A.Nonempty ∧ ∃ d : MeasurableSpace.DynkinSystem Ω',
      ¬ ∃ dA : MeasurableSpace.DynkinSystem A, dA.Has = traceOn d.Has A := sorry
