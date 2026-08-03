module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Bases

universe u v

public section

namespace Pi

open Filter Topology

/-- Helper for Exercise 29.2: evaluation from a nonempty product is an open quotient map. -/
lemma isOpenQuotientMap_eval {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → Nonempty (X i)] (i : ι) :
    IsOpenQuotientMap (Function.eval i : ((j : ι) → X j) → X i) := by
  -- Combine the standard continuity, openness, and surjectivity of evaluation.
  exact ⟨Function.surjective_eval i, continuous_apply i, isOpenMap_eval i⟩

/-- Helper for Exercise 29.2: a compact product neighborhood forces all coordinates
outside a finite set to be compact. -/
lemma compactSpaceOutsideFinite_of_compact_mem_nhds {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → Nonempty (X i)]
    (x : (i : ι) → X i) (K : Set ((i : ι) → X i)) (hK : IsCompact K)
    (hKx : K ∈ 𝓝 x) :
    ∃ s : Set ι, s.Finite ∧ ∀ i ∉ s, CompactSpace (X i) := by
  classical
  -- Refine the product neighborhood to a cylinder with finite support.
  rw [nhds_pi, Filter.mem_pi] at hKx
  obtain ⟨s, hs, U, hU, hUK⟩ := hKx
  refine ⟨s, hs, fun i hi ↦ ?_⟩
  have hxU : x ∈ s.pi U := fun j _ ↦ mem_of_mem_nhds (hU j)
  have hU_nonempty : (s.pi U).Nonempty := ⟨x, hxU⟩
  have hevalU : Function.eval i '' s.pi U = Set.univ := by
    rw [Set.eval_image_pi_of_notMem hi, if_pos hU_nonempty]
  have hevalK : Function.eval i '' K = Set.univ := by
    apply Set.Subset.antisymm
    · intro y _
      exact Set.mem_univ y
    · rw [← hevalU]
      exact Set.image_mono hUK
  -- The whole factor is the continuous image of the compact neighborhood.
  rw [← isCompact_univ_iff, ← hevalK]
  exact hK.image (continuous_apply i)

/-- Helper for Exercise 29.2: finitely many noncompact weakly locally compact factors
still have a weakly locally compact product. -/
lemma weaklyLocallyCompactSpace_of_finite_noncompact {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] (s : Set ι) (hs : s.Finite)
    (hlocal : ∀ i, WeaklyLocallyCompactSpace (X i))
    (hcompact : ∀ i ∉ s, CompactSpace (X i)) :
    WeaklyLocallyCompactSpace ((i : ι) → X i) := by
  -- Choose compact coordinate neighborhoods and restrict only the exceptional coordinates.
  refine ⟨fun x ↦ ?_⟩
  choose K hK hKx using fun i ↦
    @exists_compact_mem_nhds (X i) _ (hlocal i) (x i)
  refine ⟨s.pi K, ?_, ?_⟩
  · classical
    rw [← Set.univ_pi_ite]
    refine isCompact_univ_pi fun i ↦ ?_
    by_cases hi : i ∈ s
    · rw [if_pos hi]
      exact hK i
    · rw [if_neg hi]
      exact isCompact_univ_iff.mpr (hcompact i hi)
  · exact (set_pi_mem_nhds_iff hs x).mpr fun i _ ↦ hKx i

/-- Exercise 29.2: a nonempty product is weakly locally compact exactly when every
factor is weakly locally compact and all but finitely many factors are compact. -/
theorem weaklyLocallyCompactSpace_iff {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → Nonempty (X i)] :
    WeaklyLocallyCompactSpace ((i : ι) → X i) ↔
      (∀ i, WeaklyLocallyCompactSpace (X i)) ∧
        ∀ᶠ i in Filter.cofinite, CompactSpace (X i) := by
  constructor
  · intro hproduct
    constructor
    · intro i
      -- Transfer weak local compactness through the open quotient evaluation map.
      exact @IsOpenQuotientMap.weaklyLocallyCompactSpace _ _ _ _ hproduct _
        (isOpenQuotientMap_eval i)
    · -- One compact product neighborhood supplies the finite exceptional set.
      let x : (i : ι) → X i := fun i ↦ Classical.choice (inferInstance : Nonempty (X i))
      obtain ⟨K, hK, hKx⟩ := @exists_compact_mem_nhds _ _ hproduct x
      obtain ⟨s, hs, hcompact⟩ :=
        compactSpaceOutsideFinite_of_compact_mem_nhds x K hK hKx
      filter_upwards [hs.eventually_cofinite_notMem] with i hi
      exact hcompact i hi
  · rintro ⟨hlocal, hcompact⟩
    classical
    -- Use the cofinite hypothesis as the finite exceptional set for the cylinder construction.
    rw [Filter.eventually_cofinite] at hcompact
    refine weaklyLocallyCompactSpace_of_finite_noncompact
      {i | ¬ CompactSpace (X i)} hcompact hlocal ?_
    intro i hi
    simpa only [Set.mem_setOf_eq, not_not] using hi

/-- Exercise 29.2 (1): if a nonempty product is weakly locally compact, then each
factor is weakly locally compact. -/
theorem factorWeaklyLocallyCompactSpace {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → Nonempty (X i)]
    [WeaklyLocallyCompactSpace ((i : ι) → X i)] :
    ∀ i, WeaklyLocallyCompactSpace (X i) :=
  (weaklyLocallyCompactSpace_iff.mp inferInstance).1

/-- Exercise 29.2 (2): if a nonempty product is weakly locally compact, then all
but finitely many factors are compact. -/
theorem eventuallyCompactSpace {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → Nonempty (X i)]
    [WeaklyLocallyCompactSpace ((i : ι) → X i)] :
    ∀ᶠ i in Filter.cofinite, CompactSpace (X i) :=
  (weaklyLocallyCompactSpace_iff.mp inferInstance).2

/-- Exercise 29.2 (3): a nonempty product of weakly locally compact spaces is
weakly locally compact when all but finitely many factors are compact. -/
theorem weaklyLocallyCompactSpaceOfEventuallyCompact {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → Nonempty (X i)]
    [(i : ι) → WeaklyLocallyCompactSpace (X i)]
    (hcompact : ∀ᶠ i in Filter.cofinite, CompactSpace (X i)) :
    WeaklyLocallyCompactSpace ((i : ι) → X i) :=
  weaklyLocallyCompactSpace_iff.mpr ⟨inferInstance, hcompact⟩

end Pi
