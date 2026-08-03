module

public import Topology_Munkres_2000.Book.Exercise_45_7.ClosedBoundedSets
public import Mathlib.Topology.MetricSpace.Thickening

public section

noncomputable section

open Set

universe u

namespace TopologicalSpace.NonemptyClosedBounded

variable {X : Type u} [MetricSpace X]

/-- The Hausdorff metric on nonempty closed bounded subsets. -/
instance instMetricSpace : MetricSpace (NonemptyClosedBounded X) :=
  EMetricSpace.toMetricSpace fun A B ↦
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded A.nonempty B.nonempty A.isBounded
      B.isBounded

/-- Helper for Exercise 45.7: finite Hausdorff edistance from a nonempty bounded set
preserves boundedness. -/
theorem _root_.Metric.isBounded_of_hausdorffEDist_ne_top {s t : Set X}
    (_hs : s.Nonempty) (hbs : Bornology.IsBounded s)
    (hfin : Metric.hausdorffEDist s t ≠ ⊤) : Bornology.IsBounded t := by
  -- Choose a finite integral radius strictly larger than the Hausdorff edistance.
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin
  -- Place the target inside that bounded thickening of the source.
  apply (hbs.thickening (δ := (n : ℝ))).subset
  intro x hx
  rw [Metric.mem_thickening_iff_exists_edist_lt]
  rw [Metric.hausdorffEDist_comm] at hn
  obtain ⟨y, hy, hxy⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt hx hn
  refine ⟨y, hy, ?_⟩
  simpa only [edist_dist, ENNReal.ofReal_natCast] using hxy

/-- Helper for Exercise 45.7: the nonempty bounded closed sets form a clopen part of
`TopologicalSpace.Closeds X`. -/
theorem isClopen_nonempty_isBounded :
    IsClopen {A : TopologicalSpace.Closeds X |
      (A : Set X).Nonempty ∧ Bornology.IsBounded (A : Set X)} := by
  -- An empty ambient space has no nonempty closed subsets.
  cases isEmpty_or_nonempty X with
  | inl hX =>
      have hset : {A : TopologicalSpace.Closeds X |
          (A : Set X).Nonempty ∧ Bornology.IsBounded (A : Set X)} = ∅ := by
        ext A
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hA
        obtain ⟨x, _⟩ := hA.1
        exact isEmptyElim x
      rw [hset]
      exact isClopen_empty
  | inr hX =>
      let C : NonemptyClosedBounded X := singleton (Classical.choice hX)
      have hset : {A : TopologicalSpace.Closeds X |
          (A : Set X).Nonempty ∧ Bornology.IsBounded (A : Set X)} = Metric.eball C.val ⊤ := by
        ext A
        rw [Metric.mem_eball, TopologicalSpace.Closeds.edist_eq]
        constructor
        · intro hA
          exact lt_top_iff_ne_top.mpr <|
            Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hA.1 C.nonempty hA.2
              C.isBounded
        · intro hA
          have hfin : Metric.hausdorffEDist (A : Set X) (C : Set X) ≠ ⊤ :=
            lt_top_iff_ne_top.mp hA
          rw [Metric.hausdorffEDist_comm] at hfin
          exact ⟨Metric.nonempty_of_hausdorffEDist_ne_top C.nonempty hfin,
            Metric.isBounded_of_hausdorffEDist_ne_top C.nonempty C.isBounded hfin⟩
      rw [hset]
      exact ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩

/-- A complete metric space has a complete Hausdorff hyperspace of nonempty closed bounded sets. -/
instance instCompleteSpace [CompleteSpace X] :
    CompleteSpace (NonemptyClosedBounded X) := by
  -- The clopen component is closed in the complete Hausdorff hyperspace.
  letI : CompleteSpace (TopologicalSpace.Closeds X) := inferInstance
  exact isClopen_nonempty_isBounded.isClosed.completeSpace_coe

/-- Total boundedness of the ambient metric space passes to its Hausdorff hyperspace. -/
theorem totallyBounded_univ
    (hX : TotallyBounded (Set.univ : Set X)) :
    TotallyBounded (Set.univ : Set (NonemptyClosedBounded X)) := by
  -- The whole closed-set hyperspace is totally bounded when the ambient space is.
  have hCloseds : TotallyBounded (Set.univ : Set (TopologicalSpace.Closeds X)) := by
    simpa using TopologicalSpace.Closeds.totallyBounded_subsets_of_totallyBounded hX
  -- Pull total boundedness back along the subtype inclusion.
  simpa using totallyBounded_preimage isUniformEmbedding_subtype_val.isUniformInducing hCloseds

/-- A compact metric space has a compact Hausdorff hyperspace of nonempty closed bounded sets. -/
instance instCompactSpace [CompactSpace X] :
    CompactSpace (NonemptyClosedBounded X) := by
  -- Combine completeness with total boundedness of the whole hyperspace.
  refine isCompact_univ_iff.mp ?_
  apply isCompact_iff_totallyBounded_isComplete.mpr
  exact ⟨totallyBounded_univ isCompact_univ.totallyBounded, complete_univ⟩


end TopologicalSpace.NonemptyClosedBounded

namespace Metric.NonemptyClosedBounded

variable {X : Type u} [MetricSpace X]

/-- Helper for Exercise 45.7: mutual containment in open thickenings bounds the
Hausdorff distance by the thickening radius. -/
theorem hausdorffDist_le_of_mutual_subset_thickening {s t : Set X} {ε : ℝ}
    (ht : t.Nonempty) (hs : s.Nonempty) (hst : s ⊆ Metric.thickening ε t)
    (hts : t ⊆ Metric.thickening ε s) : Metric.hausdorffDist s t ≤ ε := by
  -- A nonempty source point shows that an admissible radius is positive.
  have hε : 0 ≤ ε := by
    have hxε : Metric.infDist hs.some t < ε :=
      (Metric.mem_thickening_iff_infDist_lt ht).mp (hst hs.some_mem)
    exact (Metric.infDist_nonneg.trans_lt hxε).le
  -- Convert the two containment hypotheses into pointwise infimum bounds.
  apply Metric.hausdorffDist_le_of_infDist hε
  · intro y hy
    exact ((Metric.mem_thickening_iff_infDist_lt ht).mp (hst hy)).le
  · intro y hy
    exact ((Metric.mem_thickening_iff_infDist_lt hs).mp (hts hy)).le

/-- Helper for Exercise 45.7: every radius strictly larger than a finite Hausdorff
distance gives mutual containment in the corresponding thickenings. -/
theorem mutual_subset_thickening_of_hausdorffDist_lt {s t : Set X} {ε : ℝ}
    (hfin : Metric.hausdorffEDist s t ≠ ⊤) (hε : Metric.hausdorffDist s t < ε) :
    s ⊆ Metric.thickening ε t ∧ t ⊆ Metric.thickening ε s := by
  -- Choose the nearby point supplied by the Hausdorff-distance bound on each side.
  constructor
  · intro x hx
    rw [Metric.mem_thickening_iff]
    exact Metric.exists_dist_lt_of_hausdorffDist_lt hx hε hfin
  · intro y hy
    rw [Metric.mem_thickening_iff]
    obtain ⟨x, hx, hxy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hy hε hfin
    exact ⟨x, hx, by simpa only [dist_comm] using hxy⟩

/-- The hyperspace distance is the Hausdorff distance of the underlying sets. -/
theorem dist_eq (A B : TopologicalSpace.NonemptyClosedBounded X) :
    dist A B = Metric.hausdorffDist (A : Set X) (B : Set X) := by
  -- Normalize the induced metric through the inherited Hausdorff edistance.
  rw [dist_edist, Metric.hausdorffDist, Subtype.edist_eq,
    TopologicalSpace.Closeds.edist_eq]

/-- The Hausdorff distance is the infimum of radii of mutual metric thickenings. -/
theorem dist_eq_sInf (A B : TopologicalSpace.NonemptyClosedBounded X) :
    dist A B =
      sInf {ε : ℝ |
        (A : Set X) ⊆ Metric.thickening ε (B : Set X) ∧
          (B : Set X) ⊆ Metric.thickening ε (A : Set X)} := by
  -- Work with the underlying set Hausdorff distance.
  rw [dist_eq]
  let radii : Set ℝ := {ε : ℝ |
    (A : Set X) ⊆ Metric.thickening ε (B : Set X) ∧
      (B : Set X) ⊆ Metric.thickening ε (A : Set X)}
  have hfin : Metric.hausdorffEDist (A : Set X) (B : Set X) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded A.nonempty B.nonempty A.isBounded
      B.isBounded
  have hlower : ∀ ε ∈ radii, Metric.hausdorffDist (A : Set X) (B : Set X) ≤ ε := by
    intro ε hε
    exact hausdorffDist_le_of_mutual_subset_thickening B.nonempty A.nonempty hε.1 hε.2
  have hbdd : BddBelow radii := by
    rw [bddBelow_def]
    exact ⟨Metric.hausdorffDist (A : Set X) (B : Set X), hlower⟩
  have hnear : ∀ ε, Metric.hausdorffDist (A : Set X) (B : Set X) < ε → ε ∈ radii := by
    intro ε hε
    exact mutual_subset_thickening_of_hausdorffDist_lt hfin hε
  have hnonempty : radii.Nonempty := by
    refine ⟨Metric.hausdorffDist (A : Set X) (B : Set X) + 1, ?_⟩
    exact hnear _ (lt_add_one _)
  apply le_antisymm
  · exact le_csInf hnonempty hlower
  · apply le_of_forall_gt_imp_ge_of_dense
    intro ε hε
    exact csInf_le hbdd (hnear ε hε)

end Metric.NonemptyClosedBounded
