import LinearRepresentations_Serre_1977.Chap04.Definition_4_23
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5

open MeasureTheory
open scoped ENNReal

noncomputable section

-- Semantic recall: `continuous_regularRepresentation_orbit` is the `L²(G)` continuity input, and
-- compactness supplies the finite subcover behind the measurable partition in the source proof.
-- Semantic search note: no closer mathlib theorem surfaced for this exact finite Borel partition
-- packaging, so the statement stays source-faithful over explicit `Fin n` data.

universe u

section

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

local notation "L²G" => (G →₂[(μG : Measure G)] ℂ)

/-- A finite Borel partition of `G` with sample points whose regular-representation orbit stays
within `ε` in `L²(G)` on each cell. -/
structure IsRegularRepresentationApproxPartition (h : L²G) (ε : ℝ) {n : ℕ}
    (y : Fin n → G) (E : Fin n → Set G) : Prop where
  measurableSet (i : Fin n) : MeasurableSet (E i)
  pairwiseDisjoint : Pairwise (fun i j ↦ Disjoint (E i) (E j))
  iUnion_eq_univ : (⋃ i, E i) = Set.univ
  norm_sub_lt (i : Fin n) {z : G} : z ∈ E i →
    ‖(regularRepresentation μG z h : L²G) - regularRepresentation μG (y i) h‖ < ε

/-- Helper for Lemma 4-49: compactness produces finitely many regular-representation orbit balls
that cover `G`. -/
lemma exists_finiteOrbitBallCover (h : L²G) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ y : Fin n → G,
      (Set.univ : Set G) ⊆ ⋃ i, {z : G |
        ‖(regularRepresentation μG z h : L²G) - regularRepresentation μG (y i) h‖ < ε} := by
  classical
  let orb : G → L²G := fun y ↦ regularRepresentation μG y h
  have horb : Continuous orb := by
    -- The orbit map is the continuous `G`-action on `L²(G)` evaluated at `h`.
    simpa [orb, regularRepresentation] using
      (continuous_id.smul continuous_const : Continuous fun y : G ↦ y • h)
  let U : G → Set G := fun z ↦ orb ⁻¹' Metric.ball (orb z) ε
  have hU_open : ∀ z, IsOpen (U z) := by
    -- Each cover set is the preimage of an open `L²`-ball under the orbit map.
    intro z
    simpa [U] using Metric.isOpen_ball.preimage horb
  have hU_mem : ∀ z, z ∈ U z := by
    -- Every point lies in its own `ε`-ball because `ε > 0`.
    intro z
    simpa [U, Metric.mem_ball, orb] using hε
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU_open fun z _ ↦
    Set.mem_iUnion.mpr ⟨z, hU_mem z⟩
  let e := t.equivFin
  refine ⟨t.card, fun i ↦ ((e.symm i : t) : G), ?_⟩
  intro z hz
  rcases Set.mem_iUnion₂.mp (ht hz) with ⟨w, hwt, hwz⟩
  -- Reindex the finite subcover once by `Fin t.card` and keep the orbit-ball description.
  refine Set.mem_iUnion.mpr ⟨e ⟨w, hwt⟩, ?_⟩
  simpa [U, orb, Metric.mem_ball, dist_eq_norm, e.apply_symm_apply]
    using hwz

/-
The partition helper is purely set-theoretic and measurable, so it does not need the ambient
topological compactness assumptions from the main theorem.
-/
omit [TopologicalSpace G] [BorelSpace G] [IsTopologicalGroup G] [CompactSpace G] in
/-- Helper for Lemma 4-49: a finite measurable cover can be disjointified without leaving the
original cover sets. -/
lemma exists_measurablePartition_subordinateToFiniteCover {n : ℕ} (U : Fin n → Set G)
    (hU_measurable : ∀ i, MeasurableSet (U i))
    (hcover : (Set.univ : Set G) ⊆ ⋃ i, U i) :
    ∃ E : Fin n → Set G,
      (∀ i, MeasurableSet (E i)) ∧
      Pairwise (fun i j ↦ Disjoint (E i) (E j)) ∧
      (⋃ i, E i) = Set.univ ∧
      ∀ i, E i ⊆ U i := by
  classical
  cases n with
  | zero =>
      exfalso
      have hone : (1 : G) ∈ (Set.univ : Set G) := by simp
      have : (1 : G) ∈ ⋃ i : Fin 0, U i := hcover hone
      simp at this
  | succ n =>
      let E : Fin (n + 1) → Set G := disjointed U
      have hE_measurable : ∀ i, MeasurableSet (E i) := by
        -- Write the disjointified cell as an intersection with finitely many complements.
        intro i
        rw [show E i = U i ∩ ⋂ j < i, (U j)ᶜ by simpa [E] using disjointed_eq_inter_compl U i]
        exact (hU_measurable i).inter <|
          MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦ (hU_measurable j).compl
      have hE_pairwise : Pairwise (fun i j ↦ Disjoint (E i) (E j)) := by
        -- The disjointified cells are pairwise disjoint by construction.
        intro i j hij
        simpa [E] using disjoint_disjointed U hij
      have hU_eq_univ : (⋃ i, U i) = (Set.univ : Set G) :=
        Set.Subset.antisymm (by simp) hcover
      have hE_eq_univ : (⋃ i, E i) = (Set.univ : Set G) := by
        -- Disjointification preserves the total union of a finite family.
        rw [show (⋃ i, E i) = ⋃ i, U i by simpa [E] using (iUnion_disjointed (f := U))]
        exact hU_eq_univ
      refine ⟨E, hE_measurable, hE_pairwise, hE_eq_univ, ?_⟩
      -- Each disjointified cell stays inside the original cover set it came from.
      intro i
      simpa [E] using disjointed_subset U i

/-- Helper for Lemma 4-49: a measurable partition subordinate to the orbit-ball cover gives the
target approximation structure. -/
lemma isRegularRepresentationApproxPartition_of_subordinateCover
    (h : L²G) {ε : ℝ} {n : ℕ} {y : Fin n → G} {E : Fin n → Set G}
    (hE_measurable : ∀ i, MeasurableSet (E i))
    (hE_pairwise : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hE_eq_univ : (⋃ i, E i) = Set.univ)
    (hE_sub : ∀ i, E i ⊆ {z : G |
      ‖(regularRepresentation μG z h : L²G) - regularRepresentation μG (y i) h‖ < ε}) :
    IsRegularRepresentationApproxPartition h ε y E := by
  refine
    { measurableSet := hE_measurable
      pairwiseDisjoint := hE_pairwise
      iUnion_eq_univ := hE_eq_univ
      norm_sub_lt := ?_ }
  -- Membership in a subordinate cell immediately gives the required orbit-ball bound.
  intro i z hz
  exact hE_sub i hz

/-- Lemma 4-49: for a compact group `G` and `h : L²(G)`, every `ε > 0` admits a finite family of
points `y i : G` and Borel sets `E i ⊆ G` that disjointly cover `G`, such that every `y ∈ E i`
satisfies `‖regularRepresentation μG y h - regularRepresentation μG (y i) h‖ < ε`. -/
theorem exists_finite_borel_partition_regularRepresentation_norm_sub_lt
    (h : L²G) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ y : Fin n → G, ∃ E : Fin n → Set G,
      IsRegularRepresentationApproxPartition h ε y E := by
  obtain ⟨n, y, hy_cover⟩ := exists_finiteOrbitBallCover h hε
  let U : Fin n → Set G := fun i ↦ {z : G |
    ‖(regularRepresentation μG z h : L²G) - regularRepresentation μG (y i) h‖ < ε}
  have horb : Continuous (fun z : G ↦ regularRepresentation μG z h) := by
    -- The same continuity input makes each orbit ball Borel measurable.
    simpa [regularRepresentation] using
      (continuous_id.smul continuous_const : Continuous fun z : G ↦ z • h)
  have hU_open : ∀ i, IsOpen (U i) := by
    -- Each orbit ball is open in `L²(G)`, so its preimage along the orbit map is open in `G`.
    intro i
    simpa [U, Set.preimage, Metric.mem_ball, dist_eq_norm] using
      (Metric.isOpen_ball.preimage horb :
        IsOpen ((fun z : G ↦ regularRepresentation μG z h) ⁻¹'
          Metric.ball (regularRepresentation μG (y i) h) ε))
  have hU_measurable : ∀ i, MeasurableSet (U i) := by
    -- Open orbit balls are Borel measurable.
    intro i
    exact (hU_open i).measurableSet
  have hU_cover : (Set.univ : Set G) ⊆ ⋃ i, U i := by
    simpa [U] using hy_cover
  obtain ⟨E, hE_measurable, hE_pairwise, hE_eq_univ, hE_sub⟩ :=
    exists_measurablePartition_subordinateToFiniteCover U hU_measurable hU_cover
  -- Assemble the disjoint measurable partition together with the orbit-ball control.
  exact ⟨n, y, E,
    isRegularRepresentationApproxPartition_of_subordinateCover
      h hE_measurable hE_pairwise hE_eq_univ hE_sub⟩

end
