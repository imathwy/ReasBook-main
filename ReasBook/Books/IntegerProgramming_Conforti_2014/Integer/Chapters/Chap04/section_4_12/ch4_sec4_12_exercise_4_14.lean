import Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_theorem_4_15

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so this file uses
-- direct local inspection of the Chapter 4 flow/cut API and Mathlib's finite-sum API.

noncomputable section

open scoped BigOperators

section Exercise_4_14

variable {V A : Type} [Fintype A]
variable (tail head : A → V)

/-- The bounded circulations of a finite digraph are the arc vectors whose incoming and outgoing
flow agree at every vertex and which lie between the lower and upper arc bounds coordinatewise. -/
def bounded_circulations (tail head : A → V) (ℓ u : A → ℝ) : Set (A → ℝ) :=
  {x | (∀ v : V, incoming_flow head x v = outgoing_flow tail x v) ∧ ℓ ≤ x ∧ x ≤ u}

private def lower_bound_imbalance (tail head : A → V) (ℓ : A → ℝ) (v : V) : ℝ :=
  incoming_flow head ℓ v - outgoing_flow tail ℓ v

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableEq A := Classical.decEq A

private abbrev endpoint_support (tail head : A → V) : Finset V :=
  circuit_vertices tail head Finset.univ

private abbrev SupportVertex (tail head : A → V) := {v : V // v ∈ endpoint_support tail head}

private lemma tail_mem_endpoint_support (tail head : A → V) (a : A) :
    tail a ∈ endpoint_support tail head := by
  classical
  change tail a ∈ circuit_vertices tail head Finset.univ
  rw [mem_circuit_vertices_iff]
  exact ⟨a, Finset.mem_univ a, Or.inl rfl⟩

private lemma head_mem_endpoint_support (tail head : A → V) (a : A) :
    head a ∈ endpoint_support tail head := by
  classical
  change head a ∈ circuit_vertices tail head Finset.univ
  rw [mem_circuit_vertices_iff]
  exact ⟨a, Finset.mem_univ a, Or.inr rfl⟩

private lemma incoming_cut_arcs_eq_filter (tail head : A → V) (X : Finset V) :
    δ⁻[tail, head] X = Finset.univ.filter fun a ↦ tail a ∉ X ∧ head a ∈ X := by
  ext a
  simp [incoming_cut_arcs]

private lemma outgoing_cut_arcs_eq_filter (tail head : A → V) (X : Finset V) :
    δ⁺[tail, head] X = Finset.univ.filter fun a ↦ tail a ∈ X ∧ head a ∉ X := by
  ext a
  simp [outgoing_cut_arcs]

/-- Summing the lower-bound imbalance over a cut side records the difference between the
lower-bound inflow across `δ⁻(X)` and the lower-bound outflow across `δ⁺(X)`. -/
private lemma sum_lower_bound_imbalance_eq_cut_difference
    (tail head : A → V) (ℓ : A → ℝ) (X : Finset V) :
    Finset.sum X (lower_bound_imbalance tail head ℓ) =
      Finset.sum (δ⁻[tail, head] X) ℓ - Finset.sum (δ⁺[tail, head] X) ℓ := by
  sorry

/-- Summing the vertex-balance equations over a cut side shows that the total flow entering the
side equals the total flow leaving it. -/
private lemma cut_balance_of_flow_balance
    (tail head : A → V) (x : A → ℝ)
    (hbalance : ∀ v : V, incoming_flow head x v = outgoing_flow tail x v)
    (X : Finset V) :
    Finset.sum (δ⁻[tail, head] X) x = Finset.sum (δ⁺[tail, head] X) x := by
  sorry

private def supported_cut_side (tail head : A → V) (X : Set V) : Finset V :=
  let _ : DecidablePred fun v : V ↦ v ∈ X := Classical.decPred _
  (endpoint_support tail head).filter fun v ↦ v ∈ X

private lemma incoming_cut_arcs_eq_supported_cut_side
    (tail head : A → V) (X : Set V) :
    δ⁻[tail, head] X = δ⁻[tail, head] (supported_cut_side tail head X : Set V) := by
  ext a
  simp [supported_cut_side, tail_mem_endpoint_support tail head a,
    head_mem_endpoint_support tail head a]

private lemma outgoing_cut_arcs_eq_supported_cut_side
    (tail head : A → V) (X : Set V) :
    δ⁺[tail, head] X = δ⁺[tail, head] (supported_cut_side tail head X : Set V) := by
  ext a
  simp [supported_cut_side, tail_mem_endpoint_support tail head a,
    head_mem_endpoint_support tail head a]

/-- A bounded circulation satisfies the cut inequality on every vertex subset. -/
lemma cut_condition_of_mem_bounded_circulations
    (tail head : A → V) (ℓ u x : A → ℝ)
    (hx : x ∈ bounded_circulations tail head ℓ u) (X : Set V) :
    Finset.sum (δ⁻[tail, head] X) ℓ ≤ Finset.sum (δ⁺[tail, head] X) u := by
  rcases hx with ⟨hbalance, hℓx, hxu⟩
  calc
    Finset.sum (δ⁻[tail, head] X) ℓ =
        Finset.sum (δ⁻[tail, head] (supported_cut_side tail head X : Set V)) ℓ := by
          rw [incoming_cut_arcs_eq_supported_cut_side tail head X]
    _ ≤ Finset.sum (δ⁻[tail, head] (supported_cut_side tail head X : Set V)) x := by
      exact Finset.sum_le_sum fun a ha ↦ hℓx a
    _ = Finset.sum (δ⁺[tail, head] (supported_cut_side tail head X : Set V)) x := by
      exact cut_balance_of_flow_balance tail head x hbalance (supported_cut_side tail head X)
    _ ≤ Finset.sum (δ⁺[tail, head] (supported_cut_side tail head X : Set V)) u := by
      exact Finset.sum_le_sum fun a ha ↦ hxu a
    _ = Finset.sum (δ⁺[tail, head] X) u := by
      rw [outgoing_cut_arcs_eq_supported_cut_side tail head X]

private inductive AuxiliaryVertex (V : Type)
  | source
  | sink
  | node (v : V)
deriving DecidableEq

private abbrev AuxiliaryArc (tail head : A → V) :=
  A ⊕ (SupportVertex tail head ⊕ SupportVertex tail head)

private def sourceArc {tail head : A → V} (v : SupportVertex tail head) : AuxiliaryArc tail head :=
  Sum.inr <| Sum.inl v

private def sinkArc {tail head : A → V} (v : SupportVertex tail head) : AuxiliaryArc tail head :=
  Sum.inr <| Sum.inr v

private def originalArc {tail head : A → V} (a : A) : AuxiliaryArc tail head :=
  Sum.inl a

private def auxiliaryTail (tail head : A → V) : AuxiliaryArc tail head → AuxiliaryVertex V
  | Sum.inl a => .node (tail a)
  | Sum.inr (Sum.inl _) => .source
  | Sum.inr (Sum.inr v) => .node v.1

private def auxiliaryHead (tail head : A → V) : AuxiliaryArc tail head → AuxiliaryVertex V
  | Sum.inl a => .node (head a)
  | Sum.inr (Sum.inl v) => .node v.1
  | Sum.inr (Sum.inr _) => .sink

private def source_capacity (tail head : A → V) (ℓ : A → ℝ) (v : SupportVertex tail head) : ℝ :=
  max (lower_bound_imbalance tail head ℓ v.1) 0

private def sink_capacity (tail head : A → V) (ℓ : A → ℝ) (v : SupportVertex tail head) : ℝ :=
  max (-lower_bound_imbalance tail head ℓ v.1) 0

private def auxiliaryCapacity (tail head : A → V) (ℓ u : A → ℝ) : AuxiliaryArc tail head → ℝ
  | Sum.inl a => u a - ℓ a
  | Sum.inr (Sum.inl v) => source_capacity tail head ℓ v
  | Sum.inr (Sum.inr v) => sink_capacity tail head ℓ v

private def total_source_capacity (tail head : A → V) (ℓ : A → ℝ) : ℝ :=
  Finset.sum (endpoint_support tail head).attach (source_capacity tail head ℓ)

private def total_sink_capacity (tail head : A → V) (ℓ : A → ℝ) : ℝ :=
  Finset.sum (endpoint_support tail head).attach (sink_capacity tail head ℓ)

private def full_source_side (tail head : A → V) : Set (AuxiliaryVertex V) :=
  {AuxiliaryVertex.source} ∪ Set.range fun v : SupportVertex tail head ↦ AuxiliaryVertex.node v.1

private def auxiliary_cut_vertices (tail head : A → V) (S : Set (AuxiliaryVertex V)) : Finset V :=
  let _ : DecidablePred fun v : V ↦ AuxiliaryVertex.node v ∈ S := Classical.decPred _
  (endpoint_support tail head).filter fun v ↦ AuxiliaryVertex.node v ∈ S

private def source_side_vertices
    (tail head : A → V) (S : Set (AuxiliaryVertex V)) : Finset (SupportVertex tail head) :=
  let _ : DecidablePred fun v : SupportVertex tail head ↦ AuxiliaryVertex.node v.1 ∉ S :=
    Classical.decPred _
  (endpoint_support tail head).attach.filter fun v ↦ AuxiliaryVertex.node v.1 ∉ S

private def sink_side_vertices
    (tail head : A → V) (S : Set (AuxiliaryVertex V)) : Finset (SupportVertex tail head) :=
  let _ : DecidablePred fun v : SupportVertex tail head ↦ AuxiliaryVertex.node v.1 ∈ S :=
    Classical.decPred _
  (endpoint_support tail head).attach.filter fun v ↦ AuxiliaryVertex.node v.1 ∈ S

private lemma incoming_cut_endpoint_support_eq_empty (tail head : A → V) :
    δ⁻[tail, head] (endpoint_support tail head) = ∅ := by
  ext a
  simp [tail_mem_endpoint_support tail head a]

private lemma outgoing_cut_endpoint_support_eq_empty (tail head : A → V) :
    δ⁺[tail, head] (endpoint_support tail head) = ∅ := by
  ext a
  simp [head_mem_endpoint_support tail head a]

private lemma source_capacity_sub_sink_capacity
    (tail head : A → V) (ℓ : A → ℝ) (v : SupportVertex tail head) :
    source_capacity tail head ℓ v - sink_capacity tail head ℓ v =
      lower_bound_imbalance tail head ℓ v.1 := by
  by_cases h : 0 ≤ lower_bound_imbalance tail head ℓ v.1
  · have hneg : -lower_bound_imbalance tail head ℓ v.1 ≤ 0 := by
      linarith
    simp [source_capacity, sink_capacity, h, hneg]
  · have hlt : lower_bound_imbalance tail head ℓ v.1 < 0 := lt_of_not_ge h
    have hle : lower_bound_imbalance tail head ℓ v.1 ≤ 0 := le_of_lt hlt
    have hpos : 0 ≤ -lower_bound_imbalance tail head ℓ v.1 := by
      linarith
    simp [source_capacity, sink_capacity, hle, hpos]

private lemma total_source_capacity_eq_total_sink_capacity
    (tail head : A → V) (ℓ : A → ℝ) :
    total_source_capacity tail head ℓ = total_sink_capacity tail head ℓ := by
  have hsum :
      Finset.sum (endpoint_support tail head).attach
          (fun v ↦ source_capacity tail head ℓ v - sink_capacity tail head ℓ v) = 0 := by
    calc
      Finset.sum (endpoint_support tail head).attach
          (fun v ↦ source_capacity tail head ℓ v - sink_capacity tail head ℓ v)
          = Finset.sum (endpoint_support tail head).attach
              (fun v ↦ lower_bound_imbalance tail head ℓ v.1) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa using source_capacity_sub_sink_capacity tail head ℓ v
      _ = Finset.sum (endpoint_support tail head) (lower_bound_imbalance tail head ℓ) := by
            rw [Finset.sum_attach]
      _ = Finset.sum (δ⁻[tail, head] (endpoint_support tail head)) ℓ -
            Finset.sum (δ⁺[tail, head] (endpoint_support tail head)) ℓ := by
            simpa using sum_lower_bound_imbalance_eq_cut_difference tail head ℓ
              (endpoint_support tail head)
      _ = 0 := by
            simp [incoming_cut_endpoint_support_eq_empty tail head,
              outgoing_cut_endpoint_support_eq_empty tail head]
  have hsub :
      total_source_capacity tail head ℓ - total_sink_capacity tail head ℓ = 0 := by
    simpa [total_source_capacity, total_sink_capacity, Finset.sum_sub_distrib] using hsum
  linarith

private lemma source_singleton_is_cut_side :
    IsSTCutSide (AuxiliaryVertex.source) (AuxiliaryVertex.sink)
      ({AuxiliaryVertex.source} : Set (AuxiliaryVertex V)) := by
  simp [IsSTCutSide]

private lemma full_source_side_is_cut_side (tail head : A → V) :
    IsSTCutSide (AuxiliaryVertex.source) (AuxiliaryVertex.sink) (full_source_side tail head) := by
  constructor
  · simp [full_source_side]
  · simp [full_source_side]

private lemma source_singleton_cut_capacity
    (tail head : A → V) (ℓ u : A → ℝ) :
    cut_capacity (auxiliaryTail tail head) (auxiliaryHead tail head)
        (auxiliaryCapacity tail head ℓ u) ({AuxiliaryVertex.source} : Set (AuxiliaryVertex V)) =
      total_source_capacity tail head ℓ := by
  simp [cut_capacity, outgoing_cut_arcs, Finset.sum_filter, Fintype.sum_sum_type,
    auxiliaryTail, auxiliaryHead, auxiliaryCapacity, total_source_capacity, source_capacity]

private lemma full_source_side_cut_capacity
    (tail head : A → V) (ℓ u : A → ℝ) :
    cut_capacity (auxiliaryTail tail head) (auxiliaryHead tail head)
        (auxiliaryCapacity tail head ℓ u) (full_source_side tail head) =
      total_sink_capacity tail head ℓ := by
  sorry

private lemma auxiliary_cut_capacity_eq
    (tail head : A → V) (ℓ u : A → ℝ) (S : Set (AuxiliaryVertex V))
    (hS : IsSTCutSide (AuxiliaryVertex.source) (AuxiliaryVertex.sink) S) :
    cut_capacity (auxiliaryTail tail head) (auxiliaryHead tail head)
        (auxiliaryCapacity tail head ℓ u) S =
      Finset.sum (δ⁺[tail, head] (auxiliary_cut_vertices tail head S)) (fun a ↦ u a - ℓ a) +
        Finset.sum (source_side_vertices tail head S) (source_capacity tail head ℓ) +
        Finset.sum (sink_side_vertices tail head S) (sink_capacity tail head ℓ) := by
  sorry

private lemma total_source_capacity_le_auxiliary_cut_capacity
    (tail head : A → V) (ℓ u : A → ℝ)
    (hcut :
      ∀ X : Set V, Finset.sum (δ⁻[tail, head] X) ℓ ≤ Finset.sum (δ⁺[tail, head] X) u)
    (S : Set (AuxiliaryVertex V))
    (hS : IsSTCutSide (AuxiliaryVertex.source) (AuxiliaryVertex.sink) S) :
    total_source_capacity tail head ℓ ≤
      cut_capacity (auxiliaryTail tail head) (auxiliaryHead tail head)
        (auxiliaryCapacity tail head ℓ u) S := by
  sorry

private lemma auxiliary_node_incoming_flow_eq
    (tail head : A → V) (f : AuxiliaryArc tail head → ℝ) (v : V)
    (hv : v ∈ endpoint_support tail head) :
    incoming_flow (auxiliaryHead tail head) f (AuxiliaryVertex.node v) =
      incoming_flow head (fun a ↦ f (originalArc a)) v + f (sourceArc ⟨v, hv⟩) := by
  sorry

private lemma auxiliary_node_outgoing_flow_eq
    (tail head : A → V) (f : AuxiliaryArc tail head → ℝ) (v : V)
    (hv : v ∈ endpoint_support tail head) :
    outgoing_flow (auxiliaryTail tail head) f (AuxiliaryVertex.node v) =
      outgoing_flow tail (fun a ↦ f (originalArc a)) v + f (sinkArc ⟨v, hv⟩) := by
  sorry

private lemma auxiliary_capacity_nonneg
    (tail head : A → V) (ℓ u : A → ℝ) (hℓu : ∀ a, ℓ a ≤ u a) :
    ∀ e : AuxiliaryArc tail head, 0 ≤ auxiliaryCapacity tail head ℓ u e
  | Sum.inl a => sub_nonneg.mpr (hℓu a)
  | Sum.inr (Sum.inl v) => by simp [auxiliaryCapacity, source_capacity]
  | Sum.inr (Sum.inr v) => by simp [auxiliaryCapacity, sink_capacity]

private lemma flow_balance_of_not_mem_endpoint_support
    (tail head : A → V) (x : A → ℝ) {v : V} (hv : v ∉ endpoint_support tail head) :
    incoming_flow head x v = outgoing_flow tail x v := by
  classical
  have hv' : v ∉ circuit_vertices tail head Finset.univ := by
    simpa [endpoint_support] using hv
  have htail : v ∉ Finset.univ.image tail := by
    intro hmem
    have hmem' : v ∈ circuit_vertices tail head Finset.univ := by
      rw [mem_circuit_vertices_iff]
      rcases Finset.mem_image.mp hmem with ⟨a, ha, htail⟩
      exact ⟨a, ha, Or.inl htail⟩
    exact hv' hmem'
  have hhead : v ∉ Finset.univ.image head := by
    intro hmem
    have hmem' : v ∈ circuit_vertices tail head Finset.univ := by
      rw [mem_circuit_vertices_iff]
      rcases Finset.mem_image.mp hmem with ⟨a, ha, hhead⟩
      exact ⟨a, ha, Or.inr hhead⟩
    exact hv' hmem'
  have hincoming : incoming_arcs head v = ∅ := by
    ext a
    have hne : head a ≠ v := by
      intro ha
      apply hhead
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩
    simp [incoming_arcs, hne]
  have houtgoing : outgoing_arcs tail v = ∅ := by
    ext a
    have hne : tail a ≠ v := by
      intro ha
      apply htail
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩
    simp [outgoing_arcs, hne]
  simp [incoming_flow_eq_sum_incoming_arcs, outgoing_flow_eq_sum_outgoing_arcs,
    hincoming, houtgoing]

/-- Exercise 4.14. For a finite digraph with arc lower bounds `ℓ` and upper bounds `u`, the set
of bounded circulations is nonempty if and only if every vertex subset `X` satisfies
`∑_{a ∈ δ⁻(X)} ℓ_a ≤ ∑_{a ∈ δ⁺(X)} u_a`. -/
theorem bounded_circulations_nonempty_iff_cut_condition
    (tail head : A → V) (ℓ u : A → ℝ) (hℓu : ∀ a, ℓ a ≤ u a) :
    Set.Nonempty (bounded_circulations tail head ℓ u) ↔
      ∀ X : Set V, Finset.sum (δ⁻[tail, head] X) ℓ ≤ Finset.sum (δ⁺[tail, head] X) u := by
  constructor
  · intro hx
    rcases hx with ⟨x, hx⟩
    exact cut_condition_of_mem_bounded_circulations tail head ℓ u x hx
  · intro hcut
    let tail' := auxiliaryTail tail head
    let head' := auxiliaryHead tail head
    let cap' := auxiliaryCapacity tail head ℓ u
    have hst : (AuxiliaryVertex.source : AuxiliaryVertex V) ≠ AuxiliaryVertex.sink := by
      simp
    obtain ⟨f, S, hmax, hmin, hvalue⟩ := max_flow_min_cut_theorem tail' head' cap'
      (AuxiliaryVertex.source : AuxiliaryVertex V) AuxiliaryVertex.sink hst
      (auxiliary_capacity_nonneg tail head ℓ u hℓu)
    have hmin_side :
        IsSTCutSide AuxiliaryVertex.source AuxiliaryVertex.sink S :=
      hmin.isSTCutSide
    have hcut_lower :
        total_source_capacity tail head ℓ ≤
          cut_capacity tail' head' cap' S := by
      simpa [tail', head', cap'] using
        total_source_capacity_le_auxiliary_cut_capacity tail head ℓ u hcut S hmin_side
    have hcut_upper :
        cut_capacity tail' head' cap' S ≤ total_source_capacity tail head ℓ := by
      calc
        cut_capacity tail' head' cap' S ≤
            cut_capacity tail' head' cap'
              ({AuxiliaryVertex.source} : Set (AuxiliaryVertex V)) := by
              exact hmin.le_cut_capacity _ source_singleton_is_cut_side
        _ = total_source_capacity tail head ℓ := by
              simpa [tail', head', cap'] using source_singleton_cut_capacity tail head ℓ u
    have hflow_value :
        st_flow_value tail' head' AuxiliaryVertex.source f = total_source_capacity tail head ℓ := by
      linarith [hcut_lower, hcut_upper, hvalue]
    have hfeas : IsFeasibleSTFlow tail' head' AuxiliaryVertex.source AuxiliaryVertex.sink cap' f :=
      hmax.isFeasibleSTFlow
    have hsource_eq :
        st_flow_value tail' head' AuxiliaryVertex.source f =
          cut_capacity tail' head' cap'
            ({AuxiliaryVertex.source} : Set (AuxiliaryVertex V)) := by
      rw [source_singleton_cut_capacity tail head ℓ u]
      exact hflow_value
    have hsource_sat :
        (∀ e ∈ δ⁺[tail', head'] ({AuxiliaryVertex.source} : Set (AuxiliaryVertex V)),
            f e = cap' e) ∧
          ∀ e ∈ δ⁻[tail', head'] ({AuxiliaryVertex.source} : Set (AuxiliaryVertex V)),
            f e = 0 := by
      exact
        (flow_value_eq_cut_capacity_iff tail' head' cap' f AuxiliaryVertex.source
          AuxiliaryVertex.sink ({AuxiliaryVertex.source} : Set (AuxiliaryVertex V))
          hfeas source_singleton_is_cut_side).1 hsource_eq
    have hfull_eq :
        st_flow_value tail' head' AuxiliaryVertex.source f =
          cut_capacity tail' head' cap' (full_source_side tail head) := by
      rw [full_source_side_cut_capacity tail head ℓ u]
      rw [hflow_value, total_source_capacity_eq_total_sink_capacity tail head ℓ]
    have hfull_sat :
        (∀ e ∈ δ⁺[tail', head'] (full_source_side tail head), f e = cap' e) ∧
          ∀ e ∈ δ⁻[tail', head'] (full_source_side tail head), f e = 0 := by
      exact
        (flow_value_eq_cut_capacity_iff tail' head' cap' f AuxiliaryVertex.source
          AuxiliaryVertex.sink (full_source_side tail head) hfeas
          (full_source_side_is_cut_side tail head)).1 hfull_eq
    let y : A → ℝ := fun a ↦ f (originalArc a)
    let x : A → ℝ := fun a ↦ ℓ a + y a
    refine ⟨x, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v
      by_cases hv : v ∈ endpoint_support tail head
      · let sv : SupportVertex tail head := ⟨v, hv⟩
        have hnode_balance :
            incoming_flow head' f (AuxiliaryVertex.node v) =
              outgoing_flow tail' f (AuxiliaryVertex.node v) := by
          exact hfeas.toIsSTFlow.conservation (AuxiliaryVertex.node v) (by simp) (by simp)
        have hsource_arc :
            f (sourceArc sv) = source_capacity tail head ℓ sv := by
          exact hsource_sat.1 (sourceArc sv) (by
            simp [sourceArc, tail', head', auxiliaryTail, auxiliaryHead])
        have hsink_arc :
            f (sinkArc sv) = sink_capacity tail head ℓ sv := by
          exact hfull_sat.1 (sinkArc sv) (by
            simp [sinkArc, tail', head', auxiliaryTail, auxiliaryHead, full_source_side])
        have hin :
            incoming_flow head' f (AuxiliaryVertex.node v) =
              incoming_flow head y v + f (sourceArc sv) := by
          simpa [y] using auxiliary_node_incoming_flow_eq tail head f v hv
        have hout :
            outgoing_flow tail' f (AuxiliaryVertex.node v) =
              outgoing_flow tail y v + f (sinkArc sv) := by
          simpa [y] using auxiliary_node_outgoing_flow_eq tail head f v hv
        have hy_balance :
            incoming_flow head y v + source_capacity tail head ℓ sv =
              outgoing_flow tail y v + sink_capacity tail head ℓ sv := by
          calc
            incoming_flow head y v + source_capacity tail head ℓ sv
                = incoming_flow head y v + f (sourceArc sv) := by rw [hsource_arc]
            _ = incoming_flow head' f (AuxiliaryVertex.node v) := hin.symm
            _ = outgoing_flow tail' f (AuxiliaryVertex.node v) := hnode_balance
            _ = outgoing_flow tail y v + f (sinkArc sv) := hout
            _ = outgoing_flow tail y v + sink_capacity tail head ℓ sv := by rw [hsink_arc]
        have hcap_diff :
            source_capacity tail head ℓ sv - sink_capacity tail head ℓ sv =
              incoming_flow head ℓ v - outgoing_flow tail ℓ v := by
          simpa [lower_bound_imbalance] using source_capacity_sub_sink_capacity tail head ℓ sv
        have hinx :
            incoming_flow head x v = incoming_flow head ℓ v + incoming_flow head y v := by
          simp [x, incoming_flow, Finset.sum_add_distrib]
        have houtx :
            outgoing_flow tail x v = outgoing_flow tail ℓ v + outgoing_flow tail y v := by
          simp [x, outgoing_flow, Finset.sum_add_distrib]
        linarith
      · exact flow_balance_of_not_mem_endpoint_support tail head x hv
    · intro a
      have hy_nonneg : 0 ≤ y a := hfeas.nonneg (originalArc a)
      linarith
    · intro a
      have hy_le : y a ≤ u a - ℓ a := hfeas.le_capacity (originalArc a)
      linarith

end Exercise_4_14
