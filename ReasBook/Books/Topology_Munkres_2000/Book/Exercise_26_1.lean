module

public import Mathlib.Order.Comparable
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.WithTopology

public section

/-- Part (a) of Exercise 26.1: If `t'` is finer than `t`, then compactness for `t'`
implies compactness for the coarser topology `t`. -/
theorem compactSpace_of_finer {X : Type u} (t t' : TopologicalSpace X) (h : t' ≤ t)
    (hc : CompactSpace (WithTopology X t')) : CompactSpace (WithTopology X t) := by
  -- Unwrap to `X`, use the continuous identity, and rewrap with the coarser topology.
  letI := hc
  have hunwrap : @Continuous (WithTopology X t') X
      (WithTopology.instTopologicalSpace X t') t'
      (WithTopology.ofTopology : WithTopology X t' → X) :=
    WithTopology.continuous_ofTopology t'
  have hraw : @Continuous X X t' t (id : X → X) := continuous_id_of_le h
  have hthrough : @Continuous (WithTopology X t') X
      (WithTopology.instTopologicalSpace X t') t
      ((id : X → X) ∘ (WithTopology.ofTopology : WithTopology X t' → X)) :=
    @Continuous.comp (WithTopology X t') X X
      (WithTopology.instTopologicalSpace X t') t' t
      (WithTopology.ofTopology : WithTopology X t' → X) (id : X → X) hraw hunwrap
  have hcont : Continuous (WithTopology.toTopology t ∘
      (WithTopology.ofTopology : WithTopology X t' → X)) := by
    simpa only [Function.id_comp] using
      (@Continuous.comp (WithTopology X t') X (WithTopology X t)
        (WithTopology.instTopologicalSpace X t') t (WithTopology.instTopologicalSpace X t)
        ((id : X → X) ∘ (WithTopology.ofTopology : WithTopology X t' → X))
        (WithTopology.toTopology t) (WithTopology.continuous_toTopology t) hthrough)
  have hsurj : Function.Surjective (WithTopology.toTopology t ∘
      (WithTopology.ofTopology : WithTopology X t' → X)) :=
    (WithTopology.toTopology_surjective t).comp (WithTopology.ofTopology_surjective t')
  exact hsurj.compactSpace hcont

/-- Converse for part (a) of Exercise 26.1: Compactness for a coarser topology need not imply
compactness for a finer topology. -/
theorem exists_compactSpace_not_compactSpace_of_finer :
    ∃ (X : Type) (t t' : TopologicalSpace X),
      t' ≤ t ∧ CompactSpace (WithTopology X t) ∧ ¬ CompactSpace (WithTopology X t') := by
  -- The indiscrete topology on `ℕ` is compact, while the discrete topology is not.
  refine ⟨ℕ, ⊤, ⊥, bot_le, inferInstance, ?_⟩
  intro hc
  letI := hc
  have hfinite : Finite (WithTopology ℕ (⊥ : TopologicalSpace ℕ)) :=
    finite_of_compact_of_discrete
  exact Infinite.not_finite hfinite

/-- Exercise 26.1 (b): Two compact Hausdorff topologies on the same type are
either equal or incomparable. -/
theorem eq_or_incomparable_of_compactSpace_t2Space {X : Type u}
    (t t' : TopologicalSpace X) (hc : CompactSpace (WithTopology X t))
    (hc' : CompactSpace (WithTopology X t')) (h2 : T2Space (WithTopology X t))
    (h2' : T2Space (WithTopology X t')) :
    t = t' ∨ IncompRel (· ≤ ·) t t' := by
  -- If the topologies differ, either comparison would make the identity a quotient map.
  by_cases heq : t = t'
  · exact Or.inl heq
  · right
    constructor
    · intro hle
      letI := hc
      letI := h2'
      -- The comparison gives a continuous bijection from compact `t` to Hausdorff `t'`.
      have hunwrap : @Continuous (WithTopology X t) X
          (WithTopology.instTopologicalSpace X t) t
          (WithTopology.ofTopology : WithTopology X t → X) :=
        WithTopology.continuous_ofTopology t
      have hraw : @Continuous X X t t' (id : X → X) := continuous_id_of_le hle
      have hthrough : @Continuous (WithTopology X t) X
          (WithTopology.instTopologicalSpace X t) t'
          ((id : X → X) ∘ (WithTopology.ofTopology : WithTopology X t → X)) :=
        @Continuous.comp (WithTopology X t) X X
          (WithTopology.instTopologicalSpace X t) t t'
          (WithTopology.ofTopology : WithTopology X t → X) (id : X → X) hraw hunwrap
      have hcont : Continuous (WithTopology.toTopology t' ∘
          (WithTopology.ofTopology : WithTopology X t → X)) := by
        simpa only [Function.id_comp] using
          (@Continuous.comp (WithTopology X t) X (WithTopology X t')
            (WithTopology.instTopologicalSpace X t) t'
            (WithTopology.instTopologicalSpace X t')
            ((id : X → X) ∘ (WithTopology.ofTopology : WithTopology X t → X))
            (WithTopology.toTopology t') (WithTopology.continuous_toTopology t') hthrough)
      have hsurj : Function.Surjective
          (WithTopology.toTopology t' ∘
            (WithTopology.ofTopology : WithTopology X t → X)) :=
        (WithTopology.toTopology_surjective t').comp (WithTopology.ofTopology_surjective t)
      have hquot : Topology.IsQuotientMap
          (WithTopology.toTopology t' ∘
            (WithTopology.ofTopology : WithTopology X t → X)) :=
        Topology.IsQuotientMap.of_surjective_continuous hsurj hcont
      -- Quotientness makes the inverse unwrap/rewrap map continuous as well.
      have hinv : Continuous (WithTopology.toTopology t ∘
          (WithTopology.ofTopology : WithTopology X t' → X)) := by
        rw [hquot.continuous_iff]
        simpa only [Function.comp_def, WithTopology.ofTopology_toTopology,
          WithTopology.toTopology_ofTopology] using
            (continuous_id' : Continuous (fun x : WithTopology X t ↦ x))
      have hreverse : t' ≤ t := by
        rw [← continuous_id_iff_le]
        rw [Function.id_def]
        have hto : @Continuous X (WithTopology X t') t'
            (WithTopology.instTopologicalSpace X t') (WithTopology.toTopology t') :=
          WithTopology.continuous_toTopology t'
        have hmiddle : @Continuous X (WithTopology X t) t'
            (WithTopology.instTopologicalSpace X t)
            ((WithTopology.toTopology t ∘
              (WithTopology.ofTopology : WithTopology X t' → X)) ∘
                WithTopology.toTopology t') :=
          @Continuous.comp X (WithTopology X t') (WithTopology X t) t'
            (WithTopology.instTopologicalSpace X t') (WithTopology.instTopologicalSpace X t)
            (WithTopology.toTopology t')
            (WithTopology.toTopology t ∘
              (WithTopology.ofTopology : WithTopology X t' → X)) hinv hto
        have hout : @Continuous (WithTopology X t) X
            (WithTopology.instTopologicalSpace X t) t
            (WithTopology.ofTopology : WithTopology X t → X) :=
          WithTopology.continuous_ofTopology t
        simpa only [Function.comp_def, WithTopology.ofTopology_toTopology] using
          (@Continuous.comp X (WithTopology X t) X t'
            (WithTopology.instTopologicalSpace X t) t
            ((WithTopology.toTopology t ∘
              (WithTopology.ofTopology : WithTopology X t' → X)) ∘
                WithTopology.toTopology t')
            (WithTopology.ofTopology : WithTopology X t → X) hout hmiddle)
      exact heq (le_antisymm hle hreverse)
    · intro hle
      letI := hc'
      letI := h2
      -- Repeat the compact-to-Hausdorff argument with the topologies exchanged.
      have hunwrap : @Continuous (WithTopology X t') X
          (WithTopology.instTopologicalSpace X t') t'
          (WithTopology.ofTopology : WithTopology X t' → X) :=
        WithTopology.continuous_ofTopology t'
      have hraw : @Continuous X X t' t (id : X → X) := continuous_id_of_le hle
      have hthrough : @Continuous (WithTopology X t') X
          (WithTopology.instTopologicalSpace X t') t
          ((id : X → X) ∘ (WithTopology.ofTopology : WithTopology X t' → X)) :=
        @Continuous.comp (WithTopology X t') X X
          (WithTopology.instTopologicalSpace X t') t' t
          (WithTopology.ofTopology : WithTopology X t' → X) (id : X → X) hraw hunwrap
      have hcont : Continuous (WithTopology.toTopology t ∘
          (WithTopology.ofTopology : WithTopology X t' → X)) := by
        simpa only [Function.id_comp] using
          (@Continuous.comp (WithTopology X t') X (WithTopology X t)
            (WithTopology.instTopologicalSpace X t') t
            (WithTopology.instTopologicalSpace X t)
            ((id : X → X) ∘ (WithTopology.ofTopology : WithTopology X t' → X))
            (WithTopology.toTopology t) (WithTopology.continuous_toTopology t) hthrough)
      have hsurj : Function.Surjective
          (WithTopology.toTopology t ∘
            (WithTopology.ofTopology : WithTopology X t' → X)) :=
        (WithTopology.toTopology_surjective t).comp (WithTopology.ofTopology_surjective t')
      have hquot : Topology.IsQuotientMap
          (WithTopology.toTopology t ∘
            (WithTopology.ofTopology : WithTopology X t' → X)) :=
        Topology.IsQuotientMap.of_surjective_continuous hsurj hcont
      have hinv : Continuous (WithTopology.toTopology t' ∘
          (WithTopology.ofTopology : WithTopology X t → X)) := by
        rw [hquot.continuous_iff]
        simpa only [Function.comp_def, WithTopology.ofTopology_toTopology,
          WithTopology.toTopology_ofTopology] using
            (continuous_id' : Continuous (fun x : WithTopology X t' ↦ x))
      have hreverse : t ≤ t' := by
        rw [← continuous_id_iff_le]
        rw [Function.id_def]
        have hto : @Continuous X (WithTopology X t) t
            (WithTopology.instTopologicalSpace X t) (WithTopology.toTopology t) :=
          WithTopology.continuous_toTopology t
        have hmiddle : @Continuous X (WithTopology X t') t
            (WithTopology.instTopologicalSpace X t')
            ((WithTopology.toTopology t' ∘
              (WithTopology.ofTopology : WithTopology X t → X)) ∘
                WithTopology.toTopology t) :=
          @Continuous.comp X (WithTopology X t) (WithTopology X t') t
            (WithTopology.instTopologicalSpace X t) (WithTopology.instTopologicalSpace X t')
            (WithTopology.toTopology t)
            (WithTopology.toTopology t' ∘
              (WithTopology.ofTopology : WithTopology X t → X)) hinv hto
        have hout : @Continuous (WithTopology X t') X
            (WithTopology.instTopologicalSpace X t') t'
            (WithTopology.ofTopology : WithTopology X t' → X) :=
          WithTopology.continuous_ofTopology t'
        simpa only [Function.comp_def, WithTopology.ofTopology_toTopology] using
          (@Continuous.comp X (WithTopology X t') X t
            (WithTopology.instTopologicalSpace X t') t'
            ((WithTopology.toTopology t' ∘
              (WithTopology.ofTopology : WithTopology X t → X)) ∘
                WithTopology.toTopology t)
            (WithTopology.ofTopology : WithTopology X t' → X) hout hmiddle)
      exact heq (le_antisymm hreverse hle)
