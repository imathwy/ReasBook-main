import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Corollary_6_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Criterion_6_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Lemma_6_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Theorem_6_4_5.Endpoints
import Books.AConciseCourseInAlgebraicTopology_May_1999.TopCat.Subspace

open scoped unitInterval
open unitInterval
open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.Types

universe u

variable {X : Type u} [TopologicalSpace X] {A : Set X}

-- Semantic recall via `lean_leansearch`: the available hits were model-categorical cylinder and
-- cofibration APIs, so this source-facing item uses the local Chapter 6 owners `IsNDRPair`,
-- `IsDRPair`, `IsCofibration`, and the earlier product-subspace owner `prodPairUnion`.

/-- Helper for Theorem 6.4.5: a DR-pair witness on `X × {0} ∪ A × I` packages its endpoint map as
an ambient retract of `X × I` onto that cylinder base. -/
lemma cylinderBaseUnionRetract_of_isDRPair
    (h : IsDRPair (prodPairUnion A ({0} : Set I))) :
    ∃ r : C(X × I, X × I),
      Set.range r ⊆ prodPairUnion A ({0} : Set I) ∧
        Set.EqOn r id (prodPairUnion A ({0} : Set I)) := by
  rcases h with ⟨hDR⟩
  -- The DR endpoint already lands in the cylinder base and fixes that base pointwise.
  refine ⟨hDR.retract, hDR.range_subset, hDR.eqOn⟩

/-- Helper for Theorem 6.4.5: every point of the mapping cylinder of `A ↪ X` comes from either the
target copy of `X` or the cylinder copy of `A × I`. -/
lemma subtypeMappingCylinderPointCases
    (z : (TopCat.subtypeInclusion A).hom.mappingCylinder) :
    (∃ x : X, ContinuousMap.mappingCylinderTargetInclusion (TopCat.subtypeInclusion A).hom x = z) ∨
      ∃ y : A × I,
        ContinuousMap.mappingCylinderCylinderInclusion (TopCat.subtypeInclusion A).hom y = z := by
  let hTop : IsPushout
      (TopCat.ofHom (TopCat.subtypeInclusion A).hom)
      (TopCat.ofHom (ContinuousMap.mappingCylinderTimeZeroInclusion A))
      (TopCat.ofHom (ContinuousMap.mappingCylinderTargetInclusion (TopCat.subtypeInclusion A).hom))
      (TopCat.ofHom
        (ContinuousMap.mappingCylinderCylinderInclusion (TopCat.subtypeInclusion A).hom)) :=
    IsPushout.of_hasPushout _ _
  let hType := hTop.map (forget TopCat)
  -- The underlying `Type` pushout cocone is jointly surjective.
  obtain ⟨j, y, hy⟩ :=
    jointly_surjective_of_isColimit hType.isColimit z
  cases j with
  | none =>
      change A at y
      simp only [TopCat.hom_ofHom] at hy
      exact Or.inl ⟨y, hy⟩
  | some val =>
      cases val with
      | left =>
          change X at y
          exact Or.inl ⟨y, hy⟩
      | right =>
          change A × I at y
          exact Or.inr ⟨y, hy⟩

/-- Helper for Theorem 6.4.5: the canonical map from the mapping cylinder of `A ↪ X` lands in the
cylinder base `X × {0} ∪ A × I`. -/
lemma mappingCylinderCanonicalMap_mem_prodPairUnion
    (z : (TopCat.subtypeInclusion A).hom.mappingCylinder) :
    ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom z ∈
      prodPairUnion A ({0} : Set I) := by
  rcases subtypeMappingCylinderPointCases z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · -- On the target copy, the canonical map is the time-`0` inclusion.
    have hEval :
        ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom
            (ContinuousMap.mappingCylinderTargetInclusion (TopCat.subtypeInclusion A).hom x) =
          (x, 0) := by
      have h := congrArg (fun f : C(X, X × I) ↦ f x)
        (ContinuousMap.mappingCylinderCanonicalMap_comp_targetInclusion
          (TopCat.subtypeInclusion A).hom)
      simpa [ContinuousMap.comp_apply, ContinuousMap.mappingCylinderTimeZeroInclusion] using h
    rw [mem_prodPairUnion]
    exact Or.inr (by simpa using congrArg Prod.snd hEval)
  · rcases y with ⟨a, t⟩
    -- On the cylinder copy, the canonical map is exactly `A × I ⟶ X × I`.
    have hEval :
        ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom
            (ContinuousMap.mappingCylinderCylinderInclusion (TopCat.subtypeInclusion A).hom
              (a, t)) =
          ((a : X), t) := by
      have h := congrArg (fun f : C(A × I, X × I) ↦ f (a, t))
        (ContinuousMap.mappingCylinderCanonicalMap_comp_cylinderInclusion
          (TopCat.subtypeInclusion A).hom)
      simpa [ContinuousMap.comp_apply, ContinuousMap.mappingCylinderCylinderMap_apply] using h
    rw [mem_prodPairUnion, hEval]
    exact Or.inl a.2

/-- Helper for Theorem 6.4.5: positive canonical height forces a mapping-cylinder point onto the
cylinder side of the pushout. -/
lemma mappingCylinderPointCases_of_positiveHeight
    (z : (TopCat.subtypeInclusion A).hom.mappingCylinder)
    (hz :
      0 < ((ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom z).2 : ℝ)) :
    ∃ y : A × I,
      ContinuousMap.mappingCylinderCylinderInclusion (TopCat.subtypeInclusion A).hom y = z := by
  -- Compare the point classification with the canonical formulas on the two pushout legs.
  rcases subtypeMappingCylinderPointCases z with ⟨x, hx⟩ | ⟨y, hy⟩
  · exfalso
    have hEval :
        ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom z =
          (x, 0) := by
      calc
        ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom z =
            ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom
              (ContinuousMap.mappingCylinderTargetInclusion (TopCat.subtypeInclusion A).hom x) := by
                rw [hx]
        _ = (x, 0) := by
          have h := congrArg (fun f : C(X, X × I) ↦ f x)
            (ContinuousMap.mappingCylinderCanonicalMap_comp_targetInclusion
              (TopCat.subtypeInclusion A).hom)
          simpa [ContinuousMap.comp_apply, ContinuousMap.mappingCylinderTimeZeroInclusion] using h
    have hNotPos :
        ¬ 0 <
          ((ContinuousMap.mappingCylinderCanonicalMap
            (TopCat.subtypeInclusion A).hom z).2 : ℝ) := by
      have hSecond :
          ((ContinuousMap.mappingCylinderCanonicalMap
            (TopCat.subtypeInclusion A).hom z).2 : I) = 0 :=
        congrArg Prod.snd hEval
      have hSecondReal :
          ((ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom z).2 : ℝ) =
            0 := by
        exact congrArg (fun t : I ↦ (t : ℝ)) hSecond
      simpa [hSecondReal]
    exact (hNotPos hz).elim
  · exact ⟨y, hy⟩

/-- Helper for Theorem 6.4.5: the canonical ambient map induced by a mapping-cylinder retract is
the composite `X × I ⟶ M_i ⟶ X × I`. -/
noncomputable def mappingCylinderRetractAmbientMap
    (r : C(X × I, (TopCat.subtypeInclusion A).hom.mappingCylinder)) : C(X × I, X × I) :=
  (ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom).comp r

/-- Helper for Theorem 6.4.5: the ambient map induced by a mapping-cylinder retract lands in
`X × {0} ∪ A × I`. -/
lemma mappingCylinderRetractAmbientMap_range_subset
    (r : C(X × I, (TopCat.subtypeInclusion A).hom.mappingCylinder)) :
    Set.range (mappingCylinderRetractAmbientMap r) ⊆
      prodPairUnion A ({0} : Set I) := by
  rintro _ ⟨p, rfl⟩
  -- Every point factors through the canonical map image of the mapping cylinder.
  exact mappingCylinderCanonicalMap_mem_prodPairUnion (r p)

/-- Helper for Theorem 6.4.5: the ambient map induced by a mapping-cylinder retract fixes the
cylinder base pointwise. -/
lemma mappingCylinderRetractAmbientMap_eqOn
    (r : C(X × I, (TopCat.subtypeInclusion A).hom.mappingCylinder))
    (hr : IsMappingCylinderRetract r) :
    Set.EqOn (mappingCylinderRetractAmbientMap r) id
      (prodPairUnion A ({0} : Set I)) := by
  intro p hp
  rcases p with ⟨x, t⟩
  rw [mem_prodPairUnion] at hp
  rcases hp with hxA | htZero
  · let a : A := ⟨x, hxA⟩
    -- On `A × I`, the retract agrees with the cylinder inclusion.
    have hCylinder :
        r (x, t) = ContinuousMap.mappingCylinderCylinderInclusion (TopCat.subtypeInclusion A).hom
          (a, t) := by
      have h := congrArg
        (fun f : C(A × I, (TopCat.subtypeInclusion A).hom.mappingCylinder) ↦ f (a, t))
        hr.cylinder
      simpa [ContinuousMap.comp_apply, ContinuousMap.mappingCylinderCylinderMap_apply] using h
    have hEval :
        mappingCylinderRetractAmbientMap r (x, t) = (x, t) := by
      calc
        mappingCylinderRetractAmbientMap r (x, t) =
            ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom
              (r (x, t)) := rfl
        _ =
            ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom
              (ContinuousMap.mappingCylinderCylinderInclusion (TopCat.subtypeInclusion A).hom
                (a, t)) := by
                  rw [hCylinder]
        _ = (x, t) := by
          have h := congrArg (fun f : C(A × I, X × I) ↦ f (a, t))
            (ContinuousMap.mappingCylinderCanonicalMap_comp_cylinderInclusion
              (TopCat.subtypeInclusion A).hom)
          simpa [ContinuousMap.comp_apply,
            ContinuousMap.mappingCylinderCylinderMap_apply, a] using h
    exact hEval
  · rcases Set.mem_singleton_iff.mp htZero with rfl
    -- On `X × {0}`, the retract agrees with the target inclusion.
    have hEndpoint :
        r (x, 0) =
          ContinuousMap.mappingCylinderTargetInclusion (TopCat.subtypeInclusion A).hom x := by
      have h := congrArg
        (fun f : C(X, (TopCat.subtypeInclusion A).hom.mappingCylinder) ↦ f x)
        hr.endpoint
      simpa [ContinuousMap.comp_apply, ContinuousMap.mappingCylinderTimeZeroInclusion] using h
    calc
      mappingCylinderRetractAmbientMap r (x, 0) =
          ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom
            (r (x, 0)) := rfl
      _ =
          ContinuousMap.mappingCylinderCanonicalMap (TopCat.subtypeInclusion A).hom
            (ContinuousMap.mappingCylinderTargetInclusion (TopCat.subtypeInclusion A).hom x) := by
              rw [hEndpoint]
      _ = (x, 0) := by
        have h := congrArg (fun f : C(X, X × I) ↦ f x)
          (ContinuousMap.mappingCylinderCanonicalMap_comp_targetInclusion
            (TopCat.subtypeInclusion A).hom)
        simpa [ContinuousMap.comp_apply, ContinuousMap.mappingCylinderTimeZeroInclusion] using h

/-- Helper for Theorem 6.4.5: a mapping-cylinder retract for `(TopCat.subtypeInclusion A).hom`
induces an ambient retract of `X × {0} ∪ A × I` inside `X × I`. -/
lemma cylinderBaseUnionRetract_of_mappingCylinderRetract
    (r : C(X × I, (TopCat.subtypeInclusion A).hom.mappingCylinder))
    (hr : IsMappingCylinderRetract r) :
    ∃ s : C(X × I, X × I),
      Set.range s ⊆ prodPairUnion A ({0} : Set I) ∧
        Set.EqOn s id (prodPairUnion A ({0} : Set I)) := by
  -- Package the canonical ambient map and its two basic properties.
  refine ⟨mappingCylinderRetractAmbientMap r,
    mappingCylinderRetractAmbientMap_range_subset r,
    mappingCylinderRetractAmbientMap_eqOn r hr⟩

/-- Helper for Theorem 6.4.5: if `X × {0} ∪ A × I` is closed in `X × I`, then `A` is closed in
`X` by restricting along the time-one inclusion `x ↦ (x, 1)`. -/
lemma isClosed_of_closed_cylinderBaseUnion
    (hClosed : IsClosed (prodPairUnion A ({0} : Set I))) :
    IsClosed A := by
  let timeOneInclusion : C(X, X × I) :=
    (ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I))
  have hPreimage :
      timeOneInclusion ⁻¹' prodPairUnion A ({0} : Set I) = A := by
    -- At time `1`, the `{0}` branch disappears, so the cylinder base pulls back exactly to `A`.
    ext x
    change timeOneInclusion x ∈ prodPairUnion A ({0} : Set I) ↔ x ∈ A
    rw [mem_prodPairUnion]
    constructor
    · rintro (hxA | hxZero)
      · exact hxA
      · exfalso
        simp [timeOneInclusion] at hxZero
    · intro hxA
      exact Or.inl hxA
  simpa [timeOneInclusion, hPreimage] using hClosed.preimage timeOneInclusion.continuous

/-- Helper for Theorem 6.4.5: the source-style control associated to an ambient retract onto
`X × {0} ∪ A × I` is the supremum of the height deficits `t - π₂(s(x, t))`. -/
noncomputable def cylinderBaseRetractSupControlRaw
    (s : C(X × I, X × I)) : X → ℝ :=
  fun x ↦ sSup (Set.range fun t : I ↦ (t : ℝ) - ((s (x, t)).2 : ℝ))

/-- Helper for Theorem 6.4.5: the raw supremum control varies continuously with `x`. -/
lemma cylinderBaseRetractSupControlContinuous
    (s : C(X × I, X × I)) :
    Continuous (cylinderBaseRetractSupControlRaw s) := by
  -- Curry the height-defect function and apply compact supremum continuity over the interval `I`.
  let defect : X → I → ℝ := fun x t ↦ (t : ℝ) - ((s (x, t)).2 : ℝ)
  have hDefect : Continuous ↿defect := by
    exact (continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp (continuous_snd.comp s.continuous))
  simpa [cylinderBaseRetractSupControlRaw, defect, Function.uncurry] using
    (IsCompact.continuous_sSup isCompact_univ hDefect)

/-- Helper for Theorem 6.4.5: the raw supremum control lands in the unit interval once the ambient
retract fixes `X × {0} ∪ A × I` pointwise. -/
lemma cylinderBaseRetractSupControlRaw_mem_unitInterval
    {s : C(X × I, X × I)}
    (hRange : Set.range s ⊆ prodPairUnion A ({0} : Set I))
    (hFix : Set.EqOn s id (prodPairUnion A ({0} : Set I)))
    (x : X) :
    cylinderBaseRetractSupControlRaw s x ∈ I := by
  let _ := hRange
  let defect : I → ℝ := fun t ↦ (t : ℝ) - ((s (x, t)).2 : ℝ)
  have hDefectContinuous : Continuous defect := by
    -- Freeze `x` and keep only the time-variable in the height-defect expression.
    exact continuous_subtype_val.sub
      (continuous_subtype_val.comp
        ((continuous_snd.comp s.continuous).comp (continuous_const.prodMk continuous_id)))
  have hBddAbove : BddAbove (Set.range defect) := by
    simpa [Set.image_univ] using isCompact_univ.bddAbove_image hDefectContinuous.continuousOn
  constructor
  · -- The time-zero slice is fixed, so `0` belongs to the image and bounds the supremum below.
    have hFixZero : s (x, 0) = (x, 0) := by
      apply hFix
      rw [mem_prodPairUnion]
      exact Or.inr (by simp)
    have hZeroMem : (0 : ℝ) ∈ Set.range defect := by
      refine ⟨0, ?_⟩
      simp [defect, hFixZero]
    simpa [cylinderBaseRetractSupControlRaw, defect] using le_csSup hBddAbove hZeroMem
  · -- Every time deficit is at most `1`, so the supremum is also at most `1`.
    refine csSup_le (by simpa using Set.range_nonempty defect) ?_
    rintro _ ⟨t, rfl⟩
    have ht_le : (t : ℝ) ≤ 1 := t.2.2
    have hs_nonneg : 0 ≤ ((s (x, t)).2 : ℝ) := (s (x, t)).2.2.1
    have : (t : ℝ) - ((s (x, t)).2 : ℝ) ≤ 1 := by
      nlinarith
    simpa [defect] using this

/-- Helper for Theorem 6.4.5: bundling the raw supremum control gives the `u : X → I` used in the
ambient-retract proof of the NDR criterion. -/
noncomputable def cylinderBaseRetractSupControl
    {s : C(X × I, X × I)}
    (hRange : Set.range s ⊆ prodPairUnion A ({0} : Set I))
    (hFix : Set.EqOn s id (prodPairUnion A ({0} : Set I))) :
    C(X, I) :=
  { toFun := fun x ↦
      ⟨cylinderBaseRetractSupControlRaw s x,
        cylinderBaseRetractSupControlRaw_mem_unitInterval hRange hFix x⟩
    continuous_toFun :=
      (cylinderBaseRetractSupControlContinuous s).subtype_mk _ }

/-- Helper for Theorem 6.4.5: the bundled supremum control vanishes exactly on `A`. -/
lemma cylinderBaseRetractSupControl_zero_iff
    (hA : IsClosed A) {s : C(X × I, X × I)}
    (hRange : Set.range s ⊆ prodPairUnion A ({0} : Set I))
    (hFix : Set.EqOn s id (prodPairUnion A ({0} : Set I)))
    (x : X) :
    cylinderBaseRetractSupControl hRange hFix x = 0 ↔ x ∈ A := by
  let defect : I → ℝ := fun t ↦ (t : ℝ) - ((s (x, t)).2 : ℝ)
  have hDefectContinuous : Continuous defect := by
    -- Freeze `x` and keep only the time-variable in the defect path.
    exact continuous_subtype_val.sub
      (continuous_subtype_val.comp
        ((continuous_snd.comp s.continuous).comp (continuous_const.prodMk continuous_id)))
  have hBddAbove : BddAbove (Set.range defect) := by
    simpa [Set.image_univ] using isCompact_univ.bddAbove_image hDefectContinuous.continuousOn
  constructor
  · intro hxZero
    -- A positive-time sequence stays in `A`, and closedness lets the limit point at time `0`
    -- return to `A`.
    have hSupZero :
        cylinderBaseRetractSupControlRaw s x = 0 := by
      simpa [cylinderBaseRetractSupControl] using
        congrArg (fun t : I ↦ (t : ℝ)) hxZero
    let approachingZero : ℕ → I :=
      fun n ↦
        ⟨(1 : ℝ) / ((n : ℝ) + 1), by
          constructor
          · positivity
          · have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
            have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
            have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
            have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
              have hden' : (1 : ℝ) / 1 ≤ (n : ℝ) + 1 := by
                simp [hden]
              exact (one_div_le hpos (by positivity : (0 : ℝ) < 1)).2 hden'
            simpa using hle⟩
    have hApproachingZero :
        Filter.Tendsto approachingZero Filter.atTop (nhds (0 : I)) := by
      refine tendsto_subtype_rng.mpr ?_
      simpa [approachingZero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0))
    let slice : C(I, X × I) := (ContinuousMap.const I x).prodMk (ContinuousMap.id I)
    let path : C(I, X) := ContinuousMap.fst.comp (s.comp slice)
    have hPathZero : path 0 = x := by
      -- The retract fixes the time-zero base `X × {0}` pointwise.
      have hFixZero : s (x, 0) = (x, 0) := by
        apply hFix
        rw [mem_prodPairUnion]
        exact Or.inr (by simp)
      simpa [path, slice] using congrArg Prod.fst hFixZero
    have hPathMem : ∀ n : ℕ, path (approachingZero n) ∈ A := by
      intro n
      have hSliceLe :
          defect (approachingZero n) ≤ 0 := by
        have hMem :
            defect (approachingZero n) ∈ Set.range defect := by
          exact ⟨approachingZero n, rfl⟩
        have hLeSup : defect (approachingZero n) ≤ cylinderBaseRetractSupControlRaw s x := by
          simpa [cylinderBaseRetractSupControlRaw, defect] using le_csSup hBddAbove hMem
        simpa [hSupZero] using hLeSup
      have hUnion :
          s (x, approachingZero n) ∈ prodPairUnion A ({0} : Set I) :=
        hRange ⟨(x, approachingZero n), rfl⟩
      rw [mem_prodPairUnion] at hUnion
      rcases hUnion with hxA | hZero
      · simpa [path, slice] using hxA
      · exfalso
        have hPositive : (0 : ℝ) < (approachingZero n : ℝ) := by
          positivity
        have hSecondGe : (approachingZero n : ℝ) ≤ ((s (x, approachingZero n)).2 : ℝ) := by
          nlinarith [hSliceLe]
        have hSecondPos : (0 : ℝ) < ((s (x, approachingZero n)).2 : ℝ) :=
          lt_of_lt_of_le hPositive hSecondGe
        have hEq : (s (x, approachingZero n)).2 = 0 := Set.mem_singleton_iff.mp hZero
        exact hSecondPos.ne' (by simp [hEq])
    have hPathLimit :
        Filter.Tendsto (fun n : ℕ ↦ path (approachingZero n)) Filter.atTop (nhds x) := by
      have hPathAtZero : ContinuousAt path 0 := path.continuous.continuousAt
      simpa [hPathZero] using hPathAtZero.tendsto.comp hApproachingZero
    exact hA.mem_of_tendsto hPathLimit (Filter.Eventually.of_forall hPathMem)
  · intro hxA
    -- Points of `A` are fixed for every time, so every height deficit is zero.
    apply Subtype.ext
    apply le_antisymm
    · refine csSup_le (by simpa using Set.range_nonempty defect) ?_
      rintro _ ⟨t, rfl⟩
      have hFixA : s (x, t) = (x, t) := by
        apply hFix
        rw [mem_prodPairUnion]
        exact Or.inl hxA
      simp [hFixA]
    · have hFixZero : s (x, 0) = (x, 0) := by
        apply hFix
        rw [mem_prodPairUnion]
        exact Or.inr (by simp)
      have hZeroMem : (0 : ℝ) ∈ Set.range defect := by
        refine ⟨0, ?_⟩
        simp [defect, hFixZero]
      simpa [cylinderBaseRetractSupControl, cylinderBaseRetractSupControlRaw, defect] using
        le_csSup hBddAbove hZeroMem

/-- Helper for Theorem 6.4.5: if the bundled supremum control is `< 1`, then the time-one slice of
the ambient retract lies in `A`. -/
lemma cylinderBaseRetractEndpoint_mem
    {s : C(X × I, X × I)}
    (hRange : Set.range s ⊆ prodPairUnion A ({0} : Set I))
    (hFix : Set.EqOn s id (prodPairUnion A ({0} : Set I)))
    (x : X)
    (hx :
      cylinderBaseRetractSupControl hRange hFix x < 1) :
    (s (x, 1)).1 ∈ A := by
  let defect : I → ℝ := fun t ↦ (t : ℝ) - ((s (x, t)).2 : ℝ)
  have hDefectContinuous : Continuous defect := by
    -- Freeze `x` and keep only the time-variable in the defect path.
    exact continuous_subtype_val.sub
      (continuous_subtype_val.comp
        ((continuous_snd.comp s.continuous).comp (continuous_const.prodMk continuous_id)))
  have hBddAbove : BddAbove (Set.range defect) := by
    simpa [Set.image_univ] using isCompact_univ.bddAbove_image hDefectContinuous.continuousOn
  have hSupLt :
      cylinderBaseRetractSupControlRaw s x < 1 := by
    simpa [cylinderBaseRetractSupControl] using hx
  have hUnion : s (x, 1) ∈ prodPairUnion A ({0} : Set I) :=
    hRange ⟨(x, 1), rfl⟩
  rw [mem_prodPairUnion] at hUnion
  rcases hUnion with hxA | hZero
  · exact hxA
  · exfalso
    have hDefectAtOne :
        defect 1 ≤ cylinderBaseRetractSupControlRaw s x := by
      have hMem : defect 1 ∈ Set.range defect := ⟨1, rfl⟩
      simpa [cylinderBaseRetractSupControlRaw, defect] using le_csSup hBddAbove hMem
    have hEq : (s (x, 1)).2 = 0 := Set.mem_singleton_iff.mp hZero
    have hOneLe :
        (1 : ℝ) ≤ cylinderBaseRetractSupControlRaw s x := by
      simpa [defect, hEq] using hDefectAtOne
    linarith

/-- Helper for Theorem 6.4.5: a closed ambient retract onto `X × {0} ∪ A × I` produces the
source-style NDR witness on `A`. -/
lemma isNDRPair_of_closed_cylinderBaseUnion_retract
    (hA : IsClosed A)
    {s : C(X × I, X × I)}
    (hRange : Set.range s ⊆ prodPairUnion A ({0} : Set I))
    (hFix : Set.EqOn s id (prodPairUnion A ({0} : Set I))) :
    IsNDRPair A := by
  let control : C(X, I) := cylinderBaseRetractSupControl hRange hFix
  let timeOneInclusion : C(X, X × I) :=
    (ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I))
  let retract : C(X, X) := ContinuousMap.fst.comp (s.comp timeOneInclusion)
  let homotopyMap : C(X × I, X) := ContinuousMap.fst.comp s
  have hZero : ∀ x : X, homotopyMap (x, 0) = x := by
    -- The ambient retract fixes the cylinder base at time `0`.
    intro x
    have hFixZero : s (x, 0) = (x, 0) := by
      apply hFix
      rw [mem_prodPairUnion]
      exact Or.inr (by simp)
    simpa [homotopyMap] using congrArg Prod.fst hFixZero
  have hOne : ∀ x : X, homotopyMap (x, 1) = retract x := by
    -- The endpoint map is exactly the time-one slice of the first coordinate.
    intro x
    rfl
  let homotopy : (ContinuousMap.id X).Homotopy retract :=
    ContinuousMap.Homotopy.ofProdSwap homotopyMap hZero hOne
  have hRel : (ContinuousMap.id X).HomotopyRel retract A := by
    refine ⟨homotopy, ?_⟩
    -- Points of `A` stay fixed for the entire homotopy because the ambient retract fixes `A × I`.
    intro t x hxA
    have hFixA : s (x, t) = (x, t) := by
      apply hFix
      rw [mem_prodPairUnion]
      exact Or.inl hxA
    simpa [homotopy, homotopyMap, ContinuousMap.Homotopy.ofProdSwap] using
      congrArg Prod.fst hFixA
  have hZeroSet : control ⁻¹' ({0} : Set I) = A := by
    -- The zero-set calculation is exactly the source-style supremum-control criterion.
    ext x
    simpa [control] using cylinderBaseRetractSupControl_zero_iff hA hRange hFix x
  have hEndpoint : ∀ x, control x < 1 → retract x ∈ A := by
    -- The time-one point must lie on the `A × I` branch once the control is `< 1`.
    intro x hx
    simpa [control, retract, timeOneInclusion] using
      cylinderBaseRetractEndpoint_mem hRange hFix x hx
  exact ⟨control, retract, ⟨hRel⟩, hZeroSet, hEndpoint⟩

/-- Helper for Theorem 6.4.5: an NDR-pair already gives the ambient cylinder-base retract used in
part (2). -/
lemma cylinderBaseUnionRetract_of_isNDRPair
    (hA : IsNDRPair A) :
    ∃ r : C(X × I, X × I),
      Set.range r ⊆ prodPairUnion A ({0} : Set I) ∧
        Set.EqOn r id (prodPairUnion A ({0} : Set I)) := by
  -- The forward half of Theorem 6.4.5 (1) is the standard product DR construction.
  exact cylinderBaseUnionRetract_of_isDRPair
    (isDRPair_prod_union_right hA zeroSingletonIsDRPair)

/-- First equivalence in Theorem 6.4.5: `(X, A)` is an NDR-pair exactly when the cylinder pair
`(X × I, X × {0} ∪ A × I)` is a DR-pair; the closedness of `A` is automatic on either side. -/
theorem isNDRPair_iff_cylinderBaseUnion_isDRPair :
    IsNDRPair A ↔ IsDRPair (prodPairUnion A ({0} : Set I)) := by
  constructor
  · intro hA
    -- The product DR construction applies with the right factor `({0} : Set I)`.
    exact isDRPair_prod_union_right hA zeroSingletonIsDRPair
  · intro hCylinder
    -- The cylinder DR-pair is closed, and its time-one slice detects the closedness of `A`.
    have hClosed :
        IsClosed A := isClosed_of_closed_cylinderBaseUnion
          ((isNDRPair_of_isDRPair hCylinder).isClosed)
    rcases cylinderBaseUnionRetract_of_isDRPair hCylinder with ⟨r, hRange, hFix⟩
    -- Once the ambient retract is available, the closed retract criterion yields the NDR witness.
    exact isNDRPair_of_closed_cylinderBaseUnion_retract hClosed hRange hFix

/-- Second equivalence in Theorem 6.4.5: for `A` closed in `X`, the pair `(X, A)` is an NDR-pair
exactly when `X × {0} ∪ A × I` is a retract of `X × I`. -/
theorem isNDRPair_iff_exists_cylinderBaseUnion_retract (hA : IsClosed A) :
    IsNDRPair A ↔
      ∃ r : C(X × I, X × I),
        Set.range r ⊆ prodPairUnion A ({0} : Set I) ∧
          Set.EqOn r id (prodPairUnion A ({0} : Set I)) := by
  constructor
  · intro hNDR
    -- First turn the NDR data into the cylinder DR-pair, then extract its endpoint retract.
    exact cylinderBaseUnionRetract_of_isNDRPair hNDR
  · intro hRetract
    rcases hRetract with ⟨s, hRange, hFix⟩
    exact isNDRPair_of_closed_cylinderBaseUnion_retract hA hRange hFix

/-- Helper for Theorem 6.4.5: an ambient retract onto `X × {0} ∪ A × I` should factor through
the mapping cylinder of `A ↪ X`. -/
lemma mappingCylinderRetract_of_cylinderBaseUnionRetract
    (hA : IsClosed A)
    (s : C(X × I, X × I))
    (hRange : Set.range s ⊆ prodPairUnion A ({0} : Set I))
    (hFix : Set.EqOn s id (prodPairUnion A ({0} : Set I))) :
    ∃ r : C(X × I, (TopCat.subtypeInclusion A).hom.mappingCylinder),
      IsMappingCylinderRetract r := by
  -- Route correction: the forward implication should factor the ambient retract through the
  -- ambient cylinder base via a continuous piecewise comparison map.
  classical
  let i : C(A, X) := (TopCat.subtypeInclusion A).hom
  let U := ↥(prodPairUnion A ({0} : Set I))
  let zeroSlice : Set U := {u | u.1.2 = 0}
  let aSlice : Set U := {u | u.1.1 ∈ A}
  let targetFun : U → i.mappingCylinder :=
    fun u ↦ ContinuousMap.mappingCylinderTargetInclusion i u.1.1
  let cylinderOrTarget : U → i.mappingCylinder :=
    fun u ↦
      if hx : u.1.1 ∈ A then
        ContinuousMap.mappingCylinderCylinderInclusion i ⟨⟨u.1.1, hx⟩, u.1.2⟩
      else
        ContinuousMap.mappingCylinderTargetInclusion i u.1.1
  have hTargetFunContinuous : Continuous targetFun := by
    -- The target branch only reads the first cylinder coordinate.
    have hFirst : Continuous fun u : U ↦ u.1.1 := continuous_fst.comp continuous_subtype_val
    simpa [targetFun] using (ContinuousMap.mappingCylinderTargetInclusion i).continuous.comp hFirst
  have hZeroSliceClosed : IsClosed zeroSlice := by
    -- The zero slice is the closed fiber of the height coordinate over `{0}`.
    have hSecond : Continuous fun u : U ↦ u.1.2 := continuous_snd.comp continuous_subtype_val
    simpa [zeroSlice] using (isClosed_singleton.preimage hSecond)
  have hASliceClosed : IsClosed aSlice := by
    -- Closedness of `A` pulls back along the first coordinate of `U ⊆ X × I`.
    have hFirst : Continuous fun u : U ↦ u.1.1 := continuous_fst.comp continuous_subtype_val
    simpa [aSlice] using hA.preimage hFirst
  have hNonzeroSubset : zeroSliceᶜ ⊆ aSlice := by
    -- Away from height `0`, membership in the union forces the point onto the `A × I` branch.
    intro u hu
    have huNonzero : u.1.2 ≠ 0 := by
      simpa [zeroSlice] using hu
    have huUnion : u.1 ∈ prodPairUnion A ({0} : Set I) := u.2
    rw [mem_prodPairUnion] at huUnion
    rcases huUnion with huA | huZero
    · simpa [aSlice] using huA
    · exact False.elim <| huNonzero <| Set.mem_singleton_iff.mp huZero
  have hNonzeroClosureSubset : closure (zeroSliceᶜ) ⊆ aSlice :=
    closure_minimal hNonzeroSubset hASliceClosed
  have hCylinderOrTargetContinuousOnASlice : ContinuousOn cylinderOrTarget aSlice := by
    -- On the `A`-slice the comparison map is literally the cylinder inclusion.
    rw [continuousOn_iff_continuous_restrict]
    have hRestrictEq :
        aSlice.restrict cylinderOrTarget =
          fun u : aSlice ↦
            ContinuousMap.mappingCylinderCylinderInclusion i
              ⟨⟨u.1.1.1, u.2⟩, u.1.1.2⟩ := by
      funext u
      by_cases hx : (↑u : U).1.1 ∈ A
      · have hArg : (⟨u.1.1.1, hx⟩ : A) = ⟨u.1.1.1, u.2⟩ := by
          apply Subtype.ext
          rfl
        simp [Set.restrict, cylinderOrTarget, hx, hArg]
      · exact False.elim (hx u.2)
    rw [hRestrictEq]
    have hAcoord : Continuous fun u : aSlice ↦ ((⟨u.1.1.1, u.2⟩ : A) : A) := by
      have hBase : Continuous fun u : aSlice ↦ u.1.1.1 := by
        exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
      simpa using hBase.subtype_mk fun u ↦ u.2
    have hTcoord : Continuous fun u : aSlice ↦ u.1.1.2 := by
      exact continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact (ContinuousMap.mappingCylinderCylinderInclusion i).continuous.comp
      (hAcoord.prodMk hTcoord)
  have hCylinderOrTargetContinuousOnNonzeroClosure :
      ContinuousOn cylinderOrTarget (closure zeroSliceᶜ) :=
    hCylinderOrTargetContinuousOnASlice.mono hNonzeroClosureSubset
  have hFrontierAgreement : ∀ u ∈ frontier zeroSlice, targetFun u = cylinderOrTarget u := by
    intro u hu
    have huZero : u.1.2 = 0 := by
      simpa [zeroSlice, hZeroSliceClosed.closure_eq] using hu.1
    by_cases hx : u.1.1 ∈ A
    · -- On `A × {0}`, the target and cylinder legs are identified in the pushout.
      have hCompat :=
        congrArg (fun f : C(A, i.mappingCylinder) ↦ f ⟨u.1.1, hx⟩)
          (ContinuousMap.mappingCylinderTargetInclusion_comp i)
      simpa [targetFun, cylinderOrTarget, ContinuousMap.comp_apply,
        ContinuousMap.mappingCylinderTimeZeroInclusion, huZero, hx] using hCompat
    · simp [targetFun, cylinderOrTarget, hx]
  have hComparisonContinuous :
      Continuous (zeroSlice.piecewise targetFun cylinderOrTarget) := by
    -- The zero slice is closed, and the cylinder branch agrees with the target branch there.
    exact continuous_piecewise hFrontierAgreement hTargetFunContinuous.continuousOn
      hCylinderOrTargetContinuousOnNonzeroClosure
  let comparisonMap : C(U, i.mappingCylinder) :=
    { toFun := zeroSlice.piecewise targetFun cylinderOrTarget
      continuous_toFun := hComparisonContinuous }
  let sSub : C(X × I, U) :=
    { toFun := fun p ↦ ⟨s p, hRange ⟨p, rfl⟩⟩
      continuous_toFun := s.continuous.subtype_mk fun p ↦ hRange ⟨p, rfl⟩ }
  let r : C(X × I, i.mappingCylinder) := comparisonMap.comp sSub
  have hEndpoint :
      r.comp (ContinuousMap.mappingCylinderTimeZeroInclusion X) =
        ContinuousMap.mappingCylinderTargetInclusion i := by
    -- The ambient retract fixes the bottom edge pointwise, where the comparison map is the
    -- target inclusion.
    ext x
    have hxMem : (x, 0) ∈ prodPairUnion A ({0} : Set I) := by
      rw [mem_prodPairUnion]
      exact Or.inr (by simp)
    have hxFix : s (x, 0) = (x, 0) := hFix hxMem
    have hxSub : sSub (x, 0) = ⟨(x, 0), hxMem⟩ := by
      apply Subtype.ext
      simpa [sSub] using hxFix
    calc
      (r.comp (ContinuousMap.mappingCylinderTimeZeroInclusion X)) x = r (x, 0) := by
        simp [ContinuousMap.comp_apply, ContinuousMap.mappingCylinderTimeZeroInclusion]
      _ = comparisonMap (sSub (x, 0)) := rfl
      _ = comparisonMap ⟨(x, 0), hxMem⟩ := by rw [hxSub]
      _ = ContinuousMap.mappingCylinderTargetInclusion i x := by
        simp [comparisonMap, zeroSlice, targetFun, cylinderOrTarget]
  have hCylinder :
      r.comp (ContinuousMap.mappingCylinderCylinderMap i) =
        ContinuousMap.mappingCylinderCylinderInclusion i := by
    -- The ambient retract fixes the entire `A × I` branch, and the comparison map reads it as
    -- the cylinder inclusion.
    ext z
    rcases z with ⟨a, t⟩
    have hzMem : (((a : X), t) : X × I) ∈ prodPairUnion A ({0} : Set I) := by
      rw [mem_prodPairUnion]
      exact Or.inl a.2
    have hzFix : s ((a : X), t) = ((a : X), t) := hFix hzMem
    have hzSub : sSub ((a : X), t) = ⟨((a : X), t), hzMem⟩ := by
      apply Subtype.ext
      simpa [sSub] using hzFix
    calc
      (r.comp (ContinuousMap.mappingCylinderCylinderMap i)) (a, t) =
          r (i a, t) := by
            simp [ContinuousMap.comp_apply, ContinuousMap.mappingCylinderCylinderMap_apply]
      _ = r ((a : X), t) := by
        simp [i]
      _ = comparisonMap (sSub ((a : X), t)) := rfl
      _ = comparisonMap ⟨((a : X), t), hzMem⟩ := by rw [hzSub]
      _ = ContinuousMap.mappingCylinderCylinderInclusion i (a, t) := by
        by_cases ht : t = 0
        · have hCompat :=
            congrArg (fun f : C(A, i.mappingCylinder) ↦ f a)
              (ContinuousMap.mappingCylinderTargetInclusion_comp i)
          simpa [comparisonMap, zeroSlice, targetFun, cylinderOrTarget,
            ContinuousMap.comp_apply, ContinuousMap.mappingCylinderTimeZeroInclusion, ht] using
            hCompat
        · simp [comparisonMap, zeroSlice, targetFun, cylinderOrTarget, ht]
  have hLeftInv :
      r.comp (ContinuousMap.mappingCylinderCanonicalMap i) =
        ContinuousMap.id i.mappingCylinder := by
    -- Once the two boundary restrictions match, pushout uniqueness gives the left inverse.
    have hcat :
        TopCat.ofHom (r.comp (ContinuousMap.mappingCylinderCanonicalMap i)) =
          TopCat.ofHom (ContinuousMap.id i.mappingCylinder) := by
      apply pushout.hom_ext
      · simpa [TopCat.ofHom_comp] using
          congrArg TopCat.ofHom
            (by
              rw [ContinuousMap.comp_assoc,
                ContinuousMap.mappingCylinderCanonicalMap_comp_targetInclusion, hEndpoint]
              simp :
                ((r.comp (ContinuousMap.mappingCylinderCanonicalMap i)).comp
                    (ContinuousMap.mappingCylinderTargetInclusion i)) =
                  (ContinuousMap.id i.mappingCylinder).comp
                    (ContinuousMap.mappingCylinderTargetInclusion i))
      · simpa [TopCat.ofHom_comp] using
          congrArg TopCat.ofHom
            (by
              rw [ContinuousMap.comp_assoc,
                ContinuousMap.mappingCylinderCanonicalMap_comp_cylinderInclusion, hCylinder]
              simp :
                ((r.comp (ContinuousMap.mappingCylinderCanonicalMap i)).comp
                    (ContinuousMap.mappingCylinderCylinderInclusion i)) =
                  (ContinuousMap.id i.mappingCylinder).comp
                    (ContinuousMap.mappingCylinderCylinderInclusion i))
    simpa using congrArg TopCat.Hom.hom hcat
  exact ⟨r, ⟨hLeftInv, hEndpoint, hCylinder⟩⟩

/-- Helper for Theorem 6.4.5: the mapping-cylinder retract gives the exact zero set of the
supremum control without an external closedness hypothesis on `A`. -/
lemma cylinderBaseRetractSupControl_zero_iff_of_mappingCylinderRetract
    (hA : IsClosed A)
    (r : C(X × I, (TopCat.subtypeInclusion A).hom.mappingCylinder))
    (hr : IsMappingCylinderRetract r) (x : X) :
    cylinderBaseRetractSupControl
        (mappingCylinderRetractAmbientMap_range_subset r)
        (mappingCylinderRetractAmbientMap_eqOn r hr) x = 0 ↔
      x ∈ A := by
  -- The mapping-cylinder retract already induces the ambient retract handled by the closed
  -- supremum-control criterion proved earlier.
  simpa using cylinderBaseRetractSupControl_zero_iff hA
    (mappingCylinderRetractAmbientMap_range_subset r)
    (mappingCylinderRetractAmbientMap_eqOn r hr) x

/-- Helper for Theorem 6.4.5: a mapping-cylinder retract for the subtype inclusion packages the
ambient retract data back into an NDR witness. -/
lemma isNDRPair_of_mappingCylinderRetractSubtype
    (hA : IsClosed A)
    (r : C(X × I, (TopCat.subtypeInclusion A).hom.mappingCylinder))
    (hr : IsMappingCylinderRetract r) :
    IsNDRPair A := by
  -- The reverse implication now reuses the closed ambient-retract criterion instead of rebuilding
  -- the supremum control directly on the mapping cylinder.
  rcases cylinderBaseUnionRetract_of_mappingCylinderRetract r hr with ⟨s, hRange, hFix⟩
  exact isNDRPair_of_closed_cylinderBaseUnion_retract hA hRange hFix

/-- Theorem 6.4.5::statement_repair::3. For `A` closed in `X`, the pair `(X, A)` is an NDR-pair
exactly when the canonical inclusion `A ↪ X`, viewed as
`(TopCat.subtypeInclusion A).hom : C(A, X)`, is a cofibration. -/
theorem isNDRPair_iff_isCofibration_subtypeVal (hA : IsClosed A) :
    IsNDRPair A ↔ IsCofibration.{u, u, u} (TopCat.subtypeInclusion A).hom := by
  constructor
  · intro hNDR
    -- First extract the ambient cylinder-base retract, then convert it into the mapping-cylinder
    -- retract required by Criterion 6.2.3.
    rcases (isNDRPair_iff_exists_cylinderBaseUnion_retract hA).1 hNDR with ⟨s, hRange, hFix⟩
    rcases mappingCylinderRetract_of_cylinderBaseUnionRetract hA s hRange hFix with ⟨r, hr⟩
    exact (isCofibration_iff_exists_mappingCylinderRetract).2 ⟨r, hr⟩
  · intro hCofibration
    -- A cofibration supplies a mapping-cylinder retract, and the closed ambient retract criterion
    -- turns that back into the desired NDR data.
    rcases (isCofibration_iff_exists_mappingCylinderRetract).1 hCofibration with ⟨r, hr⟩
    exact isNDRPair_of_mappingCylinderRetractSubtype hA r hr
