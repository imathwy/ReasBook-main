import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.EffectiveEpi
import Mathlib.CategoryTheory.Category.ULift
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Example_5_1_12
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_2_3

open CategoryTheory CategoryTheory.Limits
open Set

universe u v w

-- Semantic search hits: `TopologicalSpace.compactlyGenerated`,
-- `uCompactlyGeneratedSpace_of_coinduced`, `CompactlyGenerated`; local precedent:
-- `CompactlyGeneratedWeakHausdorffSpace` from
-- `Definition_5_1_10`. This remark is formalized on the canonical `TopCat` colimit object.

/-- Helper for Remark 5.2.13: the colimit topology on `colimit F` is the coinduced topology from
the single sigma-desc map out of the disjoint union of the diagram objects. -/
lemma colimitTopology_eq_coinducedSigmaDesc
    {J : Type u} [Category.{v} J] (F : J ⥤ TopCat.{w}) [HasColimit F] :
    (colimit F).str =
      TopologicalSpace.coinduced
        (fun x : Σ j, F.obj j ↦ colimit.ι F x.1 x.2) inferInstance := by
  -- Rewrite the colimit topology as the supremum of the coinduced topologies of the structure
  -- maps and then package those maps through the sigma coproduct.
  rw [TopCat.colimit_topology, instTopologicalSpaceSigma, coinduced_iSup]
  apply iSup_congr
  intro j
  rw [coinduced_compose]
  rfl

/-- Helper for Remark 5.2.13: the carrier used in the counterexample is the real line lifted to
the target universe. -/
abbrev openUnitIntervalCollapseCarrier :=
  ULift.{w} ℝ

/-- Helper for Remark 5.2.13: the subset collapsed in the counterexample is the open interval
`(0, 1)` inside `ULift ℝ`. -/
def openUnitIntervalSet : Set openUnitIntervalCollapseCarrier :=
  fun x ↦ (x.down : ℝ) ∈ Set.Ioo (0 : ℝ) 1

/-- Helper for Remark 5.2.13: the open interval `(0, 1)` in `ℝ` is not closed. -/
lemma openUnitInterval_notClosed : ¬ IsClosed (Set.Ioo (0 : ℝ) 1) := by
  intro hClosed
  -- The closure of `(0,1)` contains the endpoint `0`, so closedness would force `0 ∈ (0,1)`.
  have h01 : (0 : ℝ) ≠ 1 := by
    norm_num
  have hZero : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo h01]
    simp
  rw [hClosed.closure_eq] at hZero
  simp at hZero

/-- Helper for Remark 5.2.13: the lifted open interval remains nonclosed. -/
lemma openUnitIntervalSet_notClosed : ¬ IsClosed openUnitIntervalSet := by
  intro hClosed
  -- Pull back along `ULift.up` to reduce to the standard nonclosed interval in `ℝ`.
  have hPreimage :
      IsClosed (ULift.up ⁻¹' openUnitIntervalSet) := hClosed.preimage continuous_uliftUp
  have hReal : IsClosed (Set.Ioo (0 : ℝ) 1) := by
    have hEq : ULift.up ⁻¹' openUnitIntervalSet = Set.Ioo (0 : ℝ) 1 := by
      ext x
      rfl
    rw [← hEq]
    exact hPreimage
  exact openUnitInterval_notClosed hReal

/-- Helper for Remark 5.2.13: the quotient relation identifies every two points of the open unit
interval and leaves all other points distinct. -/
def collapseOpenUnitIntervalRel
    (x y : openUnitIntervalCollapseCarrier) : Prop :=
  x = y ∨ x ∈ openUnitIntervalSet ∧ y ∈ openUnitIntervalSet

/-- Helper for Remark 5.2.13: the collapse relation on `ULift ℝ` is an equivalence relation. -/
theorem collapseOpenUnitIntervalRel_equivalence :
    Equivalence collapseOpenUnitIntervalRel := by
  refine ⟨?_, ?_, ?_⟩
  · -- Equality gives reflexivity immediately.
    intro x
    exact Or.inl rfl
  · -- Swapping the two interval-membership witnesses preserves the collapsed branch.
    intro x y hxy
    rcases hxy with rfl | hxy
    · exact Or.inl rfl
    · exact Or.inr ⟨hxy.2, hxy.1⟩
  · -- Two collapsed-step relations compose because the middle point stays in the interval.
    intro x y z hxy hyz
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr ⟨hxy.1, hxy.2⟩
    · exact Or.inr ⟨hxy.1, hyz.2⟩

/-- Helper for Remark 5.2.13: the setoid collapsing the open unit interval to one point. -/
def collapseOpenUnitIntervalSetoid : Setoid openUnitIntervalCollapseCarrier where
  r := collapseOpenUnitIntervalRel
  iseqv := collapseOpenUnitIntervalRel_equivalence

/-- Helper for Remark 5.2.13: the quotient relation induced by collapsing `(0,1)` is not closed in
the square because its pullback along `x ↦ (x, 1/2)` is exactly the nonclosed interval `(0,1)`. -/
lemma collapseOpenUnitIntervalRelation_notClosed :
    ¬ IsClosed
      ({p : openUnitIntervalCollapseCarrier × openUnitIntervalCollapseCarrier |
        collapseOpenUnitIntervalSetoid.r p.1 p.2} : Set _) := by
  let mid : openUnitIntervalCollapseCarrier := ULift.up (1 / 2 : ℝ)
  have hMid : mid ∈ openUnitIntervalSet := by
    -- The chosen probe point lies in the interval branch of the quotient relation.
    have hMidReal : ((mid.down : ℝ) ∈ Set.Ioo (0 : ℝ) 1) := by
      simp [mid]
      norm_num
    simpa [openUnitIntervalSet] using hMidReal
  let probe : openUnitIntervalCollapseCarrier →
      openUnitIntervalCollapseCarrier × openUnitIntervalCollapseCarrier :=
    fun x ↦ (x, mid)
  have hProbe :
      probe ⁻¹'
          ({p : openUnitIntervalCollapseCarrier × openUnitIntervalCollapseCarrier |
            collapseOpenUnitIntervalSetoid.r p.1 p.2} : Set _) =
        openUnitIntervalSet := by
    -- Fixing the second coordinate at `1/2` turns the relation test into membership in `(0,1)`.
    ext x
    change collapseOpenUnitIntervalSetoid.r x mid ↔ x ∈ openUnitIntervalSet
    constructor
    · intro hx
      rcases hx with rfl | ⟨hx, _⟩
      · simpa [mid] using hMid
      · exact hx
    · intro hx
      change collapseOpenUnitIntervalRel x mid
      exact Or.inr ⟨hx, hMid⟩
  intro hClosed
  have hProbeContinuous : Continuous probe := by
    -- The probe is the graph of a constant map.
    simpa [probe] using continuous_id.prodMk continuous_const
  have hIntervalClosed : IsClosed openUnitIntervalSet := by
    rw [← hProbe]
    exact hClosed.preimage hProbeContinuous
  exact openUnitIntervalSet_notClosed hIntervalClosed

/-- Helper for Remark 5.2.13: collapsing the open unit interval `(0,1) ⊂ ULift ℝ` produces a
quotient space that is not weak Hausdorff. -/
lemma collapseOpenUnitIntervalQuotient_notWeaklyHausdorff :
    ¬ WeaklyHausdorffSpace.{w, w} (Quotient collapseOpenUnitIntervalSetoid) := by
  let _ : Setoid openUnitIntervalCollapseCarrier := collapseOpenUnitIntervalSetoid
  let q : openUnitIntervalCollapseCarrier →
      Quotient collapseOpenUnitIntervalSetoid := Quotient.mk'
  have hq : Topology.IsQuotientMap q := by
    simpa [q] using
      (isQuotientMap_quotient_mk' :
        Topology.IsQuotientMap
          (Quotient.mk' : openUnitIntervalCollapseCarrier → Quotient collapseOpenUnitIntervalSetoid))
  let _ : CompactlyGeneratedWeakHausdorffSpace openUnitIntervalCollapseCarrier := inferInstance
  intro hWeak
  let _ : WeaklyHausdorffSpace.{w, w} (Quotient collapseOpenUnitIntervalSetoid) := hWeak
  -- Proposition 5.2.2 converts weak Hausdorffness of the quotient into closedness of its kernel
  -- relation in the square of the source.
  have hClosed :
      IsClosed
        ((Prod.map q q) ⁻¹'
          diagonal (Quotient collapseOpenUnitIntervalSetoid)) :=
    (weaklyHausdorffSpace_iff_isClosed_preimage_diagonal_of_isQuotientMap q hq).mp inferInstance
  have hRelationEq :
      ((Prod.map q q) ⁻¹' diagonal (Quotient collapseOpenUnitIntervalSetoid)) =
        ({p : openUnitIntervalCollapseCarrier × openUnitIntervalCollapseCarrier |
          collapseOpenUnitIntervalSetoid.r p.1 p.2} : Set _) := by
    ext p
    simpa [q, diagonal] using
      (Quotient.eq : Quotient.mk' p.1 = Quotient.mk' p.2 ↔ collapseOpenUnitIntervalSetoid p.1 p.2)
  have hRelationClosed :
      IsClosed
        ({p : openUnitIntervalCollapseCarrier × openUnitIntervalCollapseCarrier |
          collapseOpenUnitIntervalSetoid.r p.1 p.2} : Set _) := by
    rw [← hRelationEq]
    exact hClosed
  exact collapseOpenUnitIntervalRelation_notClosed hRelationClosed

/-- Remark 5.2.13 (1). There exists a point-set colimit in `TopCat` of weak Hausdorff spaces that
is not weak Hausdorff. -/
theorem exists_weaklyHausdorffSpace_colimit_not_weaklyHausdorffSpace :
    ∃ (J : Type u) (_hJ : Category.{v} J) (F : J ⥤ TopCat.{w}) (_hF : HasColimit F),
      (∀ j, WeaklyHausdorffSpace.{w, w} (F.obj j)) ∧
        ¬ WeaklyHausdorffSpace.{w, w} (colimit F : TopCat.{w}) := by
  let X : TopCat.{w} := TopCat.of openUnitIntervalCollapseCarrier
  let S : Setoid openUnitIntervalCollapseCarrier := collapseOpenUnitIntervalSetoid
  let Y : TopCat.{w} := TopCat.of (Quotient S)
  let q : X ⟶ Y := TopCat.ofHom ⟨Quotient.mk', continuous_quotient_mk'⟩
  let baseF : WalkingParallelPair ⥤ TopCat.{w} :=
    parallelPair (TopCat.pullbackFst q q) (TopCat.pullbackSnd q q)
  have hq : Topology.IsQuotientMap q := by
    -- The quotient map is the standard quotient-space projection.
    simpa [q, X, Y, S] using
      (isQuotientMap_quotient_mk' :
        Topology.IsQuotientMap
          (Quotient.mk' : openUnitIntervalCollapseCarrier → Quotient S))
  have hYNot : ¬ WeaklyHausdorffSpace Y := by
    -- The quotient is not weak Hausdorff because the induced relation is not closed.
    simpa [Y, S] using collapseOpenUnitIntervalQuotient_notWeaklyHausdorff
  have hBaseT2 : ∀ j, T2Space (baseF.obj j) := by
    intro j
    cases j
    · simpa [baseF] using
        (inferInstance :
          T2Space (TopCat.of { p : X × X // q p.1 = q p.2 } : TopCat.{w}))
    · simpa [baseF, X] using (inferInstance : T2Space openUnitIntervalCollapseCarrier)
  have hBaseNot : ¬ WeaklyHausdorffSpace (colimit baseF : TopCat.{w}) := by
    have hEffective : EffectiveEpi q := (TopCat.effectiveEpi_iff_isQuotientMap q).2 hq
    let _ : EffectiveEpi q := hEffective
    have hCofork :
        IsColimit (Cofork.ofπ q (TopCat.pullbackCone q q).condition) := by
      -- Quotient maps are effective epimorphisms, hence regular epimorphisms in `TopCat`.
      exact
        CategoryTheory.isColimitCoforkOfEffectiveEpi q
          (TopCat.pullbackCone q q) (TopCat.pullbackConeIsLimit q q)
    let e : Y ≅ colimit baseF :=
      hCofork.coconePointUniqueUpToIso (colimit.isColimit baseF)
    intro hColim
    let _ : WeaklyHausdorffSpace (colimit baseF : TopCat.{w}) := hColim
    have : WeaklyHausdorffSpace Y := by
      -- Route correction: transport weak Hausdorffness through the canonical colimit comparison
      -- homeomorphism instead of unfolding the coequalizer construction directly.
      exact (TopCat.homeoOfIso e).isEmbedding.weaklyHausdorffSpace
    exact hYNot this
  letI : Category.{0} (ULift.{u} WalkingParallelPair) :=
    CategoryTheory.uliftCategory (C := WalkingParallelPair)
  let J : Type u := CategoryTheory.ULiftHom.{v} (ULift.{u} WalkingParallelPair)
  let eIndex : WalkingParallelPair ≌ J :=
    CategoryTheory.ULiftHomULiftCategory.equiv WalkingParallelPair
  let F : J ⥤ TopCat.{w} := eIndex.inverse ⋙ baseF
  let _ : HasColimit F := by
    -- Transport the already-known colimit of the base parallel-pair diagram across the index
    -- equivalence so the witness lives in the requested universes `u` and `v`.
    exact (hasColimit_inverse_equivalence_comp_iff (F := baseF) eIndex).2 inferInstance
  have hIndexIso : eIndex.functor ⋙ F ≅ baseF :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerRight eIndex.unitIso.symm baseF ≪≫
      Functor.leftUnitor baseF
  have hColimIso : colimit baseF ≅ colimit F :=
    HasColimit.isoOfEquivalence eIndex hIndexIso
  have hNot : ¬ WeaklyHausdorffSpace (colimit F : TopCat.{w}) := by
    intro hColim
    let _ : WeaklyHausdorffSpace (colimit F : TopCat.{w}) := hColim
    have : WeaklyHausdorffSpace (colimit baseF : TopCat.{w}) := by
      exact (TopCat.homeoOfIso hColimIso).isEmbedding.weaklyHausdorffSpace
    exact hBaseNot this
  refine ⟨J, inferInstance, F, inferInstance, ?_⟩
  change
    (∀ j, WeaklyHausdorffSpace (F.obj j)) ∧
      ¬ WeaklyHausdorffSpace.{w, w} (colimit F : TopCat.{w})
  refine ⟨?_, hNot⟩
  intro j
  -- Objectwise weak Hausdorffness is inherited from the base parallel-pair diagram.
  let _ : T2Space (F.obj j) := by
    simpa [F] using hBaseT2 (eIndex.inverse.obj j)
  exact inferInstance

/-- Remark 5.2.13 (2). Formalizing the positive clause: if the point-set colimit `colimit F` in
`TopCat` of compactly generated spaces is weak Hausdorff, then it is automatically a `k`-space.
This is the canonical typeclass form of the positive clause. -/
instance instUCompactlyGeneratedSpaceColimitOfWeaklyHausdorff
    {J : Type u} [Category.{v} J] (F : J ⥤ TopCat.{w}) [HasColimit F]
    [∀ j, CompactlyGeneratedWeakHausdorffSpace.{w, w} (F.obj j)]
    [WeaklyHausdorffSpace.{w, w} (colimit F : TopCat.{w})] :
    UCompactlyGeneratedSpace.{w} (colimit F : TopCat.{w}) := by
  let sigmaDesc : (Σ j, F.obj j) → (colimit F : TopCat.{w}) :=
    fun x ↦ colimit.ι F x.1 x.2
  have hSigmaDesc : Continuous sigmaDesc := by
    -- Continuity of the sigma-desc map is equivalent to continuity of each structure map.
    rw [continuous_sigma_iff]
    intro j
    simpa [sigmaDesc] using (colimit.ι F j).hom.continuous
  have hTopology :
      (colimit F).str = TopologicalSpace.coinduced sigmaDesc inferInstance := by
    -- Normalize the colimit topology to a single coinduced topology from the sigma-domain.
    simpa [sigmaDesc] using colimitTopology_eq_coinducedSigmaDesc (F := F)
  let _ : ∀ j, UCompactlyGeneratedSpace.{w} (F.obj j) := by
    intro j
    let h : CompactlyGeneratedWeakHausdorffSpace.{w, w} (F.obj j) := inferInstance
    exact h.toUCompactlyGeneratedSpace
  have hSigma : UCompactlyGeneratedSpace.{w} (Σ j, F.obj j) := by
    -- The sigma of compactly generated spaces is compactly generated.
    refine uCompactlyGeneratedSpace_of_isClosed ?_
    intro s hs
    rw [isClosed_sigma_iff]
    intro j
    exact UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦
      hs S ⟨Sigma.mk j ∘ f, continuous_sigmaMk.comp hf⟩
  let _ : UCompactlyGeneratedSpace.{w} (Σ j, F.obj j) := hSigma
  -- The sigma of compactly generated components is compactly generated, and coinduced quotients
  -- of compactly generated spaces stay compactly generated.
  have hColimCG :
      UCompactlyGeneratedSpace.{w} (colimit F : TopCat.{w}) := by
    exact
      uCompactlyGeneratedSpace_of_coinduced
        (X := Σ j, F.obj j) (Y := (colimit F : TopCat.{w})) hSigmaDesc hTopology
  exact hColimCG

/-- A weak Hausdorff colimit in `TopCat` of compactly generated spaces is compactly generated in
the textbook sense. This is the canonical typeclass form of the stronger conclusion. -/
instance instCompactlyGeneratedWeakHausdorffSpaceColimitOfWeaklyHausdorff
    {J : Type u} [Category.{v} J] (F : J ⥤ TopCat.{w}) [HasColimit F]
    [∀ j, CompactlyGeneratedWeakHausdorffSpace.{w, w} (F.obj j)]
    [hX : WeaklyHausdorffSpace.{w, w} (colimit F : TopCat.{w})] :
    CompactlyGeneratedWeakHausdorffSpace.{w, w} (colimit F : TopCat.{w}) where
  toWeaklyHausdorffSpace := hX
  toUCompactlyGeneratedSpace := instUCompactlyGeneratedSpaceColimitOfWeaklyHausdorff F
