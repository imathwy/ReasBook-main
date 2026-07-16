import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_3
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_4
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Theorem_5_51
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_30.Definition_5_30_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` did not surface a matching regular-domain theorem, so
-- this item follows the local Chapter 5 owners `IsDefiningFunction`,
-- `SmoothManifoldWithBoundary`, and `Set.IsRegularDomain`.

open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]

local notation "dimM" => Module.finrank ℝ E

/-- Helper for Problem 5-21: if each point of `S` already has either a full slice chart or a
boundary slice chart in ambient dimension `dimM`, then `S` satisfies the chapter's local
slice-with-boundary condition. -/
lemma pointwiseSliceOrBoundarySlice_satisfiesLocalSliceConditionWithBoundary
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    {S : Set M}
    (hPointwise :
      ∀ x : M, x ∈ S →
        (∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
          x ∈ e.source ∧ e.IsSliceChart S dimM) ∨
          ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
            x ∈ e.source ∧ e.IsBoundarySliceChart S dimM) :
    Set.SatisfiesLocalSliceConditionWithBoundary dimM S dimM := by
  refine ⟨?_⟩
  intro x hx
  -- Package the pointwise slice-or-boundary-slice alternative into the owner predicate.
  rcases hPointwise x hx with hSlice | hBoundary
  · rcases hSlice with ⟨e, hxSource, he⟩
    exact ⟨e, hxSource, Or.inl he⟩
  · rcases hBoundary with ⟨e, hxSource, he⟩
    exact ⟨e, hxSource, Or.inr he⟩

/-- Helper for Problem 5-21: the shifted product `(u - a) * (u - b)` is nonpositive exactly for
`u ∈ Set.Icc a b` when `a < b`. -/
lemma mulShifted_nonpos_iff_mem_Icc {a b u : ℝ} (hab : a < b) :
    (u - a) * (u - b) ≤ 0 ↔ u ∈ Set.Icc a b := by
  constructor
  · intro hu
    by_cases hua : u ≤ a
    · have hu_eq : u = a := by
        nlinarith [hu, hab]
      subst hu_eq
      exact ⟨le_rfl, hab.le⟩
    · have hau : a < u := lt_of_not_ge hua
      have hub : u ≤ b := by
        nlinarith [hu, hau]
      exact ⟨hau.le, hub⟩
  · rintro ⟨hau, hub⟩
    -- On the closed interval `[a, b]`, the two factors have opposite signs.
    nlinarith

/-- Helper for Problem 5-21: the closed strip `f ⁻¹' Set.Icc a b` is the same as the closed
sublevel set of the auxiliary function `x ↦ (f x - a) * (f x - b)` at level `0`. -/
lemma preimage_Icc_eq_preimage_Iic_mulShifted {f : M → ℝ} {a b : ℝ} (hab : a < b) :
    f ⁻¹' Set.Icc a b =
      (fun x ↦ (f x - a) * (f x - b)) ⁻¹' Set.Iic 0 := by
  ext x
  -- Reduce the set equality to the one-variable inequality from the source proof.
  simp [Set.mem_Iic, mulShifted_nonpos_iff_mem_Icc hab]

/-- Helper for Problem 5-21: in full ambient dimension, the Euclidean slice condition imposes no
tail-coordinate equations, so the slice is exactly the ambient open set. -/
lemma euclideanSlice_full_dimensional_eq
    (U : Set (EuclideanSpace ℝ (Fin dimM))) (hk : dimM ≤ dimM)
    (c : Fin (dimM - dimM) → ℝ) :
    Set.euclideanSlice U dimM hk c = U := by
  -- The defining tail-coordinate equations are vacuous because `Fin (dimM - dimM)` is empty.
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro i
    exact False.elim (by simpa [Nat.sub_self] using i.is_lt)

/-- Helper for Problem 5-21: if an ambient open neighborhood through `x` is already contained in
`S`, then restricting an ambient chart to that neighborhood produces a full slice chart for `S` at
`x`. -/
lemma point_has_fullSliceChart_of_open_subset
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    {S U : Set M} {x : M}
    (hU_open : IsOpen U) (hxU : x ∈ U) (hUS : U ⊆ S) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)),
      x ∈ e.source ∧ e.IsSliceChart S dimM := by
  let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)) :=
    (chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr U
  have hx_source : x ∈ e.source := by
    -- Restrict the ambient chart to the chosen open neighborhood inside `S`.
    change x ∈ ((chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr U).source
    rw [(chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr_source' U hU_open]
    exact ⟨mem_chart_source (EuclideanSpace ℝ (Fin dimM)) x, hxU⟩
  refine ⟨e, hx_source, ?_⟩
  refine ⟨?_, ?_⟩
  · -- Restricting a maximal-atlas chart to an open subset preserves maximal-atlas membership.
    change ((chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr U) ∈
        IsManifold.maximalAtlas (𝓡 dimM) (⊤ : WithTop ℕ∞) M
    exact restr_mem_maximalAtlas
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM))
      (IsManifold.chart_mem_maximalAtlas x)
      hU_open
  · have hsource_subset : e.source ⊆ S := by
      intro y hy
      change y ∈ ((chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr U).source at hy
      rw [(chartAt (EuclideanSpace ℝ (Fin dimM)) x).restr_source' U hU_open] at hy
      exact hUS hy.2
    have hinter : S ∩ e.source = e.source := by
      ext y
      constructor
      · intro hy
        exact hy.2
      · intro hy
        exact ⟨hsource_subset hy, hy⟩
    -- On this restricted source, the subset fills the whole chart patch.
    refine ⟨le_rfl, fun i ↦ False.elim (by simpa [Nat.sub_self] using i.is_lt), ?_⟩
    calc
      e '' (S ∩ e.source) = e '' e.source := by rw [hinter]
      _ = e.target := e.image_source_eq_target
      _ = Set.euclideanSlice e.target dimM le_rfl
            (fun i ↦ False.elim (by simpa [Nat.sub_self] using i.is_lt)) := by
            symm
            exact euclideanSlice_full_dimensional_eq e.target le_rfl
              (fun i ↦ False.elim (by simpa [Nat.sub_self] using i.is_lt))

/-- Helper for Problem 5-21: an ordered basis gives a fixed continuous linear equivalence
`ℝ^dimM ≃L[ℝ] E` for the ambient model space. -/
noncomputable def ambientBasisContinuousLinearEquiv
    (b : Module.Basis (Fin dimM) ℝ E) :
    EuclideanSpace ℝ (Fin dimM) ≃L[ℝ] E :=
  let e : E ≃ₗ[ℝ] Fin dimM → ℝ := b.equivFun
  (EuclideanSpace.equiv (Fin dimM) ℝ).trans e.symm.toContinuousLinearEquiv

/-- Helper for Problem 5-21: the chosen basis identifies the Euclidean ambient model `ℝ^dimM`
with the original model space `E` by a diffeomorphism. -/
noncomputable def ambientBasisDiffeomorph
    (b : Module.Basis (Fin dimM) ℝ E) :
    EuclideanSpace ℝ (Fin dimM) ≃ₘ[ℝ] E :=
  (ambientBasisContinuousLinearEquiv b).toDiffeomorph

/-- Helper for Problem 5-21: the basis identification gives a global Euclidean chart on the model
space `E`. -/
noncomputable def ambientBasisModelChart
    (b : Module.Basis (Fin dimM) ℝ E) :
    OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
  (ambientBasisDiffeomorph b).symm.toHomeomorph.toOpenPartialHomeomorph

/-- Helper for Problem 5-21: at each point, use the ambient extended chart `extChartAt I x` and
then express its Euclidean target using the chosen basis. -/
noncomputable def ambientBasisChart
    (b : Module.Basis (Fin dimM) ℝ E) (x : M) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin dimM)) :=
  (extChartAt I x).trans (ambientBasisModelChart b)

/-- Helper for Problem 5-21: the temporary Euclidean chart centered at `x` is defined at `x`. -/
lemma ambientBasisChart_mem_source
    (b : Module.Basis (Fin dimM) ℝ E) :
    ∀ x : M, x ∈ (ambientBasisChart b x).source := by
  intro x
  -- The basis model chart is global, so only the original chart source matters.
  change x ∈ ((extChartAt I x).trans (ambientBasisModelChart b)).source
  simp [ambientBasisChart, ambientBasisModelChart, mem_extChartAt_source]

/-- Helper for Problem 5-21: each temporary Euclidean chart belongs to the temporary atlas by
construction. -/
lemma ambientBasisChart_mem_atlas
    (b : Module.Basis (Fin dimM) ℝ E) :
    ∀ x : M, ambientBasisChart b x ∈ Set.range (ambientBasisChart b) := by
  intro x
  exact ⟨x, rfl⟩

/-- Helper for Problem 5-21: use the extended ambient `I`-charts, expressed in a fixed basis of
`E`, as a temporary Euclidean charted-space structure on `M`. -/
noncomputable abbrev ambientBasisChartedSpace
    (b : Module.Basis (Fin dimM) ℝ E) :
    ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
  { atlas := Set.range (ambientBasisChart b)
    chartAt := ambientBasisChart b
    mem_chart_source := ambientBasisChart_mem_source b
    chart_mem_atlas := ambientBasisChart_mem_atlas b }

/-- Helper for Problem 5-21: the temporary Euclidean charted space on `M` is automatically a
topological manifold once the transported charts are installed. -/
noncomputable abbrev ambientBasisTopologicalManifold
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M := ambientBasisChartedSpace b
    TopologicalManifold dimM M :=
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M := ambientBasisChartedSpace b
  topologicalManifoldOfChartedSpace dimM M

/-- Helper for Problem 5-21: transporting an `I`-smooth extended coordinate change through the
fixed basis chart yields a Euclidean-smooth chart transition. -/
lemma ambientBasisTransition_mem_contDiffGroupoid
    (b : Module.Basis (Fin dimM) ℝ E)
    (x y : M) :
    let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
      ambientBasisModelChart b
    ((ambientBasisChart b x).symm.trans (ambientBasisChart b y)) ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM) := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin dimM)) :=
    ambientBasisModelChart b
  let eChange : OpenPartialHomeomorph E E := (extChartAt I x).symm.trans (extChartAt I y)
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  have hChange :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) eChange eChange.source := by
    -- The middle transition is exactly the extended `I`-coordinate change.
    simpa [eChange, ModelWithCorners.extendCoordChange] using
      I.contDiffOn_extendCoordChange
        (IsManifold.chart_mem_maximalAtlas x)
        (IsManifold.chart_mem_maximalAtlas y)
  have hChangeSymm :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) eChange.symm eChange.target := by
    -- The inverse transition is the reversed extended `I`-coordinate change.
    simpa [eChange, ModelWithCorners.extendCoordChange] using
      I.contDiffOn_extendCoordChange_symm
        (IsManifold.chart_mem_maximalAtlas x)
        (IsManifold.chart_mem_maximalAtlas y)
  have heModel_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞) (eModel : E → EuclideanSpace ℝ (Fin dimM)) := by
    -- The basis model chart is the inverse of a fixed continuous linear equivalence.
    simpa [eModel, ambientBasisModelChart, ambientBasisDiffeomorph,
      ambientBasisContinuousLinearEquiv] using
      (ambientBasisContinuousLinearEquiv b).symm.toContinuousLinearMap.contDiff
  have heModel_symm_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞) (eModel.symm : EuclideanSpace ℝ (Fin dimM) → E) := by
    -- Its inverse is the original continuous linear equivalence.
    simpa [eModel, ambientBasisModelChart, ambientBasisDiffeomorph,
      ambientBasisContinuousLinearEquiv] using
      (ambientBasisContinuousLinearEquiv b).toContinuousLinearMap.contDiff
  have hsource :
      eModel.symm ⁻¹' eChange.source = ((ambientBasisChart b x).symm.trans (ambientBasisChart b y)).source := by
    -- The global basis chart only changes notation for the model-space source.
    ext z
    simp [ambientBasisChart, eModel, eChange]
  have htarget :
      eModel.symm ⁻¹' eChange.target = ((ambientBasisChart b x).symm.trans (ambientBasisChart b y)).target := by
    -- The same simplification holds for the transported target.
    ext z
    simp [ambientBasisChart, eModel, eChange]
  constructor
  · -- Compose the `I`-smooth extended coordinate change with the fixed Euclidean basis changes.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ eChange (eModel.symm x))
          (eModel.symm ⁻¹' eChange.source) := by
      refine hChange.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ eModel (eChange (eModel.symm x)))
          (eModel.symm ⁻¹' eChange.source) := by
      refine (heModel_contDiff.contDiffOn : ContDiffOn ℝ (⊤ : WithTop ℕ∞) eModel Set.univ).comp
        hmid ?_
      intro x hx
      simp [Set.mem_univ, eModel]
    simpa [hsource, ambientBasisChart, eModel, eChange, Function.comp,
      OpenPartialHomeomorph.trans_source] using
      hfinal
  · -- The inverse transition is handled by the same conjugation argument.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ eChange.symm (eModel.symm x))
          (eModel.symm ⁻¹' eChange.target) := by
      refine hChangeSymm.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin dimM) ↦ eModel (eChange.symm (eModel.symm x)))
          (eModel.symm ⁻¹' eChange.target) := by
      refine (heModel_contDiff.contDiffOn : ContDiffOn ℝ (⊤ : WithTop ℕ∞) eModel Set.univ).comp
        hmid ?_
      intro x hx
      simp [Set.mem_univ, eModel]
    simpa [htarget, ambientBasisChart, eModel, eChange, Function.comp,
      OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc] using
      hfinal

/-- Helper for Problem 5-21: after transporting every extended `I`-chart through a fixed basis of
`E`, the manifold `M` carries the expected Euclidean ambient smooth structure. -/
lemma ambientBasisIsManifold
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      ambientBasisChartedSpace b
    IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
    ambientBasisChartedSpace b
  have hGroupoid : HasGroupoid M (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM)) := by
    refine ⟨?_⟩
    intro c c' hc hc'
    rcases hc with ⟨x, rfl⟩
    rcases hc' with ⟨y, rfl⟩
    -- Compatibility of temporary charts is exactly compatibility of extended `I`-coordinate
    -- changes, rewritten in the fixed Euclidean basis.
    simpa [ambientBasisChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using
      ambientBasisTransition_mem_contDiffGroupoid (I := I) b x y
  let _ : HasGroupoid M (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 dimM)) := hGroupoid
  exact IsManifold.mk' (𝓡 dimM) (⊤ : WithTop ℕ∞) M

/-- Helper for Problem 5-21: the regular closed sublevel set should satisfy the local
slice-with-boundary condition in ambient dimension `dimM`. -/
-- TODO: build full slice charts at points with `f x < b`, half-slice charts at points with
-- `f x = b`, and then package those pointwise witnesses with
-- `pointwiseSliceOrBoundarySlice_satisfiesLocalSliceConditionWithBoundary`.
lemma regularSublevel_satisfiesLocalSliceConditionWithBoundary
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hb : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f b) :
    Set.SatisfiesLocalSliceConditionWithBoundary dimM (f ⁻¹' Set.Iic b) dimM := by
  -- Split the pointwise chart construction into the strict-sublevel and boundary-fiber branches.
  refine pointwiseSliceOrBoundarySlice_satisfiesLocalSliceConditionWithBoundary ?_
  intro x hx
  by_cases hlt : f x < b
  · -- TODO: on a neighborhood where `f < b`, the sublevel set is locally the whole chart patch,
    -- so this branch supplies a full slice chart by restricting an ambient chart to `{f < b}`.
    have hOpenLt : IsOpen (f ⁻¹' Set.Iio b) := isOpen_Iio.preimage hf.continuous
    have hxOpenLt : x ∈ f ⁻¹' Set.Iio b := by
      simpa [Set.mem_preimage, Set.mem_Iio] using hlt
    have hLtSubset :
        f ⁻¹' Set.Iio b ⊆ f ⁻¹' Set.Iic b := by
      intro y hy
      exact (show f y ≤ b from (show f y < b from hy).le)
    rcases point_has_fullSliceChart_of_open_subset (E := E) (M := M)
        (S := f ⁻¹' Set.Iic b) (U := f ⁻¹' Set.Iio b) hOpenLt hxOpenLt hLtSubset with
      ⟨e, hxSource, he⟩
    exact Or.inl ⟨e, hxSource, he⟩
  · have hEq : f x = b := by
      have hle : f x ≤ b := by simpa [Set.mem_preimage, Set.mem_Iic] using hx
      linarith
    -- TODO: at a boundary point `f x = b`, regularity of `b` should give a local submersion
    -- normal form whose sublevel image is a Euclidean half-slice.
    let _ := hf
    let _ := hb
    let _ := hEq
    sorry

/-- Helper for Problem 5-21: subtracting a constant does not change the manifold derivative. -/
lemma mfderiv_sub_const {f : M → ℝ} {c : ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (mfderiv% (f - fun _ : M ↦ c) x : TangentSpace I x →L[ℝ] ℝ) = mfderiv% f x := by
  have hfDiffAt : MDiffAt f x :=
    hf.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hconstDiffAt : MDiffAt (fun _ : M ↦ c) x := mdifferentiableAt_const
  -- Subtracting a constant only contributes the zero linear map to the derivative.
  rw [mfderiv_sub hfDiffAt hconstDiffAt]
  have hconst :
      (mfderiv% (fun _ : M ↦ c) x : TangentSpace I x →L[ℝ] ℝ) = 0 := by
    simpa using
      (mfderiv_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := c) (x := x) :
        mfderiv% (fun _ : M ↦ c) x =
          (0 : TangentSpace I x →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) c))
  rw [hconst]
  ext v
  change (mfderiv% f x) v - 0 = (mfderiv% f x) v
  simp

/-- Helper for Problem 5-21: translating the target by a real constant preserves regular values. -/
lemma isRegularValue_sub_const_zero_iff {f : M → ℝ} {c : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Manifold.IsRegularValue I 𝓘(ℝ, ℝ) (fun x ↦ f x - c) 0 ↔
      Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f c := by
  rw [Manifold.isRegularValue_iff_forall_isRegularPoint,
    Manifold.isRegularValue_iff_forall_isRegularPoint]
  constructor
  · intro h x hx
    have hShiftPoint :
        Manifold.IsRegularPoint I 𝓘(ℝ, ℝ) (fun y ↦ f y - c) x := by
      -- Rewrite the shifted fiber equation to move the regular-point witness to level `0`.
      exact h x (by simpa [hx])
    have hShiftSurj :
        Function.Surjective
          (mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ f y - c) x) := by
      exact
        (Manifold.isRegularPoint_iff_surjective_mfderiv
          (I := I) (J := 𝓘(ℝ, ℝ)) (Φ := fun y ↦ f y - c) (p := x)).1 hShiftPoint
    change Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) (f - fun _ : M ↦ c) x) at hShiftSurj
    rw [mfderiv_sub_const (hf := hf) (c := c) (x := x)] at hShiftSurj
    -- The shifted derivative is definitionally the same linear map as the original derivative.
    exact
      (Manifold.isRegularPoint_iff_surjective_mfderiv
        (I := I) (J := 𝓘(ℝ, ℝ)) (Φ := f) (p := x)).2 hShiftSurj
  · intro h x hx
    have hPoint :
        Manifold.IsRegularPoint I 𝓘(ℝ, ℝ) f x := by
      -- The zero fiber of the shifted function is the `c`-fiber of `f`.
      exact h x (by linarith)
    have hSurj : Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) f x) := by
      exact
        (Manifold.isRegularPoint_iff_surjective_mfderiv
          (I := I) (J := 𝓘(ℝ, ℝ)) (Φ := f) (p := x)).1 hPoint
    have hShiftSurj :
        Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ f y - c) x) := by
      change Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) (f - fun _ : M ↦ c) x)
      simpa [mfderiv_sub_const (hf := hf) (c := c) (x := x)] using hSurj
    -- Reuse the derivative-identification lemma in the reverse direction.
    exact
      (Manifold.isRegularPoint_iff_surjective_mfderiv
        (I := I) (J := 𝓘(ℝ, ℝ)) (Φ := fun y ↦ f y - c) (p := x)).2 hShiftSurj

/-- Helper for Problem 5-21: multiplying a surjective linear functional by a nonzero scalar keeps
it surjective. -/
lemma surjective_smul_mfderiv {x : M}
    {L : TangentSpace I x →L[ℝ] ℝ} {c : ℝ}
    (hL : Function.Surjective L) (hc : c ≠ 0) :
    Function.Surjective (c • L) := by
  intro y
  -- Pull back `y / c` along `L`, then rescale back to `y`.
  rcases hL (y / c) with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  rw [ContinuousLinearMap.smul_apply, hv]
  have hmul : c * (y / c) = y := by
    field_simp [hc]
  simpa [smul_eq_mul] using hmul

/-- Helper for Problem 5-21: if `a < b` are regular values of `f`, then `0` is a regular value of
`x ↦ (f x - a) * (f x - b)`. -/
lemma isRegularValue_zero_of_mulShifted {f : M → ℝ} {a b : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (ha : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f a)
    (hb : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f b) (hab : a < b) :
    Manifold.IsRegularValue I 𝓘(ℝ, ℝ)
      (fun x ↦ (f x - a) * (f x - b)) 0 := by
  rw [Manifold.isRegularValue_iff_forall_isRegularPoint]
  intro x hx
  have hZeroFactor : f x = a ∨ f x = b := by
    -- A zero of the product lies on one of the two regular fibers.
    have hProdZero : (f x - a) * (f x - b) = 0 := by simpa using hx
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hProdZero with hxa | hxb
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hShiftADiff : MDiffAt (fun y ↦ f y - a) x :=
    (hf.sub contMDiff_const).contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hShiftBDiff : MDiffAt (fun y ↦ f y - b) x :=
    (hf.sub contMDiff_const).contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hShiftAHas :
      HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y ↦ f y - a) x (mfderiv I 𝓘(ℝ, ℝ) f x) := by
    -- Rewrite the shifted derivative onto the common codomain `ℝ` before multiplying.
    exact hShiftADiff.hasMFDerivAt.congr_mfderiv (mfderiv_sub_const (hf := hf) (c := a) (x := x))
  have hShiftBHas :
      HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y ↦ f y - b) x (mfderiv I 𝓘(ℝ, ℝ) f x) := by
    -- The same normalization removes the target-tangent mismatch for the second factor.
    exact hShiftBDiff.hasMFDerivAt.congr_mfderiv (mfderiv_sub_const (hf := hf) (c := b) (x := x))
  have hProdDeriv :
      mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ (f y - a) * (f y - b)) x =
        (f x - a) • mfderiv I 𝓘(ℝ, ℝ) f x +
          (f x - b) • mfderiv I 𝓘(ℝ, ℝ) f x := by
    -- Differentiate the product after normalizing both factor derivatives to `mfderiv f x`.
    simpa using (hShiftAHas.mul hShiftBHas).mfderiv
  rcases hZeroFactor with hxa | hxb
  · have hSurjF : Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) f x) := by
      -- Regularity at the `a`-fiber gives surjectivity of `mfderiv f x`.
      exact
        (Manifold.isRegularPoint_iff_surjective_mfderiv
          (I := I) (J := 𝓘(ℝ, ℝ)) (Φ := f) (p := x)).1 <|
          (Manifold.isRegularValue_iff_forall_isRegularPoint
            (I := I) (J := 𝓘(ℝ, ℝ)) (Φ := f) (c := a)).1 ha x hxa
    have hAuxSurj :
        Function.Surjective
          (mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ (f y - a) * (f y - b)) x) := by
      -- On the `a`-fiber, the product derivative collapses to `(a - b) • df`.
      rw [hProdDeriv]
      simpa [hxa, add_smul] using
        surjective_smul_mfderiv (x := x)
          (L := mfderiv I 𝓘(ℝ, ℝ) f x) hSurjF
          (by linarith : (a - b : ℝ) ≠ 0)
    exact
      (Manifold.isRegularPoint_iff_surjective_mfderiv
        (I := I) (J := 𝓘(ℝ, ℝ)) (Φ := fun y ↦ (f y - a) * (f y - b)) (p := x)).2 hAuxSurj
  · have hSurjF : Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) f x) := by
      -- Regularity at the `b`-fiber gives surjectivity of `mfderiv f x`.
      exact
        (Manifold.isRegularPoint_iff_surjective_mfderiv
          (I := I) (J := 𝓘(ℝ, ℝ)) (Φ := f) (p := x)).1 <|
          (Manifold.isRegularValue_iff_forall_isRegularPoint
            (I := I) (J := 𝓘(ℝ, ℝ)) (Φ := f) (c := b)).1 hb x hxb
    have hAuxSurj :
        Function.Surjective
          (mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ (f y - a) * (f y - b)) x) := by
      -- On the `b`-fiber, the product derivative collapses to `(b - a) • df`.
      rw [hProdDeriv]
      simpa [hxb, add_smul, add_comm] using
        surjective_smul_mfderiv (x := x)
          (L := mfderiv I 𝓘(ℝ, ℝ) f x) hSurjF
          (by linarith : (b - a : ℝ) ≠ 0)
    exact
      (Manifold.isRegularPoint_iff_surjective_mfderiv
        (I := I) (J := 𝓘(ℝ, ℝ)) (Φ := fun y ↦ (f y - a) * (f y - b)) (p := x)).2 hAuxSurj

/-- Helper for Problem 5-21: once the local slice-with-boundary criterion is available in a
temporary Euclidean ambient structure, the regular closed sublevel set already carries the
canonical codimension-`0` regular-domain structure for that Euclidean ambient model. -/
lemma regularSublevel_preimage_exists_regularDomain_euclideanAmbient
    [ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M]
    [IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M]
    {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hb : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f b) :
    let D : Set M := f ⁻¹' Set.Iic b
    ∃ hSmooth : SmoothManifoldWithBoundary dimM D,
      letI : SmoothManifoldWithBoundary dimM D := hSmooth
      letI :
          SmoothManifoldWithBoundary
            (Module.finrank ℝ (EuclideanSpace ℝ (Fin dimM))) D := by
          simpa using hSmooth
      Set.IsRegularDomain (𝓡 dimM) D := by
  let D : Set M := f ⁻¹' Set.Iic b
  have hSlice :
      Set.SatisfiesLocalSliceConditionWithBoundary dimM D dimM := by
    -- The local slice-with-boundary condition is the only geometric input needed for Theorem 5.51.
    simpa [D] using
      regularSublevel_satisfiesLocalSliceConditionWithBoundary
        (I := I) (M := M) hf hb
  let _ : TopologicalManifold dimM M := topologicalManifoldOfChartedSpace dimM M
  rcases
      satisfiesLocalSliceConditionWithBoundary_has_manifold_with_boundary_structure
        dimM D hSlice with
    ⟨hSmooth, hSubtype⟩
  refine ⟨hSmooth, ?_⟩
  letI : SmoothManifoldWithBoundary dimM D := hSmooth
  letI :
      SmoothManifoldWithBoundary
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin dimM))) D := by
    simpa using hSmooth
  refine
    { isSmoothEmbedding_subtype_val := ?_
      isProperlyEmbedded := ?_ }
  · -- Theorem 5.51 already gives the Euclidean-ambient subtype embedding.
    simpa using hSubtype
  · -- Proper embeddedness is purely topological, so closedness of the sublevel set is enough.
    have hClosed : IsClosed D := by
      simpa [D] using isClosed_Iic.preimage hf.continuous
    exact hClosed.isProperlyEmbedded

/-- Helper for Problem 5-21: once the temporary Euclidean ambient structure is installed on `M`,
the identity map back to the original ambient model `I` should be a smooth embedding. -/
-- Route correction: the final remaining transport step is to prove that the temporary Euclidean
-- chart structure and the original `I`-chart structure are related by a smooth identity map.
lemma ambientId_isSmoothEmbedding
    (b : Module.Basis (Fin dimM) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
      ambientBasisChartedSpace b
    let _ : TopologicalManifold dimM M :=
      ambientBasisTopologicalManifold b
    let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold b
    Manifold.IsSmoothEmbedding (𝓡 dimM) I (⊤ : WithTop ℕ∞) (id : M → M) := by
  -- TODO: in the temporary Euclidean charts, the identity map is written as the inverse basis
  -- chart `ambientBasisModelChart b).symm`; prove its immersion field pointwise and combine it
  -- with `Topology.IsEmbedding.id`.
  sorry

/-- Problem 5-21 (1): for a smooth function `f : M → ℝ`, the closed sublevel set
`f ⁻¹' Set.Iic b` of any regular value `b` admits a smooth manifold-with-boundary structure making
it a regular domain in `M`. -/
theorem regularSublevel_preimage_exists_regularDomain {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hb : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f b) :
    let D : Set M := f ⁻¹' Set.Iic b
    ∃ hSmooth : SmoothManifoldWithBoundary dimM D,
      letI : SmoothManifoldWithBoundary dimM D := hSmooth
      Set.IsRegularDomain I D := by
  -- Route correction: the Euclidean-ambient packaging step is now isolated in
  -- `regularSublevel_preimage_exists_regularDomain_euclideanAmbient`; the remaining blocker is
  -- to install the temporary Euclidean ambient structure on `M` and transport the resulting
  -- subtype embedding from target `(𝓡 dimM)` back to the original ambient model `I`.
  let D : Set M := f ⁻¹' Set.Iic b
  have hClosed : IsClosed D := by
    -- Closedness of the sublevel set is independent of the remaining manifold-transport work.
    simpa [D] using isClosed_Iic.preimage hf.continuous
  let bE : Module.Basis (Fin dimM) ℝ E := Module.finBasis ℝ E
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin dimM)) M :=
    ambientBasisChartedSpace bE
  let _ : TopologicalManifold dimM M := ambientBasisTopologicalManifold bE
  let _ : IsManifold (𝓡 dimM) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold bE
  rcases
      regularSublevel_preimage_exists_regularDomain_euclideanAmbient
        (I := I) (M := M) hf hb with
    ⟨hSmooth, hRegularEuclid⟩
  refine ⟨hSmooth, ?_⟩
  letI : SmoothManifoldWithBoundary dimM D := hSmooth
  refine
    { isSmoothEmbedding_subtype_val := ?_
      isProperlyEmbedded := hClosed.isProperlyEmbedded }
  · have hAmbientId :
        Manifold.IsSmoothEmbedding (𝓡 dimM) I (⊤ : WithTop ℕ∞) (id : M → M) := by
      simpa [bE] using ambientId_isSmoothEmbedding bE
    have hSubtype :
        Manifold.IsSmoothEmbedding
          (leeBoundaryModelWithCorners dimM)
          (𝓡 dimM)
          (⊤ : WithTop ℕ∞)
          (Subtype.val : D → M) := by
      simpa using hRegularEuclid.isSmoothEmbedding_subtype_val
    -- Compose the Euclidean-ambient inclusion with the ambient identity embedding.
    simpa [Function.comp] using Manifold.IsSmoothEmbedding.comp hAmbientId hSubtype

/-- Problem 5-21 (2): for a smooth function `f : M → ℝ`, if `a < b` are regular values of `f`,
then the closed strip `f ⁻¹' Set.Icc a b` admits a smooth manifold-with-boundary structure making
it a regular domain in `M`. -/
theorem regularClosedInterval_preimage_exists_regularDomain {f : M → ℝ} {a b : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (ha : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f a)
    (hb : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f b) (hab : a < b) :
    let D : Set M := f ⁻¹' Set.Icc a b
    ∃ hSmooth : SmoothManifoldWithBoundary dimM D,
      letI : SmoothManifoldWithBoundary dimM D := hSmooth
      Set.IsRegularDomain I D := by
  dsimp
  let g : M → ℝ := fun x ↦ (f x - a) * (f x - b)
  have hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := by
    -- The auxiliary function is obtained from `f` by smooth scalar shifts and multiplication.
    exact (hf.sub contMDiff_const).mul (hf.sub contMDiff_const)
  have hzero : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) g 0 :=
    isRegularValue_zero_of_mulShifted hf ha hb hab
  have hD : f ⁻¹' Set.Icc a b = g ⁻¹' Set.Iic 0 := by
    -- Rewrite the strip as the closed sublevel set of the auxiliary function.
    simpa [g] using preimage_Icc_eq_preimage_Iic_mulShifted (f := f) hab
  -- After identifying the strip with a single sublevel set, reuse the first theorem verbatim.
  rw [hD]
  simpa [g] using
    (regularSublevel_preimage_exists_regularDomain (f := g) (b := 0) hg hzero)
