import Mathlib
import DifferentialForms_Cartan_1970.VI.section26.«0002_Definition_VI_5_extra_2»

open scoped Manifold
open Topology Filter
open Path.Homotopic.Quotient

/- Domain sampling: the primary domain here is connected one-dimensional complex manifolds together
with unramified covering surfaces over them. The relevant declarations inspected before this
refinement were:
* the chapter-local primitive owner `UnramifiedSurfaceOver` in
  `cartan/VI/section26/0002_Definition_VI_5_extra_2.lean`, which records the topological
  local-homeomorphism data over a base;
* the source-facing refinement `ConnectedHausdorffUnramifiedSurfaceOver` in the same file, which
  adds the connected Hausdorff hypotheses required by the theorem;
* the bridge `ConnectedHausdorffUnramifiedSurfaceOver.toRiemannSurfaceOver`, showing that
  `RiemannSurfaceOver` is downstream derived API rather than the primitive owner for the universal
  covering theorem itself;
* mathlib's owner theorem `IsCoveringMap.isLocalHomeomorph`, which places the covering property at
  the same topological owner level.
Source/core/bridge triage: this theorem is `source-facing`, so its main existential object should
be the unramified-covering owner `ConnectedHausdorffUnramifiedSurfaceOver Y`. The
`RiemannSurfaceOver` package is a `bridge/view` layer available afterwards when one wants the
induced complex-analytic surface structure. Primitive data is therefore the unramified-surface
owner and the simply connectedness, covering, and surjectivity properties of its projection. -/

-- Declarations for this item will be appended below by the statement pipeline.

universe uY

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: the complex line has a basis of
contractible metric-ball neighborhoods, so it is strongly locally contractible. -/
instance complexStronglyLocallyContractible : StronglyLocallyContractibleSpace ℂ := by
  refine StronglyLocallyContractibleSpace.of_bases
    (p := fun z r => 0 < r) (s := fun z r => Metric.ball z r) ?_ ?_
  · -- Metric balls form the standard neighborhood basis in the model space `ℂ`.
    intro z
    simpa using (Metric.nhds_basis_ball : (nhds z).HasBasis (fun r : ℝ => 0 < r) (Metric.ball z))
  · -- Every complex ball is convex, hence contractible.
    intro z r hr
    simpa using (Metric.contractibleSpace_ball (x := z) (r := r) hr)

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: once local path connectedness is
transported from the model space, connectedness upgrades the manifold to path connectedness. -/
theorem connectedComplexManifold_pathConnected
    {Y : Type uY} [TopologicalSpace Y] [ChartedSpace ℂ Y] [ConnectedSpace Y] :
    PathConnectedSpace Y := by
  letI : LocPathConnectedSpace Y := ChartedSpace.locPathConnectedSpace ℂ Y
  -- Connected locally path-connected spaces are path connected.
  exact PathConnectedSpace.of_locPathConnectedSpace

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: every point of a complex manifold has
an open contractible chart neighborhood, obtained by pulling back a small complex ball through the
chart at that point. -/
lemma contractibleChartNeighborhood
    {Y : Type uY} [TopologicalSpace Y] [ChartedSpace ℂ Y] (y : Y) :
    ∃ U : Set Y, y ∈ U ∧ IsOpen U ∧ ContractibleSpace U := by
  let e := chartAt ℂ y
  rcases Metric.mem_nhds_iff.mp (chart_target_mem_nhds ℂ y) with ⟨r, hrpos, hrsubset⟩
  let V : Set ℂ := Metric.ball (e y) r
  let U : Set Y := e.symm '' V
  refine ⟨U, ?_, ?_, ?_⟩
  · -- The chart center lies in the chosen ball, so it pulls back to the base point.
    refine ⟨e y, Metric.mem_ball_self hrpos, ?_⟩
    simp [e, mem_chart_source]
  · -- Pulling back an open target ball through the inverse chart preserves openness.
    exact (e.isOpen_symm_image_iff_of_subset_target hrsubset).2 Metric.isOpen_ball
  · -- The inverse chart identifies the pulled-back neighborhood with the complex ball.
    let hVU : V ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hrsubset rfl
    letI : ContractibleSpace V := by
      simpa [V] using (Metric.contractibleSpace_ball (x := e y) (r := r) hrpos)
    exact hVU.symm.contractibleSpace

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: every open neighborhood in a complex
manifold contains a smaller open contractible chart neighborhood around the same point. -/
lemma contractibleChartNeighborhoodWithin
    {Y : Type uY} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {y : Y} {s : Set Y} (hs : IsOpen s) (hy : y ∈ s) :
    ∃ U : Set Y, y ∈ U ∧ U ⊆ s ∧ IsOpen U ∧ ContractibleSpace U := by
  let e := chartAt ℂ y
  let S : Set Y := s ∩ e.source
  have hyS : y ∈ S := ⟨hy, mem_chart_source ℂ y⟩
  have hopenImage : IsOpen (e '' S) :=
    e.isOpen_image_of_subset_source (hs.inter e.open_source) (fun _ hz ↦ hz.2)
  have himage : e '' S ∈ nhds (e y) := hopenImage.mem_nhds ⟨y, hyS, rfl⟩
  have htarget : e.target ∈ nhds (e y) := by
    simpa [e] using chart_target_mem_nhds ℂ y
  -- Intersect the chart target with the prescribed neighborhood image to get a small ball.
  have hinter : e.target ∩ e '' S ∈ nhds (e y) := inter_mem htarget himage
  rcases Metric.mem_nhds_iff.mp hinter with ⟨r, hr, hball⟩
  let V : Set ℂ := Metric.ball (e y) r
  let U : Set Y := e.symm '' V
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · -- The chart center maps back to the original point.
    exact ⟨e y, Metric.mem_ball_self hr, by simp [e, mem_chart_source]⟩
  · -- The pulled-back ball lies inside the requested neighborhood by construction.
    intro z hz
    rcases hz with ⟨w, hwV, rfl⟩
    have hw : w ∈ e.target ∩ e '' S := hball hwV
    rcases hw.2 with ⟨z', hz'S, hz'eq⟩
    have hsymm : e.symm w = z' := by
      simpa [hz'eq] using e.left_inv hz'S.2
    simpa [hsymm] using hz'S.1
  · -- Openness again comes from the inverse chart on the target ball.
    exact (e.isOpen_symm_image_iff_of_subset_target (fun z hz ↦ (hball hz).1)).2
      Metric.isOpen_ball
  · -- The inverse chart identifies the neighborhood with a contractible complex ball.
    let hVU : V ≃ₜ U := e.symm.homeomorphOfImageSubsetSource (fun z hz ↦ (hball hz).1) rfl
    letI : ContractibleSpace V := by
      simpa [V] using (Metric.contractibleSpace_ball (x := e y) (r := r) hr)
    exact hVU.symm.contractibleSpace

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: a contractible neighborhood determines
the canonical path-homotopy class between any two of its points after inclusion into the ambient
manifold. -/
noncomputable def localPathClass
    {Y : Type uY} [TopologicalSpace Y] (U : Set Y) [ContractibleSpace U]
    {c z : Y} (hc : c ∈ U) (hz : z ∈ U) : Path.Homotopic.Quotient c z :=
  (mk (PathConnectedSpace.somePath (⟨c, hc⟩ : U) ⟨z, hz⟩)).map
    ⟨Subtype.val, continuous_subtype_val⟩

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: the local path class at a point is the
constant path class. -/
lemma localPathClass_refl
    {Y : Type uY} [TopologicalSpace Y] (U : Set Y) [ContractibleSpace U]
    {c : Y} (hc : c ∈ U) :
    localPathClass U hc hc = Path.Homotopic.Quotient.refl c := by
  letI : SimplyConnectedSpace U := SimplyConnectedSpace.ofContractible U
  have hq :
      mk (PathConnectedSpace.somePath (⟨c, hc⟩ : U) ⟨c, hc⟩) =
        Path.Homotopic.Quotient.refl (⟨c, hc⟩ : U) := by
    exact Subsingleton.elim _ _
  -- Map the unique local path class in the subtype back to the ambient manifold.
  simpa [localPathClass] using congrArg
    (fun q : Path.Homotopic.Quotient (⟨c, hc⟩ : U) ⟨c, hc⟩ =>
      q.map ⟨Subtype.val, continuous_subtype_val⟩) hq

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: any path inside a contractible subtype
represents the canonical local path class after inclusion into the ambient manifold. -/
lemma subtypePathClass_eq_localPathClass
    {Y : Type uY} [TopologicalSpace Y] (U : Set Y) [ContractibleSpace U]
    {c z : Y} (hc : c ∈ U) (hz : z ∈ U)
    (p : Path (⟨c, hc⟩ : U) ⟨z, hz⟩) :
    (mk p).map ⟨Subtype.val, continuous_subtype_val⟩ = localPathClass U hc hz := by
  letI : SimplyConnectedSpace U := SimplyConnectedSpace.ofContractible U
  have hq :
      mk p = mk (PathConnectedSpace.somePath (⟨c, hc⟩ : U) ⟨z, hz⟩) := by
    exact Subsingleton.elim _ _
  -- Contractibility makes every path class in the subtype collapse to the same canonical one.
  simpa [localPathClass] using congrArg
    (fun q : Path.Homotopic.Quotient (⟨c, hc⟩ : U) ⟨z, hz⟩ =>
      q.map ⟨Subtype.val, continuous_subtype_val⟩) hq

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: if a path stays inside a contractible
neighborhood, then its ambient path class is exactly the canonical local path class of that
neighborhood. -/
lemma localPathClass_eq_mk
    {Y : Type uY} [TopologicalSpace Y] (U : Set Y) [ContractibleSpace U]
    {x z : Y} (hx : x ∈ U) (γ : Path x z) (hγ : ∀ t, γ t ∈ U) :
    localPathClass U hx (γ.target ▸ hγ 1) = Path.Homotopic.Quotient.mk γ := by
  let hz : z ∈ U := γ.target ▸ hγ 1
  let γU : Path (⟨x, hx⟩ : U) ⟨z, hz⟩ :=
    { toContinuousMap := ⟨fun t ↦ ⟨γ t, hγ t⟩, γ.continuous.subtype_mk hγ⟩
      source' := by
        simp
      target' := by
        ext
        exact γ.target }
  -- Realize the canonical local class by the given path, viewed inside the contractible subtype.
  rw [← subtypePathClass_eq_localPathClass U hx hz γU]
  rw [← Path.Homotopic.Quotient.mk_map]
  rfl

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: shrinking a contractible neighborhood
does not change the ambient canonical path class between points of the smaller neighborhood. -/
lemma localPathClass_subset
    {Y : Type uY} [TopologicalSpace Y] {U W : Set Y}
    [ContractibleSpace U] [ContractibleSpace W] (hWU : W ⊆ U)
    {x z : Y} (hx : x ∈ W) (hz : z ∈ W) :
    localPathClass W hx hz = localPathClass U (hWU hx) (hWU hz) := by
  let iWU : C(W, U) := ⟨fun q ↦ ⟨q.1, hWU q.2⟩, by continuity⟩
  let pW : Path (⟨x, hx⟩ : W) ⟨z, hz⟩ := PathConnectedSpace.somePath _ _
  let pU : Path (⟨x, hWU hx⟩ : U) ⟨z, hWU hz⟩ := pW.map iWU.continuous
  have hpW : localPathClass W hx hz = (mk pU).map ⟨Subtype.val, continuous_subtype_val⟩ := by
    change (mk pW).map ⟨Subtype.val, continuous_subtype_val⟩ = _
    -- Re-express the smaller-subtype path as a path in the larger subtype before forgetting to `Y`.
    rw [← mk_map]
    rfl
  rw [hpW]
  -- Once viewed inside the larger contractible subtype, the class is again canonical.
  exact subtypePathClass_eq_localPathClass U (hWU hx) (hWU hz) pU

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: canonical local path classes compose
through an intermediate point of the same contractible neighborhood. -/
lemma localPathClass_trans
    {Y : Type uY} [TopologicalSpace Y] (U : Set Y) [ContractibleSpace U]
    {c x z : Y} (hc : c ∈ U) (hx : x ∈ U) (hz : z ∈ U) :
    (localPathClass U hc hx).trans (localPathClass U hx hz) = localPathClass U hc hz := by
  let f : C(U, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let p : Path (⟨c, hc⟩ : U) ⟨x, hx⟩ := PathConnectedSpace.somePath _ _
  let q : Path (⟨x, hx⟩ : U) ⟨z, hz⟩ := PathConnectedSpace.somePath _ _
  have hp : localPathClass U hc hx = (mk p).map f := by
    -- Any path inside the contractible subtype gives the same ambient local class.
    exact (subtypePathClass_eq_localPathClass U hc hx p).symm
  have hq : localPathClass U hx hz = (mk q).map f := by
    -- The same uniqueness principle applies to the second leg.
    exact (subtypePathClass_eq_localPathClass U hx hz q).symm
  have hpq : ((mk p).map f).trans ((mk q).map f) = (mk (p.trans q)).map f := by
    -- Mapping a concatenated local path agrees with concatenating the mapped path classes.
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_map]
    congr
    ext t
    simp [Path.trans_apply]
  -- The composite local class is represented by the concatenated subtype path.
  rw [hp, hq, hpq]
  exact subtypePathClass_eq_localPathClass U hc hz (p.trans q)

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: after shrinking to a smaller
contractible neighborhood, the ambient local path class factors through the chosen intermediate
point of the smaller neighborhood. -/
lemma localPathClass_factorThroughSubset
    {Y : Type uY} [TopologicalSpace Y] {U W : Set Y}
    [ContractibleSpace U] [ContractibleSpace W] (hWU : W ⊆ U)
    {c x z : Y} (hc : c ∈ U) (hx : x ∈ W) (hz : z ∈ W) :
    localPathClass U hc (hWU hz) =
      (localPathClass U hc (hWU hx)).trans (localPathClass W hx hz) := by
  -- First decompose the large-neighborhood class through the intermediate point inside `U`.
  calc
    localPathClass U hc (hWU hz)
      = (localPathClass U hc (hWU hx)).trans (localPathClass U (hWU hx) (hWU hz)) := by
          simpa using (localPathClass_trans U hc (hWU hx) (hWU hz)).symm
    _ = (localPathClass U hc (hWU hx)).trans (localPathClass W hx hz) := by
          rw [localPathClass_subset hWU hx hz]

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: reversing a concatenated path class
reverses the order of the two factors. -/
lemma pathClassTransSymm
    {Y : Type uY} [TopologicalSpace Y] {x₀ x₁ x₂ : Y}
    (γ₀ : Path.Homotopic.Quotient x₀ x₁) (γ₁ : Path.Homotopic.Quotient x₁ x₂) :
    (γ₀.trans γ₁).symm = γ₁.symm.trans γ₀.symm := by
  refine Quotient.inductionOn₂ γ₀ γ₁ ?_
  intro p q
  -- At the path level, path reversal swaps the concatenation order.
  change Path.Homotopic.Quotient.mk (Path.symm (Path.trans p q)) =
    (Path.Homotopic.Quotient.mk q.symm).trans (Path.Homotopic.Quotient.mk p.symm)
  rw [← Path.Homotopic.Quotient.mk_trans]
  congr
  ext t
  simp [Path.trans_apply]

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: the overlap cocycle comparison loops
cancel exactly as in a groupoid. -/
lemma pathClassCocycleCancel
    {Y : Type uY} [TopologicalSpace Y] {x₀ x : Y}
    (η : Path.Homotopic.Quotient x₀ x₀) (γ₀ γ₁ γ₂ : Path.Homotopic.Quotient x₀ x) :
    (η.trans (γ₀.trans γ₁.symm)).trans (γ₁.trans γ₂.symm) = η.trans (γ₀.trans γ₂.symm) := by
  -- Reassociate until the inverse pair sits next to each other, then cancel it.
  simp_rw [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc γ₁.symm γ₁ γ₂.symm,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: appending the same tail to two path
classes does not change their comparison loop. -/
lemma pathClassTransRightCancel
    {Y : Type uY} [TopologicalSpace Y] {x₀ x z : Y}
    (γ₀ γ₁ : Path.Homotopic.Quotient x₀ x) (δ : Path.Homotopic.Quotient x z) :
    (γ₀.trans δ).trans (γ₁.trans δ).symm = γ₀.trans γ₁.symm := by
  -- Expand the reversed concatenation and cancel the common tail.
  rw [pathClassTransSymm]
  simp_rw [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc δ δ.symm γ₁.symm,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: if the loop obtained by joining
`x₀ → x₁ → x₂ → x₀` is null-homotopic, then the middle segment is the canonical comparison class
from `x₁` to `x₂`. -/
lemma middlePathClass_eq_of_loop_eq_refl
    {Y : Type uY} [TopologicalSpace Y] {x₀ x₁ x₂ : Y}
    (γ₀ : Path.Homotopic.Quotient x₀ x₁) (γ₁ : Path.Homotopic.Quotient x₁ x₂)
    (γ₂ : Path.Homotopic.Quotient x₀ x₂)
    (hloop : (γ₀.trans γ₁).trans γ₂.symm = Path.Homotopic.Quotient.refl x₀) :
    γ₁ = γ₀.symm.trans γ₂ := by
  have hcancel :
      ((γ₀.symm.trans ((γ₀.trans γ₁).trans γ₂.symm)).trans γ₂) = γ₁ := by
    -- Cancel the right tail and then the left head in the groupoid of path classes.
    calc
      ((γ₀.symm.trans ((γ₀.trans γ₁).trans γ₂.symm)).trans γ₂)
          = (γ₀.symm.trans (((γ₀.trans γ₁).trans γ₂.symm).trans γ₂)) := by
              rw [Path.Homotopic.Quotient.trans_assoc]
      _ = (γ₀.symm.trans ((γ₀.trans γ₁).trans (γ₂.symm.trans γ₂))) := by
              rw [Path.Homotopic.Quotient.trans_assoc]
      _ = (γ₀.symm.trans ((γ₀.trans γ₁).trans (Path.Homotopic.Quotient.refl x₂))) := by
              rw [Path.Homotopic.Quotient.symm_trans]
      _ = (γ₀.symm.trans (γ₀.trans γ₁)) := by
              rw [Path.Homotopic.Quotient.trans_refl]
      _ = ((γ₀.symm.trans γ₀).trans γ₁) := by
              rw [← Path.Homotopic.Quotient.trans_assoc]
      _ = ((Path.Homotopic.Quotient.refl x₁).trans γ₁) := by
              rw [Path.Homotopic.Quotient.symm_trans]
      _ = γ₁ := by
              rw [Path.Homotopic.Quotient.refl_trans]
  calc
    γ₁ = ((γ₀.symm.trans ((γ₀.trans γ₁).trans γ₂.symm)).trans γ₂) := hcancel.symm
    _ = ((γ₀.symm.trans (Path.Homotopic.Quotient.refl x₀)).trans γ₂) := by
          rw [hloop]
    _ = γ₀.symm.trans γ₂ := by
          simp

/-- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: a covering map over a Hausdorff base
has Hausdorff total space. The equal-fiber case uses separatedness of covering maps, while the
distinct-fiber case is detected downstairs through continuity. -/
theorem IsCoveringMap.t2Space
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {f : E → X} (hf : IsCoveringMap f) : T2Space E := by
  rw [t2_iff_nhds]
  intro e₁ e₂ hneBot
  -- Push the nontrivial intersection of neighborhoods down to the base.
  have hbase : (nhds (f e₁) ⊓ nhds (f e₂)).NeBot := by
    letI : (nhds e₁ ⊓ nhds e₂).NeBot := hneBot
    exact Filter.Tendsto.neBot <|
      (hf.continuous.continuousAt.tendsto.inf hf.continuous.continuousAt.tendsto)
  have hproj : f e₁ = f e₂ := (t2_iff_nhds.mp (inferInstance : T2Space X)) hbase
  by_contra hne
  -- Once the base points agree, separatedness of the covering map forces disjoint neighborhoods.
  have hdisj : Disjoint (nhds e₁) (nhds e₂) :=
    (isSeparatedMap_iff_disjoint_nhds.mp hf.isSeparatedMap) _ _ hproj hne
  exact hneBot.ne hdisj.eq_bot

/-- Cartan section26 0005_Theorem_VI_5_extra_5: Theorem VI.5-extra-5 says that any connected
one-dimensional complex manifold `Y` has a simply connected unramified surface over it whose
projection is a surjective covering map. This includes the special case of a connected open subset
of `ℂ`, viewed as a Riemann surface. -/
theorem connected_complex_manifold_has_simplyConnected_covering
    {Y : Type uY} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [T2Space Y]
    [ConnectedSpace Y] :
    ∃ X : ConnectedHausdorffUnramifiedSurfaceOver.{uY, uY} Y,
      SimplyConnectedSpace X ∧ IsCoveringMap X.projection ∧ X.projection.Surjective := by
  classical
  letI : PathConnectedSpace Y := connectedComplexManifold_pathConnected (Y := Y)
  -- Route correction: the earlier proof route searched for a missing global universal-cover
  -- theorem. The verified local route instead starts by extracting contractible chart
  -- neighborhoods directly from the complex manifold structure.
  have hlocal : ∀ y : Y, ∃ U : Set Y, y ∈ U ∧ IsOpen U ∧ ContractibleSpace U :=
    contractibleChartNeighborhood
  let y₀ : Y := Classical.choice (ConnectedSpace.toNonempty (α := Y))
  let beta : ∀ y : Y, Path.Homotopic.Quotient y₀ y := fun y ↦
    mk (PathConnectedSpace.somePath y₀ y)
  let U : Y → Set Y := fun y ↦ Classical.choose (hlocal y)
  let centerMem : ∀ y : Y, y ∈ U y := fun y ↦ (Classical.choose_spec (hlocal y)).1
  let openU : ∀ y : Y, IsOpen (U y) := fun y ↦ (Classical.choose_spec (hlocal y)).2.1
  let contractibleU : ∀ y : Y, ContractibleSpace (U y) := fun y ↦
    (Classical.choose_spec (hlocal y)).2.2
  let F := Path.Homotopic.Quotient y₀ y₀
  let _ : TopologicalSpace F := ⊥
  let _ : DiscreteTopology F := ⟨rfl⟩
  -- The fixed loop fiber is transported to nearby points through the chosen contractible charts.
  let chartTransport : ∀ i : Y, ∀ {x : Y}, x ∈ U i → Path.Homotopic.Quotient y₀ x :=
    fun i {x} hx ↦
      (beta i).trans (@localPathClass Y _ (U i) (contractibleU i) i x (centerMem i) hx)
  -- On overlaps, change coordinates by right-translation with the loop comparing the two chart
  -- transports. Outside the overlap the value is irrelevant, so we keep the input label unchanged.
  let coordChange : Y → Y → Y → F → F := fun i j x a ↦
    if hxi : x ∈ U i then
      if hxj : x ∈ U j then
        a.trans ((chartTransport i (x := x) hxi).trans (chartTransport j (x := x) hxj).symm)
      else
        a
    else
      a
  have coordChange_self : ∀ i, ∀ x ∈ U i, ∀ v, coordChange i i x v = v := by
    intro i x hx v
    simp [coordChange, hx]
  have continuousOn_coordChange :
      ∀ i j, ContinuousOn (fun p : Y × F => coordChange i j p.1 p.2) ((U i ∩ U j) ×ˢ Set.univ) := by
    intro i j
    rw [continuousOn_iff_continuous_restrict]
    -- Route correction: continuity does not come from discreteness alone; we prove that the
    -- restricted overlap map is locally constant by shrinking to a smaller contractible chart.
    suffices hloc :
        IsLocallyConstant
          (((U i ∩ U j) ×ˢ Set.univ).restrict (fun p : Y × F => coordChange i j p.1 p.2)) by
      exact hloc.continuous
    rw [IsLocallyConstant.iff_exists_open]
    rintro ⟨⟨x, a⟩, hp⟩
    have hxij : x ∈ U i ∩ U j := by
      simpa [Set.mem_prod] using hp
    rcases contractibleChartNeighborhoodWithin
        (y := x) (s := U i ∩ U j) ((openU i).inter (openU j)) hxij with
      ⟨W, hxW, hWsub, hWopen, hWcontractible⟩
    let hWi : W ⊆ U i := fun z hz ↦ (hWsub hz).1
    let hWj : W ⊆ U j := fun z hz ↦ (hWsub hz).2
    let T : Set (((U i ∩ U j) ×ˢ Set.univ)) := Subtype.val ⁻¹' (W ×ˢ ({a} : Set F))
    let _ : ContractibleSpace W := hWcontractible
    have chartTransport_eq_i :
        ∀ {z : Y} (hz : z ∈ W),
          chartTransport i (x := z) (hWi hz) =
            (chartTransport i (x := x) hxij.1).trans (localPathClass W hxW hz) := by
      intro z hz
      -- Factor the ambient chart transport through the smaller contractible neighborhood `W`.
      calc
        chartTransport i (x := z) (hWi hz)
            = (beta i).trans (localPathClass (U i) (centerMem i) (hWi hz)) := by
              rfl
        _ = (beta i).trans
              ((localPathClass (U i) (centerMem i) hxij.1).trans (localPathClass W hxW hz)) := by
              rw [localPathClass_factorThroughSubset hWi (centerMem i) hxW hz]
        _ = (chartTransport i (x := x) hxij.1).trans (localPathClass W hxW hz) := by
              simp [chartTransport, Path.Homotopic.Quotient.trans_assoc]
    have chartTransport_eq_j :
        ∀ {z : Y} (hz : z ∈ W),
          chartTransport j (x := z) (hWj hz) =
            (chartTransport j (x := x) hxij.2).trans (localPathClass W hxW hz) := by
      intro z hz
      -- The same factorization holds for the second chart.
      calc
        chartTransport j (x := z) (hWj hz)
            = (beta j).trans (localPathClass (U j) (centerMem j) (hWj hz)) := by
              rfl
        _ = (beta j).trans
              ((localPathClass (U j) (centerMem j) hxij.2).trans (localPathClass W hxW hz)) := by
              rw [localPathClass_factorThroughSubset hWj (centerMem j) hxW hz]
        _ = (chartTransport j (x := x) hxij.2).trans (localPathClass W hxW hz) := by
              simp [chartTransport, Path.Homotopic.Quotient.trans_assoc]
    have comparison_eq :
        ∀ {z : Y} (hz : z ∈ W),
          (chartTransport i (x := z) (hWi hz)).trans (chartTransport j (x := z) (hWj hz)).symm =
            (chartTransport i (x := x) hxij.1).trans (chartTransport j (x := x) hxij.2).symm := by
      intro z hz
      -- Both overlap transports acquire the same tail inside `W`, so their comparison loop is
      -- constant on `W`.
      rw [chartTransport_eq_i hz, chartTransport_eq_j hz]
      simpa using
        pathClassTransRightCancel
          (chartTransport i (x := x) hxij.1)
          (chartTransport j (x := x) hxij.2)
          (localPathClass W hxW hz)
    refine ⟨T, ?_, ?_, ?_⟩
    · exact (hWopen.prod (isOpen_discrete ({a} : Set F))).preimage continuous_subtype_val
    · change (x, a) ∈ W ×ˢ ({a} : Set F)
      exact ⟨hxW, by simp⟩
    · intro q hq
      rcases q with ⟨⟨z, b⟩, hzS⟩
      have hqb : (z, b) ∈ W ×ˢ ({a} : Set F) := by
        simpa [T] using hq
      have hzW : z ∈ W := hqb.1
      have hb : b = a := by
        simpa using hqb.2
      subst b
      -- On the chosen neighborhood, the discrete fiber coordinate is fixed and the comparison
      -- loop is locally constant, so the overlap map is constant.
      change coordChange i j z a = coordChange i j x a
      simp [coordChange, hWi hzW, hWj hzW, hxij.1, hxij.2, comparison_eq hzW]
  have coordChange_comp :
      ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, ∀ v,
        coordChange j k x (coordChange i j x v) = coordChange i k x v := by
    intro i j k x hx v
    rcases hx with ⟨hxij, hxk⟩
    rcases hxij with ⟨hxi, hxj⟩
    -- On a genuine triple overlap, the cocycle law is just cancellation in the loop fiber.
    simp [coordChange, hxi, hxj, hxk]
    simpa [Path.Homotopic.Quotient.trans_assoc] using
      pathClassCocycleCancel v
        (chartTransport i (x := x) hxi)
        (chartTransport j (x := x) hxj)
        (chartTransport k (x := x) hxk)
  -- This packages the local chart data as a genuine discrete-fiber bundle, so the covering-map
  -- owner theorem can now be applied directly.
  let Z : FiberBundleCore Y Y F := {
    baseSet := U
    isOpen_baseSet := openU
    indexAt := id
    mem_baseSet_at := centerMem
    coordChange := coordChange
    coordChange_self := coordChange_self
    continuousOn_coordChange := continuousOn_coordChange
    coordChange_comp := coordChange_comp
  }
  have hcover : IsCoveringMap Z.proj := FiberBundle.isCoveringMap
  have hfiber : Nonempty F := ⟨Path.Homotopic.Quotient.refl y₀⟩
  let pointClassOfPoint : (p : Z.TotalSpace) → Path.Homotopic.Quotient y₀ p.1 :=
    fun p ↦ p.2.trans (beta p.1)
  let baseLift : Z.TotalSpace := ⟨y₀, (beta y₀).symm⟩
  -- Inside one fiber, the semantic endpoint class remembers the discrete loop coordinate.
  have pointClass_fiber_injective :
      ∀ {x : Y} {a b : F}, a.trans (beta x) = b.trans (beta x) → a = b := by
    intro x a b hab
    calc
      a = (a.trans (beta x)).trans (beta x).symm := by
            simp [Path.Homotopic.Quotient.trans_assoc]
      _ = (b.trans (beta x)).trans (beta x).symm := by rw [hab]
      _ = b := by
            simp [Path.Homotopic.Quotient.trans_assoc]
  have sameFiber_eq_of_pointClass_eq :
      ∀ {x : Y} {a b : F},
        a.trans (beta x) = b.trans (beta x) → ((⟨x, a⟩ : Z.TotalSpace) = ⟨x, b⟩) := by
    intro x a b hab
    have hab' : a = b := pointClass_fiber_injective hab
    cases hab'
    rfl
  have pointClassOfPoint_localTriv :
      ∀ {i : Y} {p : Z.TotalSpace} (hp : p.1 ∈ U i),
        ((Z.localTriv i p).2).trans (chartTransport i (x := p.1) hp) = pointClassOfPoint p := by
    intro i p hp
    -- In the `i`-chart, the fiber coordinate records exactly the loop error against the canonical
    -- chart transport from the chart center to `p.1`.
    change Path.Homotopic.Quotient.trans (coordChange p.1 i p.1 p.2)
        (chartTransport i (x := p.1) hp) = pointClassOfPoint p
    simp [coordChange, chartTransport, pointClassOfPoint, centerMem, hp, localPathClass_refl,
      Path.Homotopic.Quotient.trans_assoc]
  have liftPath_eq_cliftOnChart :
      ∀ {i z : Y} {p : Z.TotalSpace} (hp : p.1 ∈ U i) (γ : Path p.1 z)
        (hγ : ∀ t, γ t ∈ U i),
        let e : (Z.localTriv i).source := ⟨p, by simpa using hp⟩
        let γU : C(↥unitInterval, (Z.localTriv i).baseSet) :=
          ⟨fun t ↦ ⟨γ t, hγ t⟩, γ.continuous.subtype_mk hγ⟩
        let forgetSource : C((Z.localTriv i).source, Z.TotalSpace) :=
          ⟨Subtype.val, continuous_subtype_val⟩
        let Γ : C(↥unitInterval, Z.TotalSpace) :=
          forgetSource.comp ((Z.localTriv i).clift (e, γU))
        hcover.liftPath γ p γ.source = Γ := by
    intro i z p hp γ hγ
    let e : (Z.localTriv i).source := ⟨p, by simpa using hp⟩
    let γU : C(↥unitInterval, (Z.localTriv i).baseSet) :=
      ⟨fun t ↦ ⟨γ t, hγ t⟩, γ.continuous.subtype_mk hγ⟩
    let forgetSource : C((Z.localTriv i).source, Z.TotalSpace) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    let Γ : C(↥unitInterval, Z.TotalSpace) :=
      forgetSource.comp ((Z.localTriv i).clift (e, γU))
    -- On one chart, the lift is the chartwise local lift with constant fiber coordinate.
    refine ((hcover.eq_liftPath_iff' (γ := γ) (e := p) (γ_0 := γ.source) (Γ := Γ)).2 ?_).symm
    constructor
    · ext t
      change Z.proj (((Z.localTriv i).clift (e, γU) t).1) = γ t
      simpa [γU] using (Z.localTriv i).proj_clift (e := e) (γ := γU) (i := t)
    · have hzero :
        (Z.localTriv i).clift (e, γU) 0 = e := by
          refine (Z.localTriv i).clift_self (e := e) (γ := γU) (i := 0) ?_
          simp [e, γU]
      change (((Z.localTriv i).clift (e, γU) 0).1) = p
      exact congrArg Subtype.val hzero
  have pointClassOfPoint_baseLift :
      pointClassOfPoint baseLift = Path.Homotopic.Quotient.refl y₀ := by
    -- The distinguished lift uses the inverse of `beta y₀`, so its semantic point class is trivial.
    simp [baseLift, pointClassOfPoint, Path.Homotopic.Quotient.symm_trans]
  have pointClassOfLiftPathOnChart :
      ∀ {i z : Y} {p : Z.TotalSpace} (hp : p.1 ∈ U i) (γ : Path p.1 z)
        (hγ : ∀ t, γ t ∈ U i),
        let q : Z.TotalSpace := hcover.liftPath γ p γ.source 1
        let γq : Path p.1 q.1 := ⟨γ, γ.source, by
          simpa [q] using (congr_fun (hcover.liftPath_lifts γ p γ.source) 1).symm⟩
        pointClassOfPoint q = (pointClassOfPoint p).trans (Path.Homotopic.Quotient.mk γq) := by
    intro i z p hp γ hγ
    let e : (Z.localTriv i).source := ⟨p, by simpa using hp⟩
    let γU : C(↥unitInterval, (Z.localTriv i).baseSet) :=
      ⟨fun t ↦ ⟨γ t, hγ t⟩, γ.continuous.subtype_mk hγ⟩
    let forgetSource : C((Z.localTriv i).source, Z.TotalSpace) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    let Γ : C(↥unitInterval, Z.TotalSpace) :=
      forgetSource.comp ((Z.localTriv i).clift (e, γU))
    let q : Z.TotalSpace := hcover.liftPath γ p γ.source 1
    let γq : Path p.1 q.1 := ⟨γ, γ.source, by
      simpa [q] using (congr_fun (hcover.liftPath_lifts γ p γ.source) 1).symm⟩
    have hLift : hcover.liftPath γ p γ.source = Γ := liftPath_eq_cliftOnChart hp γ hγ
    have hqU : q.1 ∈ U i := by
      rw [show q.1 = γ 1 by simpa [q] using congr_fun (hcover.liftPath_lifts γ p γ.source) 1]
      exact hγ 1
    have hcoord : (Z.localTriv i q).2 = (Z.localTriv i p).2 := by
      rw [show q = Γ 1 by
        simpa [q] using congrArg (fun Γ' : C(↥unitInterval, Z.TotalSpace) => Γ' 1) hLift]
      change ((Z.localTriv i : Z.TotalSpace → Y × F) (((Z.localTriv i).clift (e, γU) 1).1)).2 =
        ((Z.localTriv i : Z.TotalSpace → Y × F) p).2
      -- The cocycle law collapses the `localTriv`-of-`localTriv.symm` normalization to the
      -- original starting fiber coordinate.
      change
        coordChange (Z.indexAt (γU 1).1) i (γU 1).1
            (coordChange i (Z.indexAt (γU 1).1) (γU 1).1
              (coordChange (Z.indexAt p.1) i p.1 p.2)) =
          coordChange (Z.indexAt p.1) i p.1 p.2
      have hcomp :=
          coordChange_comp i (γU 1).1 i (γU 1).1
            ⟨⟨(γU 1).2, centerMem ((γU 1).1)⟩, (γU 1).2⟩
            (coordChange (Z.indexAt p.1) i p.1 p.2)
      simpa using hcomp.trans (coordChange_self i (γU 1).1 (γU 1).2 _)
    have hlocal :
        localPathClass (U i) hp (γq.target ▸ hqU) = Path.Homotopic.Quotient.mk γq := by
      -- The projected path itself realizes the local class on the contractible chart.
      exact localPathClass_eq_mk (U := U i) hp γq (fun t ↦ by simpa [γq] using hγ t)
    have htransport :
        chartTransport i (x := q.1) hqU =
          (chartTransport i (x := p.1) hp).trans (Path.Homotopic.Quotient.mk γq) := by
      have hfactor :
          localPathClass (U i) (centerMem i) hqU =
            (localPathClass (U i) (centerMem i) hp).trans
              (Path.Homotopic.Quotient.mk γq) := by
        -- The canonical transport from the chart center factors through the starting point `p.1`.
        calc
          localPathClass (U i) (centerMem i) hqU
              = (localPathClass (U i) (centerMem i) hp).trans
                  (localPathClass (U i) hp (γq.target ▸ hqU)) := by
                    simpa using (localPathClass_trans (U i) (centerMem i) hp (γq.target ▸ hqU)).symm
          _ = (localPathClass (U i) (centerMem i) hp).trans
                (Path.Homotopic.Quotient.mk γq) := by
                  rw [hlocal]
      -- Re-express the endpoint chart transport through the canonical factorization above.
      simp [chartTransport, hfactor, Path.Homotopic.Quotient.trans_assoc]
    -- Route correction: the local endpoint semantics come from the explicit chartwise lift, not
    -- from a global monodromy theorem.
    calc
      pointClassOfPoint q
          = ((Z.localTriv i q).2).trans (chartTransport i (x := q.1) hqU) := by
              simpa [q] using (pointClassOfPoint_localTriv (i := i) (p := q) hqU).symm
      _ = ((Z.localTriv i p).2).trans
            ((chartTransport i (x := p.1) hp).trans (Path.Homotopic.Quotient.mk γq)) := by
              rw [hcoord, htransport]
      _ = (((Z.localTriv i p).2).trans (chartTransport i (x := p.1) hp)).trans
            (Path.Homotopic.Quotient.mk γq) := by
              simp [Path.Homotopic.Quotient.trans_assoc]
      _ = (pointClassOfPoint p).trans (Path.Homotopic.Quotient.mk γq) := by
              rw [pointClassOfPoint_localTriv hp]
  have pathClassCover_t2Space : T2Space Z.TotalSpace := hcover.t2Space
  let pointClassOver : ∀ {y : Y}, Z.proj ⁻¹' ({y} : Set Y) → Path.Homotopic.Quotient y₀ y :=
    fun {y} p ↦ (pointClassOfPoint p.1).cast rfl p.2.symm
  -- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: casting the target of a concatenated
  -- path-homotopy class only changes the right factor.
  have pathClassTrans_castRight :
      ∀ {x₁ x₂ x₃ x₃' : Y} (γ₁₂ : Path.Homotopic.Quotient x₁ x₂)
        (γ₂₃ : Path.Homotopic.Quotient x₂ x₃) (hx₃ : x₃' = x₃),
        (γ₁₂.trans γ₂₃).cast rfl hx₃ = γ₁₂.trans (γ₂₃.cast rfl hx₃) := by
    intro x₁ x₂ x₃ x₃' γ₁₂ γ₂₃ hx₃
    induction γ₁₂ using Path.Homotopic.Quotient.ind with
    | mk p =>
        induction γ₂₃ using Path.Homotopic.Quotient.ind with
        | mk q =>
            rfl
  -- Route correction: the remaining blocker is not the covering core but the missing
  -- `pointClassOver` transport lemma for non-`rfl` fibers, which is needed to globalize the
  -- one-chart endpoint formula across a finite `Path.subpath` subdivision.
  have pointClassOverMonodromyOnChart :
      ∀ {i x z : Y} (e : Z.proj ⁻¹' ({x} : Set Y)) (hx : x ∈ U i) (γ : Path x z)
        (hγ : ∀ t, γ t ∈ U i),
        pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk γ) e) =
          (pointClassOver e).trans (Path.Homotopic.Quotient.mk γ) := by
    intro i x z e hx γ hγ
    rcases e with ⟨p, hp⟩
    have hp' : p.1 = x := by
      simpa using hp
    subst x
    let q : Z.TotalSpace := hcover.liftPath γ p γ.source 1
    have hqPath : γ 1 = q.1 := by
      simpa [q] using (congr_fun (hcover.liftPath_lifts γ p γ.source) 1).symm
    have hq : q.1 = z := by
      simpa [q] using congr_fun (hcover.liftPath_lifts γ p γ.source) 1
    let γq : Path p.1 q.1 := ⟨γ, γ.source, hqPath⟩
    have hγq_def : γq = γ.cast rfl hq := by
      ext t
      rfl
    have hγq :
        Path.Homotopic.Quotient.mk γq = (Path.Homotopic.Quotient.mk γ).cast rfl hq := by
      -- The lifted endpoint path is just the original base path with its target rewritten.
      rw [hγq_def]
      exact Path.Homotopic.Quotient.mk_cast γ rfl hq
    have hpoint :
        pointClassOfPoint q = (pointClassOfPoint p).trans (Path.Homotopic.Quotient.mk γq) := by
      -- The chartwise lift computation gives the endpoint semantic class before the final cast.
      simpa [q, γq] using pointClassOfLiftPathOnChart (i := i) (p := p) (hp := hx) γ hγ
    -- Move the endpoint identity into the fiber subtype once, then cast the right path factor.
    calc
      pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk γ) ⟨p, by simp⟩)
          = (pointClassOfPoint q).cast rfl hq.symm := by
              rfl
      _ = ((pointClassOfPoint p).trans (Path.Homotopic.Quotient.mk γq)).cast rfl hq.symm := by
              rw [hpoint]
      _ = (pointClassOfPoint p).trans ((Path.Homotopic.Quotient.mk γq).cast rfl hq.symm) := by
              rw [pathClassTrans_castRight]
      _ = (pointClassOfPoint p).trans (Path.Homotopic.Quotient.mk γ) := by
              rw [hγq, Path.Homotopic.Quotient.cast_cast]
              rfl
      _ = (pointClassOver ⟨p, by simp⟩).trans (Path.Homotopic.Quotient.mk γ) := by
              simp [pointClassOver]
  -- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: once each segment of a finite path
  -- concatenation stays inside one chart, monodromy composes exactly as the concatenated class.
  have pointClassOverMonodromyConcat :
      ∀ {n : ℕ} {p : Fin (n + 1) → Y}
        (δ : (k : Fin n) → Path (p k.castSucc) (p k.succ))
        (idx : Fin n → Y) (hδ : ∀ k t, δ k t ∈ U (idx k))
        (e : Z.proj ⁻¹' ({p 0} : Set Y)),
        pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk (Path.concat p δ)) e) =
          (pointClassOver e).trans (Path.Homotopic.Quotient.mk (Path.concat p δ)) := by
    intro n
    induction n with
    | zero =>
        intro p δ idx hδ e
        -- The empty concatenation is the constant path, so monodromy does nothing.
        simp [Path.concat_zero, hcover.monodromy_refl]
    | succ n ih =>
        intro p δ idx hδ e
        let p' : Fin (n + 1) → Y := p ∘ Fin.castSucc
        let δ' : (k : Fin n) → Path (p' k.castSucc) (p' k.succ) := fun k ↦ δ k.castSucc
        let e' : Z.proj ⁻¹' ({p (Fin.castSucc (Fin.last n))} : Set Y) :=
          hcover.monodromy (Path.Homotopic.Quotient.mk (Path.concat p' δ')) e
        have hprefix :
            pointClassOver e' =
              (pointClassOver e).trans (Path.Homotopic.Quotient.mk (Path.concat p' δ')) := by
          exact ih δ' (fun k ↦ idx k.castSucc) (fun k t ↦ hδ k.castSucc t) e
        have hlastStart : p (Fin.castSucc (Fin.last n)) ∈ U (idx (Fin.last n)) := by
          simpa using (δ (Fin.last n)).source ▸ hδ (Fin.last n) 0
        have hlast :
            pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk (δ (Fin.last n))) e') =
              (pointClassOver e').trans (Path.Homotopic.Quotient.mk (δ (Fin.last n))) := by
          exact pointClassOverMonodromyOnChart e' hlastStart (δ (Fin.last n)) (hδ (Fin.last n))
        have hconcat :
            ((pointClassOver e).trans (Path.Homotopic.Quotient.mk (Path.concat p' δ'))).trans
                (Path.Homotopic.Quotient.mk (δ (Fin.last n))) =
              (pointClassOver e).trans (Path.Homotopic.Quotient.mk (Path.concat p δ)) := by
          simp [p', δ', Path.concat_succ, Path.Homotopic.Quotient.mk_trans,
            Path.Homotopic.Quotient.trans_assoc]
        have hrew :
            (pointClassOver e').trans (Path.Homotopic.Quotient.mk (δ (Fin.last n))) =
              ((pointClassOver e).trans
                (Path.Homotopic.Quotient.mk (Path.concat p' δ'))).trans
                (Path.Homotopic.Quotient.mk (δ (Fin.last n))) := by
          rw [hprefix]
          rfl
        exact
          (show pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk (Path.concat p δ)) e) =
              pointClassOver
                (hcover.monodromy
                  ((Path.Homotopic.Quotient.mk (Path.concat p' δ')).trans
                    (Path.Homotopic.Quotient.mk (δ (Fin.last n)))) e) by
              simpa [p', δ', Path.concat_succ, Path.Homotopic.Quotient.mk_trans]).trans <|
          (show pointClassOver
                (hcover.monodromy
                  ((Path.Homotopic.Quotient.mk (Path.concat p' δ')).trans
                    (Path.Homotopic.Quotient.mk (δ (Fin.last n)))) e) =
              pointClassOver
                (hcover.monodromy (Path.Homotopic.Quotient.mk (δ (Fin.last n))) e') by
              simpa [e', p', δ'] using congrArg pointClassOver
                (hcover.monodromy_trans_apply
                  (Path.Homotopic.Quotient.mk (Path.concat p' δ'))
                  (Path.Homotopic.Quotient.mk (δ (Fin.last n))) e)).trans <|
          hlast.trans <|
          hrew.trans hconcat
  -- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: compactness of the unit interval turns
  -- the pointwise chart cover along a path into a finite `Fin`-indexed subdivision by subpaths.
  have existsFiniteChartSubdivision :
      ∀ {y : Y} (γ : Path y₀ y),
        ∃ n : ℕ, ∃ t : Fin (n + 1) → ↥unitInterval, ∃ idx : Fin n → Y,
          t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
          ∀ k : Fin n, ∀ s, γ.subpath (t k.castSucc) (t k.succ) s ∈ U (idx k) := by
    intro y γ
    let c : Y → Set ↥unitInterval := fun i ↦ γ ⁻¹' U i
    have hcoverI : (Set.univ : Set ↥unitInterval) ⊆ ⋃ i, c i := by
      intro s hs
      exact Set.mem_iUnion.mpr ⟨γ s, centerMem (γ s)⟩
    obtain ⟨tNat, ht0, htmono, ⟨n, hlast⟩, hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval
        (fun i ↦ (openU i).preimage γ.continuous) hcoverI
    let t : Fin (n + 1) → ↥unitInterval := fun k ↦ tNat k
    let idx : Fin n → Y := fun k ↦ Classical.choose (hsub k)
    have hidx :
        ∀ k : Fin n, Set.Icc (t k.castSucc) (t k.succ) ⊆ γ ⁻¹' U (idx k) := by
      intro k
      exact Classical.choose_spec (hsub k)
    refine ⟨n, t, idx, ht0, hlast n le_rfl, fun i j hij ↦ htmono hij, ?_⟩
    intro k s
    have hk : t k.castSucc ≤ t k.succ := htmono (Fin.castSucc_le_succ k)
    have hsRange :
        γ.subpath (t k.castSucc) (t k.succ) s ∈ γ '' Set.Icc (t k.castSucc) (t k.succ) := by
      have :
          γ.subpath (t k.castSucc) (t k.succ) s ∈
            Set.range (γ.subpath (t k.castSucc) (t k.succ)) :=
        ⟨s, rfl⟩
      simpa [Path.range_subpath_of_le γ _ _ hk] using this
    rcases hsRange with ⟨u, hu, hEq⟩
    rw [← hEq]
    exact hidx k hu
  -- Helper for Cartan section26 0005_Theorem_VI_5_extra_5: once a path is subdivided into
  -- chart-contained subpaths, the concatenation of those subpaths still represents the original
  -- quotient class after casting its endpoints back to `y₀` and `y`.
  have concatSubdivision_mk_eq :
      ∀ {y : Y} (γ : Path y₀ y) {n : ℕ} (t : Fin (n + 1) → ↥unitInterval)
        (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1),
        let p : Fin (n + 1) → Y := fun k ↦ γ (t k)
        let δ : (k : Fin n) → Path (p k.castSucc) (p k.succ) :=
          fun k ↦ γ.subpath (t k.castSucc) (t k.succ)
        let P : Path y₀ y := (Path.concat p δ).cast
          (by simpa [p, ht0] using γ.source.symm) (by simpa [p, ht1] using γ.target.symm)
        Path.Homotopic.Quotient.mk P = Path.Homotopic.Quotient.mk γ := by
    intro y γ n t ht0 ht1
    let p : Fin (n + 1) → Y := fun k ↦ γ (t k)
    let δ : (k : Fin n) → Path (p k.castSucc) (p k.succ) :=
      fun k ↦ γ.subpath (t k.castSucc) (t k.succ)
    let P : Path y₀ y := (Path.concat p δ).cast
      (by simpa [p, ht0] using γ.source.symm) (by simpa [p, ht1] using γ.target.symm)
    have hraw :
        Path.Homotopic.Quotient.mk (Path.concat p δ) =
          Path.Homotopic.Quotient.mk (γ.subpath (t 0) (t (Fin.last n))) := by
      -- `Path.concat_subpath` collapses the concatenation of all subpaths back to the long
      -- subpath from `t 0` to `t (last n)`.
      simpa [p, δ] using
        ((Path.Homotopic.Quotient.eq).2 (Path.Homotopic.concat_subpath γ t))
    have hPconcat :
        Path.Homotopic.Quotient.mk P =
          Path.Homotopic.Quotient.mk
            ((γ.subpath (t 0) (t (Fin.last n))).cast
              (by simpa [ht0] using γ.source.symm) (by simpa [ht1] using γ.target.symm)) := by
      -- Cast the quotient equality from the subdivided endpoints back to the original endpoints.
      simpa [P] using congrArg
        (fun q : Path.Homotopic.Quotient (p 0) (p (Fin.last n)) =>
          q.cast (by simpa [p, ht0] using γ.source.symm) (by simpa [p, ht1] using γ.target.symm))
        hraw
    have hPsub :
        Path.Homotopic.Quotient.mk
            ((γ.subpath (t 0) (t (Fin.last n))).cast
              (by simpa [ht0] using γ.source.symm) (by simpa [ht1] using γ.target.symm)) =
          Path.Homotopic.Quotient.mk γ := by
      -- After rewriting the subdivision endpoints to `0` and `1`, the casted subpath is
      -- literally the original path.
      apply congrArg Path.Homotopic.Quotient.mk
      ext s
      simp [Path.subpath, ht0, ht1]
    exact hPconcat.trans hPsub
  have pointClassOverMonodromyCast :
      ∀ {x y x' y' : Y} (γ : Path x y) (hx : x' = x) (hy : y' = y)
        (e : Z.proj ⁻¹' ({x'} : Set Y)),
        pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk (γ.cast hx hy)) e) =
          (pointClassOver
            (hcover.monodromy (Path.Homotopic.Quotient.mk γ)
              ⟨e.1, by simpa [hx] using e.2⟩)).cast rfl hy := by
    intro x y x' y' γ hx hy e
    cases hx
    cases hy
    simpa using (Path.Homotopic.Quotient.cast_rfl_rfl
      (pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk γ) e))).symm
  have reflCastTrans :
      ∀ {x y : Y} (Γ : Path.Homotopic.Quotient x y) (hx : y₀ = x),
        ((Path.Homotopic.Quotient.refl y₀).cast rfl hx.symm).trans Γ = Γ.cast hx rfl := by
    intro x y Γ hx
    induction Γ using Path.Homotopic.Quotient.ind with
    | mk γ =>
        cases hx
        simp
  have pointClassOfBaseLiftMonodromy :
      ∀ {y : Y} (Γ : Path.Homotopic.Quotient y₀ y),
        pointClassOver (hcover.monodromy Γ ⟨baseLift, rfl⟩) = Γ := by
    intro y Γ
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective Γ
    rcases existsFiniteChartSubdivision γ with ⟨n, t, idx, ht0, ht1, _, hsub⟩
    let p : Fin (n + 1) → Y := fun k ↦ γ (t k)
    let δ : (k : Fin n) → Path (p k.castSucc) (p k.succ) :=
      fun k ↦ γ.subpath (t k.castSucc) (t k.succ)
    have h0 : y₀ = p 0 := by
      simpa [p, ht0] using γ.source.symm
    have h1 : y = p (Fin.last n) := by
      simpa [p, ht1] using γ.target.symm
    let P : Path y₀ y := (Path.concat p δ).cast h0 h1
    let e0 : Z.proj ⁻¹' ({p 0} : Set Y) := ⟨baseLift, by simpa [baseLift] using h0⟩
    have hcast :
        pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk P) ⟨baseLift, rfl⟩) =
          (pointClassOver
            (hcover.monodromy (Path.Homotopic.Quotient.mk (Path.concat p δ)) e0)).cast rfl h1 := by
      -- Rewrite the subdivided concatenation representative to the casted path accepted by
      -- `monodromy` at the distinguished base lift.
      simpa [P, e0] using
        pointClassOverMonodromyCast (γ := Path.concat p δ) (hx := h0) (hy := h1)
          (e := ⟨baseLift, rfl⟩)
    have hconcat :
        pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk (Path.concat p δ)) e0) =
          (pointClassOver e0).trans (Path.Homotopic.Quotient.mk (Path.concat p δ)) := by
      -- The finite chart subdivision globalizes the one-chart monodromy computation.
      exact pointClassOverMonodromyConcat δ idx hsub e0
    have hbase :
        ((pointClassOver e0).trans (Path.Homotopic.Quotient.mk (Path.concat p δ))).cast rfl h1 =
          Path.Homotopic.Quotient.mk P := by
      -- After moving the final cast to the right factor, the left factor is the trivial class of
      -- the distinguished base lift, so the concatenated class is exactly the casted path class.
      rw [pathClassTrans_castRight]
      have he0 :
          pointClassOver e0 = (Path.Homotopic.Quotient.refl y₀).cast rfl h0.symm := by
        simp [e0, pointClassOver, pointClassOfPoint_baseLift]
      rw [he0]
      simpa [P, Path.Homotopic.Quotient.cast_cast] using
        (reflCastTrans
          ((Path.Homotopic.Quotient.mk (Path.concat p δ)).cast rfl h1) h0)
    have hPγ : Path.Homotopic.Quotient.mk P = Path.Homotopic.Quotient.mk γ :=
      concatSubdivision_mk_eq γ t ht0 ht1
    calc
      pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk γ) ⟨baseLift, rfl⟩)
          = pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk P) ⟨baseLift, rfl⟩) := by
              rw [hPγ.symm]
      _ = pointClassOver (hcover.monodromy (Path.Homotopic.Quotient.mk P) ⟨baseLift, rfl⟩) := rfl
      _ = (pointClassOver
              (hcover.monodromy (Path.Homotopic.Quotient.mk (Path.concat p δ)) e0)).cast
              rfl h1 := hcast
      _ = ((pointClassOver e0).trans
              (Path.Homotopic.Quotient.mk (Path.concat p δ))).cast rfl h1 := by
            rw [hconcat]
      _ = Path.Homotopic.Quotient.mk P := hbase
      _ = Path.Homotopic.Quotient.mk γ := hPγ
  have pointClassOverMonodromy :
      ∀ {x y : Y} (e : Z.proj ⁻¹' ({x} : Set Y)) (Γ : Path.Homotopic.Quotient x y),
        pointClassOver (hcover.monodromy Γ e) = (pointClassOver e).trans Γ := by
    intro x y e Γ
    rcases e with ⟨⟨x, a⟩, rfl⟩
    have hbaseLift :
        hcover.monodromy
            (pointClassOver (⟨⟨x, a⟩, rfl⟩ : Z.proj ⁻¹' ({x} : Set Y))) ⟨baseLift, rfl⟩ =
          (⟨⟨x, a⟩, rfl⟩ : Z.proj ⁻¹' ({x} : Set Y)) := by
      -- The specialized base-lift theorem reconstructs every fiber point from its point class.
      cases hm :
        hcover.monodromy
            (pointClassOver (⟨⟨x, a⟩, rfl⟩ : Z.proj ⁻¹' ({x} : Set Y))) ⟨baseLift, rfl⟩ with
      | mk p hp =>
          cases p with
          | mk x' b =>
              simp only [FiberBundleCore.proj] at hp
              cases hp
              apply Subtype.ext
              apply sameFiber_eq_of_pointClass_eq
              change Path.Homotopic.Quotient.trans b (beta x') =
                Path.Homotopic.Quotient.trans a (beta x')
              have hclass :=
                pointClassOfBaseLiftMonodromy
                  (Γ := pointClassOver (⟨⟨x', a⟩, rfl⟩ : Z.proj ⁻¹' ({x'} : Set Y)))
              rw [hm] at hclass
              simpa [pointClassOver, pointClassOfPoint] using hclass
    calc
      pointClassOver (hcover.monodromy Γ (⟨⟨x, a⟩, rfl⟩ : Z.proj ⁻¹' ({x} : Set Y)))
          = pointClassOver
              (hcover.monodromy Γ
                (hcover.monodromy
                  (pointClassOver (⟨⟨x, a⟩, rfl⟩ : Z.proj ⁻¹' ({x} : Set Y)))
                  ⟨baseLift, rfl⟩)) := by
              rw [hbaseLift]
      _ = pointClassOver
            (hcover.monodromy
              ((pointClassOver (⟨⟨x, a⟩, rfl⟩ : Z.proj ⁻¹' ({x} : Set Y))).trans Γ)
              ⟨baseLift, rfl⟩) := by
              rw [← hcover.monodromy_trans_apply
                (pointClassOver (⟨⟨x, a⟩, rfl⟩ : Z.proj ⁻¹' ({x} : Set Y))) Γ ⟨baseLift, rfl⟩]
      _ = (pointClassOver (⟨⟨x, a⟩, rfl⟩ : Z.proj ⁻¹' ({x} : Set Y))).trans Γ := by
              simpa using pointClassOfBaseLiftMonodromy
                (Γ := (pointClassOver (⟨⟨x, a⟩, rfl⟩ : Z.proj ⁻¹' ({x} : Set Y))).trans Γ)
  have joinedBaseLift : ∀ q : Z.TotalSpace, Joined baseLift q := by
    rintro ⟨x, a⟩
    obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (pointClassOfPoint ⟨x, a⟩)
    let Γ : C(↥unitInterval, Z.TotalSpace) := hcover.liftPath γ baseLift γ.source
    have hendpoint :
        hcover.monodromy (Path.Homotopic.Quotient.mk γ) ⟨baseLift, rfl⟩ = ⟨⟨x, a⟩, rfl⟩ := by
      -- The lifted representative ends at the unique point in the target fiber with the
      -- prescribed semantic point class.
      cases hm : hcover.monodromy (Path.Homotopic.Quotient.mk γ) ⟨baseLift, rfl⟩ with
      | mk p hp =>
          cases p with
          | mk x' b =>
              simp only [FiberBundleCore.proj] at hp
              cases hp
              apply Subtype.ext
              apply sameFiber_eq_of_pointClass_eq
              change Path.Homotopic.Quotient.trans b (beta x') =
                Path.Homotopic.Quotient.trans a (beta x')
              have hclass := pointClassOfBaseLiftMonodromy (Γ := Path.Homotopic.Quotient.mk γ)
              rw [hm] at hclass
              simpa [hγ, pointClassOver, pointClassOfPoint] using hclass
    refine ⟨⟨Γ, ?_, ?_⟩⟩
    · -- The lifted path starts at the distinguished base lift.
      simpa [Γ] using hcover.liftPath_zero γ baseLift γ.source
    · -- The lifted path ends at the required point by the monodromy computation above.
      simpa [Γ, IsCoveringMap.monodromy] using congrArg Subtype.val hendpoint
  have pathClassCover_pathConnected : PathConnectedSpace Z.TotalSpace := by
    refine ⟨⟨baseLift⟩, ?_⟩
    intro q r
    -- Join any two points by passing through the distinguished base lift.
    exact (joinedBaseLift q).symm.trans (joinedBaseLift r)
  have pathClassCoverSimplyConnected : SimplyConnectedSpace Z.TotalSpace := by
    rw [simply_connected_iff_paths_homotopic]
    refine ⟨pathClassCover_pathConnected, ?_⟩
    intro q r
    refine ⟨fun α β ↦ ?_⟩
    apply hcover.injective_path_homotopic_map q r
    have hα :
        α.map ⟨Z.proj, hcover.continuous⟩ =
          (pointClassOfPoint q).symm.trans (pointClassOfPoint r) := by
      have hstep :
          (pointClassOfPoint q).trans (α.map ⟨Z.proj, hcover.continuous⟩) =
            pointClassOfPoint r := by
        calc
          (pointClassOfPoint q).trans (α.map ⟨Z.proj, hcover.continuous⟩)
              = pointClassOver
                  (hcover.monodromy (α.map ⟨Z.proj, hcover.continuous⟩) ⟨q, rfl⟩) := by
                    symm
                    simpa [pointClassOver] using
                      pointClassOverMonodromy
                        (e := (⟨q, rfl⟩ : Z.proj ⁻¹' ({q.1} : Set Y)))
                        (Γ := α.map ⟨Z.proj, hcover.continuous⟩)
          _ = pointClassOver ⟨r, rfl⟩ := by
                rw [hcover.monodromy_map α]
          _ = pointClassOfPoint r := by
                simp [pointClassOver]
      have hloop :
          ((pointClassOfPoint q).trans (α.map ⟨Z.proj, hcover.continuous⟩)).trans
              (pointClassOfPoint r).symm =
            Path.Homotopic.Quotient.refl y₀ := by
        rw [hstep, Path.Homotopic.Quotient.trans_symm]
      exact middlePathClass_eq_of_loop_eq_refl
        (γ₀ := pointClassOfPoint q) (γ₁ := α.map ⟨Z.proj, hcover.continuous⟩)
        (γ₂ := pointClassOfPoint r) hloop
    have hβ :
        β.map ⟨Z.proj, hcover.continuous⟩ =
          (pointClassOfPoint q).symm.trans (pointClassOfPoint r) := by
      have hstep :
          (pointClassOfPoint q).trans (β.map ⟨Z.proj, hcover.continuous⟩) =
            pointClassOfPoint r := by
        calc
          (pointClassOfPoint q).trans (β.map ⟨Z.proj, hcover.continuous⟩)
              = pointClassOver
                  (hcover.monodromy (β.map ⟨Z.proj, hcover.continuous⟩) ⟨q, rfl⟩) := by
                    symm
                    simpa [pointClassOver] using
                      pointClassOverMonodromy
                        (e := (⟨q, rfl⟩ : Z.proj ⁻¹' ({q.1} : Set Y)))
                        (Γ := β.map ⟨Z.proj, hcover.continuous⟩)
          _ = pointClassOver ⟨r, rfl⟩ := by
                rw [hcover.monodromy_map β]
          _ = pointClassOfPoint r := by
                simp [pointClassOver]
      have hloop :
          ((pointClassOfPoint q).trans (β.map ⟨Z.proj, hcover.continuous⟩)).trans
              (pointClassOfPoint r).symm =
            Path.Homotopic.Quotient.refl y₀ := by
        rw [hstep, Path.Homotopic.Quotient.trans_symm]
      exact middlePathClass_eq_of_loop_eq_refl
        (γ₀ := pointClassOfPoint q) (γ₁ := β.map ⟨Z.proj, hcover.continuous⟩)
        (γ₂ := pointClassOfPoint r) hloop
    exact hα.trans hβ.symm
  letI : SimplyConnectedSpace Z.TotalSpace := pathClassCoverSimplyConnected
  let X : ConnectedHausdorffUnramifiedSurfaceOver Y := {
    carrier := Z.TotalSpace
    topology := inferInstance
    projection := Z.proj
    isLocalHomeomorph := hcover.isLocalHomeomorph
    connected := inferInstance
    t2Space := pathClassCover_t2Space
  }
  -- The already-constructed covering core packages directly as the required unramified surface.
  have hXsc : SimplyConnectedSpace X := by
    simpa [X] using pathClassCoverSimplyConnected
  have hXcov : IsCoveringMap X.projection := by
    simpa [X] using hcover
  have hXsurj : X.projection.Surjective := by
    simpa [X, FiberBundleCore.proj] using
      (FiberBundle.surjective_proj (F := F) (E := Z.Fiber))
  exact @Exists.intro (ConnectedHausdorffUnramifiedSurfaceOver.{uY, uY} Y)
    (fun X => SimplyConnectedSpace X ∧ IsCoveringMap X.projection ∧ X.projection.Surjective)
    X ⟨hXsc, hXcov, hXsurj⟩
