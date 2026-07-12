import Mathlib
import DifferentialForms_Cartan_1970.VI.RiemannSphere
import DifferentialForms_Cartan_1970.VI.section23.«0003_Theorem_3»
import DifferentialForms_Cartan_1970.VI.section24.«0001_Theorem_VI_3_extra_1»
import DifferentialForms_Cartan_1970.VI.section25.«0007_Theorem_VI_4_extra_7»
import DifferentialForms_Cartan_1970.VI.section25.«0008_Proposition_4_I»
import DifferentialForms_Cartan_1970.VI.section25.«0014_Proposition_6_1»

universe u

open scoped Complex.UnitDisc Manifold
open Filter

namespace Complex.UnitDisc

/-- The canonical coercion from the unit disc `𝔻` to `ℂ` is an open embedding. -/
theorem isOpenEmbedding_coe : Topology.IsOpenEmbedding ((↑) : 𝔻 → ℂ) := by
  simpa [Complex.UnitDisc] using
    ((Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal :
      Topology.IsOpenEmbedding ((↑) : Metric.ball (0 : ℂ) 1 → ℂ))

noncomputable instance : ChartedSpace ℂ 𝔻 :=
  isOpenEmbedding_coe.singletonChartedSpace

/-- The unit disc inherits the Hausdorff topology from the ambient complex plane. -/
instance : T2Space 𝔻 := inferInstanceAs (T2Space (Metric.ball (0 : ℂ) 1))

instance : IsManifold 𝓘(ℂ) 1 𝔻 :=
  isOpenEmbedding_coe.isManifold_singleton

end Complex.UnitDisc

section

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: composing with the subtype inclusion
into an open subset does not change `C¹` regularity. -/
lemma contMDiff_subtypeValComp_iff {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {U : TopologicalSpace.Opens Y} {f : Z → U} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ f) ↔ ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 f := by
  -- The ambient and subtype formulations are equivalent through the standard lift-prop API.
  simp only [ContMDiff, ContMDiffAt, ContMDiffWithinAt]
  constructor
  · intro h x
    exact
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp 𝓘(ℂ) 𝓘(ℂ) 1) (f := f) (s := Set.univ) (x := x)).mp
        (h x)
  · intro h x
    exact
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp 𝓘(ℂ) 𝓘(ℂ) 1) (f := f) (s := Set.univ) (x := x)).mpr
        (h x)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a `C¹` open partial homeomorphism
packages to a `C¹` equivalence between its source and target open submanifolds. -/
lemma openPartialHomeomorph_toComplexManifoldEquivSourceTarget
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (f : OpenPartialHomeomorph X Y)
    (h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f f.source)
    (h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm f.target) :
    let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
    let V : TopologicalSpace.Opens Y := ⟨f.target, f.open_target⟩
    Nonempty (U ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ V) := by
  let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
  let V : TopologicalSpace.Opens Y := ⟨f.target, f.open_target⟩
  let g : U → V := fun x ↦ ⟨f x, f.mapsTo x.2⟩
  let h : U ≃ₜ V := f.toHomeomorphSourceTarget
  let gInv : V → U := fun y ↦ ⟨f.symm y, f.symm_mapsTo y.2⟩
  have h_to' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 g := by
    -- First prove smoothness after forgetting the target subtype, then repackage it.
    have hambient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ g) := by
      have hsub : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : U → X) := contMDiff_subtype_val
      have hcomp : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun x : U ↦ f x.1) Set.univ := by
        simpa [Function.comp] using h_to.comp hsub.contMDiffOn (by
          intro x hx
          exact x.2)
      simpa [g, Function.comp, contMDiffOn_univ] using hcomp
    exact (contMDiff_subtypeValComp_iff (Z := U) (Y := Y) (U := V) (f := g)).mp hambient
  have h_inv' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 gInv := by
    -- The inverse branch is handled in the same ambient-first way.
    have hambient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ gInv) := by
      have hsub : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : V → Y) := contMDiff_subtype_val
      have hcomp : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun y : V ↦ f.symm y.1) Set.univ := by
        simpa [Function.comp] using h_inv.comp hsub.contMDiffOn (by
          intro y hy
          exact y.2)
      simpa [gInv, Function.comp, contMDiffOn_univ] using hcomp
    exact (contMDiff_subtypeValComp_iff (Z := V) (Y := X) (U := U) (f := gInv)).mp hambient
  refine ⟨{ toEquiv := h.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }⟩
  · -- The homeomorphism's forward branch is exactly the subtype-valued restricted map `g`.
    simpa [h, g, U, V]
      using h_to'
  · -- The inverse homeomorphism is the subtype-valued restricted inverse branch `gInv`.
    simpa [h, gInv, U, V]
      using h_inv'

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the canonical homeomorphism attached
to an open partial homeomorphism is `C¹` on the source open subtype. -/
lemma openPartialHomeomorph_toHomeomorphSourceTarget_contMDiff_toFun
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (f : OpenPartialHomeomorph X Y)
    (h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f f.source)
    (h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm f.target) :
    let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
    let V : TopologicalSpace.Opens Y := ⟨f.target, f.open_target⟩
    let g : U → V := fun x ↦ ⟨f x, f.mapsTo x.2⟩
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 g := by
  let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
  let V : TopologicalSpace.Opens Y := ⟨f.target, f.open_target⟩
  let g : U → V := fun x ↦ ⟨f x, f.mapsTo x.2⟩
  -- First prove smoothness after forgetting the target subtype, then repackage it.
  have hambient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ g) := by
    have hsub : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : U → X) := contMDiff_subtype_val
    have hcomp : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun x : U ↦ f x.1) Set.univ := by
      simpa [Function.comp] using h_to.comp hsub.contMDiffOn (by
        intro x hx
        exact x.2)
    simpa [g, Function.comp, contMDiffOn_univ] using hcomp
  -- The canonical homeomorphism has the same forward map as the restricted branch `g`.
  simpa [g, U, V] using
    (contMDiff_subtypeValComp_iff (Z := U) (Y := Y) (U := V) (f := g)).mp hambient

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the inverse of the canonical
homeomorphism attached to an open partial homeomorphism is `C¹` on the target open subtype. -/
lemma openPartialHomeomorph_toHomeomorphSourceTarget_contMDiff_invFun
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (f : OpenPartialHomeomorph X Y)
    (h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f f.source)
    (h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm f.target) :
    let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
    let V : TopologicalSpace.Opens Y := ⟨f.target, f.open_target⟩
    let gInv : V → U := fun y ↦ ⟨f.symm y, f.symm_mapsTo y.2⟩
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 gInv := by
  let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
  let V : TopologicalSpace.Opens Y := ⟨f.target, f.open_target⟩
  let gInv : V → U := fun y ↦ ⟨f.symm y, f.symm_mapsTo y.2⟩
  -- The inverse branch is handled in the same ambient-first way.
  have hambient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ gInv) := by
    have hsub : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : V → Y) := contMDiff_subtype_val
    have hcomp : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun y : V ↦ f.symm y.1) Set.univ := by
      simpa [Function.comp] using h_inv.comp hsub.contMDiffOn (by
        intro y hy
        exact y.2)
    simpa [gInv, Function.comp, contMDiffOn_univ] using hcomp
  -- The canonical inverse map has the same formula as the restricted inverse branch `gInv`.
  simpa [gInv, U, V] using
    (contMDiff_subtypeValComp_iff (Z := V) (Y := X) (U := U) (f := gInv)).mp hambient

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the canonical open-submanifold
equivalence attached to an open partial homeomorphism. This keeps the underlying homeomorphism
definitionally tied to `toHomeomorphSourceTarget`, which is needed later when reparameterizing
local sphere charts. -/
noncomputable def openPartialHomeomorph_complexManifoldEquivSourceTarget
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (f : OpenPartialHomeomorph X Y)
    (h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f f.source)
    (h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm f.target) :
    let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
    let V : TopologicalSpace.Opens Y := ⟨f.target, f.open_target⟩
    U ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ V :=
  let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
  let V : TopologicalSpace.Opens Y := ⟨f.target, f.open_target⟩
  { toEquiv := f.toHomeomorphSourceTarget.toEquiv
    contMDiff_toFun :=
      openPartialHomeomorph_toHomeomorphSourceTarget_contMDiff_toFun
        (f := f) h_to h_inv
    contMDiff_invFun :=
      openPartialHomeomorph_toHomeomorphSourceTarget_contMDiff_invFun
        (f := f) h_to h_inv }

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a `C¹` open partial homeomorphism
onto the whole target manifold induces a `C¹` equivalence from its open source subtype to the
ambient target. -/
lemma openPartialHomeomorph_toComplexManifoldEquivOfTargetEqUniv
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (f : OpenPartialHomeomorph X Y)
    (h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f f.source)
    (h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm f.target)
    (ht : f.target = Set.univ) :
    let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
    Nonempty (U ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y) := by
  let U : TopologicalSpace.Opens X := ⟨f.source, f.open_source⟩
  let g : Y → U := fun y ↦
    ⟨f.symm y, by
      have hy : y ∈ f.target := by simpa [ht]
      simpa using f.map_target hy⟩
  let h : U ≃ₜ Y :=
    (f.toHomeomorphSourceTarget.trans (Homeomorph.setCongr ht)).trans (Homeomorph.Set.univ Y)
  have h_to' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (fun x : U ↦ f x) := by
    -- Restrict the forward branch to the source subtype and use the ambient `C¹` proof.
    have hsub : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : U → X) := contMDiff_subtype_val
    have hcomp : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun x : U ↦ f x.1) Set.univ := by
      simpa using h_to.comp hsub.contMDiffOn (by
        intro x hx
        exact x.2)
    simpa [contMDiffOn_univ, U, Function.comp] using hcomp
  have h_inv' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 g := by
    -- The inverse branch is smooth once we forget the target subtype and recover it afterward.
    have hambient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ g) := by
      have hglobal : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm Set.univ := by
        simpa [ht] using h_inv
      simpa [contMDiffOn_univ, g, Function.comp] using hglobal
    exact (contMDiff_subtypeValComp_iff (Z := Y) (Y := X) (U := U) (f := g)).mp hambient
  refine ⟨{ toEquiv := h.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }⟩
  · -- The forward homeomorphism is just the restricted forward branch.
    simpa [h, U, Function.comp] using h_to'
  · -- The inverse homeomorphism is the subtype-valued inverse branch `g`.
    simpa [h, g, U, ht, Function.comp] using h_inv'

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: simply connectedness of an open
submanifold of `ℂ` can be read either on the subtype or on the underlying set. -/
lemma isSimplyConnected_coe_of_simplyConnectedSpace (D : TopologicalSpace.Opens ℂ)
    [SimplyConnectedSpace D] :
    IsSimplyConnected (D : Set ℂ) := by
  -- `IsSimplyConnected` is the simply-connectedness class on the subtype `D`.
  change SimplyConnectedSpace D
  infer_instance

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: an open subset of the Riemann sphere
that omits `∞` is biholomorphic to an open subset of the complex plane via the affine chart. -/
lemma riemannSphereOpenSubsetAwayFromInfty_equiv_openSubsetComplex
    (V : TopologicalSpace.Opens RiemannSphere) (hV : OnePoint.infty ∉ (V : Set RiemannSphere)) :
    ∃ D : TopologicalSpace.Opens ℂ, Nonempty (V ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ D) := by
  let f : OpenPartialHomeomorph RiemannSphere ℂ :=
    RiemannSphere.affineOpenPartialHomeomorph.restr (V : Set RiemannSphere)
  let D : TopologicalSpace.Opens ℂ := ⟨f.target, f.open_target⟩
  have hV_subset :
      (V : Set RiemannSphere) ⊆ RiemannSphere.affineOpenPartialHomeomorph.source := by
    intro x hx
    change x ≠ OnePoint.infty
    intro hx_infty
    exact hV (hx_infty ▸ hx)
  have hsource : f.source = (V : Set RiemannSphere) := by
    calc
      f.source = RiemannSphere.affineOpenPartialHomeomorph.source ∩ (V : Set RiemannSphere) := by
        simpa [f] using
          (RiemannSphere.affineOpenPartialHomeomorph.restr_source' (s := (V : Set RiemannSphere))
            V.isOpen)
      _ = (V : Set RiemannSphere) := by
        ext x
        constructor
        · intro hx
          exact hx.2
        · intro hx
          exact ⟨hV_subset hx, hx⟩
  have h_affine_to :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.affineOpenPartialHomeomorph
        RiemannSphere.affineOpenPartialHomeomorph.source := by
    -- The affine chart is the preferred chart at any finite point of the sphere.
    simpa [RiemannSphere.chartAt_coe, extChartAt_coe, Function.comp]
      using contMDiffOn_extChartAt (I := 𝓘(ℂ)) (x := ((0 : ℂ) : RiemannSphere))
  have h_affine_inv :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.affineOpenPartialHomeomorph.symm
        RiemannSphere.affineOpenPartialHomeomorph.target := by
    -- The inverse affine chart is the inverse preferred chart at the same base point.
    simpa [RiemannSphere.chartAt_coe, extChartAt_coe_symm, Function.comp]
      using contMDiffOn_extChartAt_symm (I := 𝓘(ℂ)) (x := ((0 : ℂ) : RiemannSphere))
  have h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f f.source := by
    -- Restrict the affine chart to the open subset `V`, which already lies in the affine source.
    simpa [f] using h_affine_to.mono (by
      intro x hx
      exact hx.1)
  have h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm f.target := by
    -- The inverse branch keeps the same ambient formula on the smaller target.
    simpa [f] using h_affine_inv.mono (by
      intro z hz
      exact hz.1)
  have hSourceOpens :
      (⟨f.source, f.open_source⟩ : TopologicalSpace.Opens RiemannSphere) = V := by
    ext x
    simpa [hsource]
  have hUD :
      Nonempty
        ((⟨f.source, f.open_source⟩ : TopologicalSpace.Opens RiemannSphere) ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯
          D) := by
    simpa [D] using
      (openPartialHomeomorph_toComplexManifoldEquivSourceTarget (f := f) h_to h_inv)
  exact ⟨D, hSourceOpens ▸ hUD⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a planar holomorphic isomorphism
between open sets packages to a `C¹` manifold equivalence of the corresponding open submanifolds.
-/
lemma holomorphicIsomorph_toComplexManifoldEquiv
    {D D' : Set ℂ} (hD : IsOpen D) (hD' : IsOpen D') (e : HolomorphicIsomorph D D') :
    Nonempty ((⟨D, hD⟩ : TopologicalSpace.Opens ℂ) ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯
      (⟨D', hD'⟩ : TopologicalSpace.Opens ℂ)) := by
  have h_to_diff : DifferentiableOn ℂ (e : OpenPartialHomeomorph ℂ ℂ) D :=
    (Complex.analyticOnNhd_iff_differentiableOn hD).1 e.analyticOn_toFun
  have h_inv_diff : DifferentiableOn ℂ ((e : OpenPartialHomeomorph ℂ ℂ).symm) D' :=
    (Complex.analyticOnNhd_iff_differentiableOn hD').1 e.analyticOn_invFun
  have h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (e : OpenPartialHomeomorph ℂ ℂ) D := by
    -- Convert planar holomorphicity to chart-free `C¹` regularity on the source domain.
    simpa [contMDiffOn_iff_contDiffOn] using h_to_diff.contDiffOn hD
  have h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 ((e : OpenPartialHomeomorph ℂ ℂ).symm) D' := by
    -- The inverse branch is handled by the same analytic-to-smooth bridge on the target domain.
    simpa [contMDiffOn_iff_contDiffOn] using h_inv_diff.contDiffOn hD'
  have h_to_source :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (e : OpenPartialHomeomorph ℂ ℂ)
        (e : OpenPartialHomeomorph ℂ ℂ).source := by
    -- Re-express the source as the prescribed set `D`.
    simpa [e.source_eq] using h_to
  have h_inv_target :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 ((e : OpenPartialHomeomorph ℂ ℂ).symm)
        (e : OpenPartialHomeomorph ℂ ℂ).target := by
    -- Re-express the target as the prescribed set `D'`.
    simpa [e.target_eq] using h_inv
  have hSourceOpens :
      (⟨(e : OpenPartialHomeomorph ℂ ℂ).source, (e : OpenPartialHomeomorph ℂ ℂ).open_source⟩ :
        TopologicalSpace.Opens ℂ) = ⟨D, hD⟩ := by
    ext z
    simpa [e.source_eq]
  have hTargetOpens :
      (⟨(e : OpenPartialHomeomorph ℂ ℂ).target, (e : OpenPartialHomeomorph ℂ ℂ).open_target⟩ :
        TopologicalSpace.Opens ℂ) = ⟨D', hD'⟩ := by
    ext z
    simpa [e.target_eq]
  exact
    (by
      -- Package the underlying open partial homeomorphism and then rewrite the open-set wrappers.
      have hEq :
          Nonempty
            ((⟨(e : OpenPartialHomeomorph ℂ ℂ).source,
                (e : OpenPartialHomeomorph ℂ ℂ).open_source⟩ : TopologicalSpace.Opens ℂ) ≃ₘ^1⟮𝓘(ℂ),
              𝓘(ℂ)⟯
              (⟨(e : OpenPartialHomeomorph ℂ ℂ).target,
                (e : OpenPartialHomeomorph ℂ ℂ).open_target⟩ : TopologicalSpace.Opens ℂ)) := by
        exact
          openPartialHomeomorph_toComplexManifoldEquivSourceTarget
            (f := (e : OpenPartialHomeomorph ℂ ℂ)) h_to_source h_inv_target
      exact hSourceOpens ▸ hTargetOpens ▸ hEq)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a simply connected open subset of the
Riemann sphere is biholomorphic either to the whole sphere, to the plane, or to the unit disc. -/
lemma simplyConnectedOpenSubset_riemannSphere_uniformization
    (V : TopologicalSpace.Opens RiemannSphere) [SimplyConnectedSpace V] :
    Nonempty (V ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ RiemannSphere) ∨
      Nonempty (V ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
      Nonempty (V ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ 𝔻) := by
  by_cases hV : (V : Set RiemannSphere) = Set.univ
  · have hVOpens : V = ⟨Set.univ, isOpen_univ⟩ := by
      ext x
      simpa [hV]
    subst hVOpens
    left
    -- When the open subset is all of the sphere, the identity map already closes the theorem.
    simpa using
      (openPartialHomeomorph_toComplexManifoldEquivOfTargetEqUniv
        (f := OpenPartialHomeomorph.refl RiemannSphere)
        (by
          -- The identity branch is globally `C¹`.
          simpa using
            (contMDiff_id.contMDiffOn :
              ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun x : RiemannSphere ↦ x) Set.univ))
        (by
          -- The inverse identity branch is the same global `C¹` map.
          simpa using
            (contMDiff_id.contMDiffOn :
              ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun x : RiemannSphere ↦ x) Set.univ))
        (by simp))
  · have hp_exists : ∃ p : RiemannSphere, p ∉ (V : Set RiemannSphere) := by
      simpa [Set.eq_univ_iff_forall] using hV
    rcases hp_exists with ⟨p, hp⟩
    obtain ⟨η, -, hηp, -⟩ := RiemannSphere.point_to_infty_is_homographic_automorphism p
    let f : OpenPartialHomeomorph RiemannSphere RiemannSphere :=
      η.toHomeomorph.toOpenPartialHomeomorph.restr (V : Set RiemannSphere)
    let W : TopologicalSpace.Opens RiemannSphere := ⟨f.target, f.open_target⟩
    have hsource : f.source = (V : Set RiemannSphere) := by
      -- The restriction source is exactly `V` because the ambient automorphism is globally defined.
      calc
        f.source = η.toHomeomorph.toOpenPartialHomeomorph.source ∩ (V : Set RiemannSphere) := by
          simpa [f] using
            (η.toHomeomorph.toOpenPartialHomeomorph.restr_source'
              (s := (V : Set RiemannSphere)) V.isOpen)
        _ = (V : Set RiemannSphere) := by simp
    have h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f f.source := by
      -- Restrict the global sphere automorphism to the given open subset.
      simpa [f] using η.contMDiff.contMDiffOn.mono (by
        intro x hx
        exact Set.mem_univ x)
    have h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm f.target := by
      -- The inverse restriction stays `C¹` for the same reason.
      simpa [f] using η.symm.contMDiff.contMDiffOn.mono (by
        intro x hx
        exact Set.mem_univ x)
    have hSourceOpens :
        (⟨f.source, f.open_source⟩ : TopologicalSpace.Opens RiemannSphere) = V := by
      ext x
      simpa [hsource]
    have hVW :
        Nonempty (V ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ W) := by
      -- Package the restricted automorphism as an equivalence from `V` onto its image `W`.
      have hVW' :
          Nonempty
            ((⟨f.source, f.open_source⟩ : TopologicalSpace.Opens RiemannSphere) ≃ₘ^1⟮𝓘(ℂ),
              𝓘(ℂ)⟯ W) := by
        simpa [W] using
          openPartialHomeomorph_toComplexManifoldEquivSourceTarget (f := f) h_to h_inv
      exact hSourceOpens ▸ hVW'
    have hWinfty : OnePoint.infty ∉ (W : Set RiemannSphere) := by
      -- The chosen automorphism sends the omitted point `p` to `∞`, so `∞` is not in the image.
      intro hmem
      have hpre : f.symm OnePoint.infty ∈ f.source := f.map_target hmem
      rw [hsource] at hpre
      have hpre_eq : f.symm OnePoint.infty = p := by
        change η.symm OnePoint.infty = p
        apply η.injective
        simpa [hηp]
      exact hp (hpre_eq ▸ hpre)
    rcases hVW with ⟨eVW⟩
    haveI : SimplyConnectedSpace W := eVW.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
    rcases riemannSphereOpenSubsetAwayFromInfty_equiv_openSubsetComplex W hWinfty with
      ⟨D, hWD⟩
    rcases hWD with ⟨eWD⟩
    haveI : SimplyConnectedSpace D := eWD.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
    by_cases hD : (D : Set ℂ) = Set.univ
    · have hDOpens : D = ⟨Set.univ, isOpen_univ⟩ := by
        ext z
        simpa [hD]
      subst hDOpens
      right
      left
      -- If the affine image is all of `ℂ`, compose with the identity model of the plane.
      have hDComplex :
          Nonempty
            (((⟨Set.univ, isOpen_univ⟩ : TopologicalSpace.Opens ℂ)) ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := by
        simpa using
          (openPartialHomeomorph_toComplexManifoldEquivOfTargetEqUniv
            (f := OpenPartialHomeomorph.refl ℂ)
            (by
              -- The identity branch is globally `C¹`.
              simpa using
                (contMDiff_id.contMDiffOn :
                  ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun z : ℂ ↦ z) Set.univ))
            (by
              -- The inverse identity branch is the same global `C¹` map.
              simpa using
                (contMDiff_id.contMDiffOn :
                  ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun z : ℂ ↦ z) Set.univ))
            (by simp))
      rcases hDComplex with ⟨eDComplex⟩
      exact ⟨(eVW.trans eWD).trans eDComplex⟩
    · have hIso : Nonempty (HolomorphicIsomorph (D : Set ℂ) (Metric.ball (0 : ℂ) 1)) :=
        simply_connected_open_set_biholomorphic_to_open_unit_disc
          D.isOpen (isSimplyConnected_coe_of_simplyConnectedSpace D) hD
      rcases hIso with ⟨e⟩
      rcases holomorphicIsomorph_toComplexManifoldEquiv D.isOpen Metric.isOpen_ball e with
        ⟨eDb⟩
      right
      right
      -- In the proper affine case, invoke the planar uniformization theorem and rewrite the ball
      -- subtype as the chapter's unit-disc manifold.
      have hBallDisc :
          Nonempty
            (((⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩ : TopologicalSpace.Opens ℂ)) ≃ₘ^1⟮𝓘(ℂ),
              𝓘(ℂ)⟯ 𝔻) := by
        let ι : OpenPartialHomeomorph 𝔻 ℂ :=
          Complex.UnitDisc.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : 𝔻 → ℂ)
        have hrange :
            Set.range ((↑) : 𝔻 → ℂ) = Metric.ball (0 : ℂ) 1 := by
          ext z
          constructor
          · rintro ⟨w, rfl⟩
            simpa using Complex.UnitDisc.norm_lt_one w
          · intro hz
            exact ⟨⟨z, by simpa [Complex.UnitDisc] using hz⟩, rfl⟩
        have hι_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 ι ι.source := by
          -- The unit-disc inclusion is globally `C¹`.
          have hglobal : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 ((↑) : 𝔻 → ℂ) := by
            simpa using
              (contMDiff_isOpenEmbedding (I := 𝓘(ℂ))
                (h := Complex.UnitDisc.isOpenEmbedding_coe) (n := 1) (e := ((↑) : 𝔻 → ℂ)))
          simpa [ι] using hglobal.contMDiffOn
        have hι_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 ι.symm ι.target := by
          -- The inverse inclusion branch is `C¹` on its image.
          simpa [ι, hrange] using
            (contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℂ))
              (h := Complex.UnitDisc.isOpenEmbedding_coe) (n := 1) (e := ((↑) : 𝔻 → ℂ)))
        have hιSource :
            (⟨ι.source, ι.open_source⟩ : TopologicalSpace.Opens 𝔻) = ⟨Set.univ, isOpen_univ⟩ := by
          ext z
          simp [ι]
        have hιTarget :
            (⟨ι.target, ι.open_target⟩ : TopologicalSpace.Opens ℂ) =
              ⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩ := by
          ext z
          simp [ι, hrange]
        have hUnivBall :
            Nonempty
              (((⟨Set.univ, isOpen_univ⟩ : TopologicalSpace.Opens 𝔻)) ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯
                ((⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩ : TopologicalSpace.Opens ℂ))) := by
          have hEq :
              Nonempty
                ((⟨ι.source, ι.open_source⟩ : TopologicalSpace.Opens 𝔻) ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯
                  (⟨ι.target, ι.open_target⟩ : TopologicalSpace.Opens ℂ)) := by
            exact openPartialHomeomorph_toComplexManifoldEquivSourceTarget (f := ι) hι_to hι_inv
          exact hιSource ▸ hιTarget ▸ hEq
        have hUnivDisc :
            Nonempty (((⟨Set.univ, isOpen_univ⟩ : TopologicalSpace.Opens 𝔻)) ≃ₘ^1⟮𝓘(ℂ),
              𝓘(ℂ)⟯ 𝔻) := by
          simpa using
            (openPartialHomeomorph_toComplexManifoldEquivOfTargetEqUniv
              (f := OpenPartialHomeomorph.refl 𝔻)
              (by
                -- The identity branch on `𝔻` is globally `C¹`.
                simpa using
                  (contMDiff_id.contMDiffOn :
                    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun z : 𝔻 ↦ z) Set.univ))
              (by
                -- The inverse identity branch is the same global `C¹` map.
                simpa using
                  (contMDiff_id.contMDiffOn :
                    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (fun z : 𝔻 ↦ z) Set.univ))
              (by simp))
        rcases hUnivBall with ⟨eUnivBall⟩
        rcases hUnivDisc with ⟨eUnivDisc⟩
        exact ⟨eUnivBall.symm.trans eUnivDisc⟩
      rcases hBallDisc with ⟨eBallDisc⟩
      exact ⟨((eVW.trans eWD).trans eDb).trans eBallDisc⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: an injective local diffeomorphism is
an open embedding. This isolates the purely topological part of the final open-image packaging. -/
lemma injectiveLocalDiffeomorph_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    {f : X → Y} (hf : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 1 f) (hinj : Function.Injective f) :
    Topology.IsOpenEmbedding f := by
  -- Forget to the local-homeomorphism owner and then use injectivity.
  exact hf.isLocalHomeomorph.isOpenEmbedding_of_injective hinj

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the image of a local diffeomorphism
is an open submanifold of the target. -/
noncomputable def injectiveLocalDiffeomorph_openImage
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    {f : X → Y} (hf : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 1 f) :
    TopologicalSpace.Opens Y :=
  hf.image

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the underlying topology of an
injective local diffeomorphism already identifies the source with its open image. -/
noncomputable def injectiveLocalDiffeomorph_homeomorphOpenImage
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    {f : X → Y} (hf : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 1 f) (hinj : Function.Injective f) :
    X ≃ₜ injectiveLocalDiffeomorph_openImage (X := X) (Y := Y) hf := by
  let hEmb : Topology.IsOpenEmbedding f := injectiveLocalDiffeomorph_isOpenEmbedding hf hinj
  let g : X → injectiveLocalDiffeomorph_openImage (X := X) (Y := Y) hf :=
    fun x ↦ ⟨f x, Set.mem_range_self x⟩
  have hEmbRange : Topology.IsOpenEmbedding g := by
    -- Repackage the same open embedding with codomain restricted to the open range.
    exact Topology.IsOpenEmbedding.of_comp g
      (TopologicalSpace.Opens.isOpenEmbedding' (injectiveLocalDiffeomorph_openImage
        (X := X) (Y := Y) hf))
      (by simpa [g, injectiveLocalDiffeomorph_openImage, Function.comp] using hEmb)
  -- The codomain-restricted map is surjective by definition of the range subtype.
  exact hEmbRange.toHomeomorphOfSurjective <| by
    intro y
    rcases y.2 with ⟨x, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    simpa [g] using hx

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a connected complex charted space is
path connected because complex charts make it locally path connected. -/
lemma connectedChartedSpace_pathConnected
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [ConnectedSpace Y] :
    PathConnectedSpace Y := by
  letI : LocPathConnectedSpace Y := ChartedSpace.locPathConnectedSpace ℂ Y
  -- Complex charts supply local path connectedness, so connectedness upgrades to path
  -- connectedness.
  exact PathConnectedSpace.of_locPathConnectedSpace

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once the continuation-surface
projection is known to be a connected covering over a simply connected complex manifold, the
covering has only one sheet and is therefore bijective. -/
lemma coveringMap_bijective_of_simplyConnected
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [SimplyConnectedSpace X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [ConnectedSpace Y]
    {π : Y → X} (hπ : IsCoveringMap π) [Nonempty Y] :
    Function.Bijective π := by
  letI : LocPathConnectedSpace X := ChartedSpace.locPathConnectedSpace ℂ X
  letI : LocPathConnectedSpace Y := ChartedSpace.locPathConnectedSpace ℂ Y
  letI : PathConnectedSpace Y := connectedChartedSpace_pathConnected
  let p : C(Y, X) := ⟨π, hπ.continuous⟩
  let y0 : Y := Classical.choice inferInstance
  -- First lift `id_X` from one chosen point of the covering to obtain a global section.
  rcases hπ.existsUnique_continuousMap_lifts (f := ContinuousMap.id X) (π y0) y0 rfl with
    ⟨σ, hσ, hσ_unique⟩
  have hsurj : Function.Surjective π := by
    intro x
    refine ⟨σ x, ?_⟩
    simpa [Function.comp] using congrFun hσ.2 x
  have h_range_le : (FundamentalGroup.map p y0).range ≤
      (FundamentalGroup.mapOfEq ⟨π, hπ.continuous⟩ rfl).range := by
    rintro _ ⟨γ, rfl⟩
    refine ⟨γ, ?_⟩
    -- The basepoint-change conjugation is trivial because the chosen equality is `rfl`.
    change (CategoryTheory.Iso.refl (FundamentalGroupoid.mk (π y0))).conj
        ((FundamentalGroup.map p y0) γ) = (FundamentalGroup.map p y0) γ
    simpa using CategoryTheory.Iso.refl_conj ((FundamentalGroup.map p y0) γ)
  -- Then compare `id_Y` and `σ ∘ π` as two lifts of `π` with the same basepoint.
  rcases hπ.existsUnique_continuousMap_lifts_of_range_le
      (f := p) (a₀ := y0) (e₀ := y0) rfl h_range_le with
    ⟨F, hF, hF_unique⟩
  have h_id : (ContinuousMap.id Y) y0 = y0 ∧ π ∘ ⇑(ContinuousMap.id Y) = ⇑p := by
    constructor
    · rfl
    · rfl
  have h_sigma_comp : (σ.comp p) y0 = y0 ∧ π ∘ ⇑(σ.comp p) = ⇑p := by
    constructor
    · simpa using hσ.1
    · ext y
      simpa [p, Function.comp] using congrFun hσ.2 (π y)
  have hF_id : F = ContinuousMap.id Y := (hF_unique _ h_id).symm
  have hF_sigma : F = σ.comp p := (hF_unique _ h_sigma_comp).symm
  have hright : σ.comp p = ContinuousMap.id Y := hF_sigma.symm.trans hF_id
  have hinj : Function.Injective π := by
    intro y1 y2 hy
    have h1 : σ (π y1) = y1 := by
      simpa [p, Function.comp] using congrArg (fun g : C(Y, Y) => g y1) hright
    have h2 : σ (π y2) = y2 := by
      simpa [p, Function.comp] using congrArg (fun g : C(Y, Y) => g y2) hright
    -- Evaluating the collapsed deck transformation `σ ∘ π = id_Y` turns equal base images into
    -- equal points upstairs.
    calc
      y1 = σ (π y1) := h1.symm
      _ = σ (π y2) := by rw [hy]
      _ = y2 := h2
  exact ⟨hinj, hsurj⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the identity map is already a
covering map on any Hausdorff space. -/
lemma isCoveringMap_id {X : Type*} [TopologicalSpace X] [T2Space X] :
    IsCoveringMap (fun x : X ↦ x) := by
  intro x
  -- Each fiber is a singleton, and the identity itself provides the required local model.
  refine IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph
    (f := fun y : X ↦ y) (x := x) ?_ ?_ ?_
  · -- Closed sets stay closed under the identity map.
    intro s hs
    simpa using hs
  · -- The fiber over `x` is the singleton `{x}`, which is finite.
    simpa using (Set.toFinite ({x} : Set X))
  · -- The identity open partial homeomorphism trivializes the singleton fiber.
    intro e he
    refine ⟨OpenPartialHomeomorph.refl X, by simp, rfl⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: once `X` is biholomorphic to an open
subset of the Riemann sphere, the bridge theorem is immediate by taking `Y = X` and `π = id`. -/
lemma existsConnectedCovering_of_equivOpenRiemannSphere
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    [ConnectedSpace X] [Nonempty X]
    (hXV : ∃ V : TopologicalSpace.Opens RiemannSphere,
      Nonempty (X ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ V)) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace ℂ Y)
      (_ : IsManifold 𝓘(ℂ) 1 Y) (_ : T2Space Y) (_ : ConnectedSpace Y) (_ : Nonempty Y)
      (π : Y → X),
        IsCoveringMap π ∧ IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 1 π ∧
          ∃ V : TopologicalSpace.Opens RiemannSphere,
            Nonempty (Y ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ V) := by
  rcases hXV with ⟨V, hXV⟩
  refine ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, fun x ↦ x, ?_⟩
  refine ⟨isCoveringMap_id (X := X), ?_, ⟨V, hXV⟩⟩
  -- The identity diffeomorphism witnesses that the projection is locally biholomorphic.
  intro x
  refine
    ⟨(Diffeomorph.refl (I := 𝓘(ℂ)) (M := X) (n := 1)).toPartialDiffeomorph,
      Set.mem_univ x, ?_⟩
  intro y hy
  rfl

end
