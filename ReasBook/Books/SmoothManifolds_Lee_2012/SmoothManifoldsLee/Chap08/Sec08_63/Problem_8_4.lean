import Mathlib
import SmoothManifolds_Lee_2012.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.Chap01.Sec01_05.Proposition_1_40
import SmoothManifolds_Lee_2012.Chap05.Sec05_35.Definition_5_35_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_35.Proposition_5_41

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- `lean_leansearch` was unavailable in this session; local project precedent fixes the owner/API
-- through `SmoothManifoldWithBoundary`, `TangentSpace`, `ContMDiff ... (T% X)`, and the Chapter 5
-- predicates `IsInwardPointing` / `IsOutwardPointing` for boundary behavior.

noncomputable section

section

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [SmoothManifoldWithBoundary n M]

-- Domain sampling for this item:
-- * source-facing ambient owner: `SmoothManifoldWithBoundary n`, which equips `M` with the
--   canonical smooth structure for Lee's boundary model `leeBoundaryModelWithCorners n` in every
--   dimension;
-- * positive-dimensional bridge/view only: `SmoothManifoldWithBoundary (n + 1)` also induces the
--   half-space model `𝓡∂ (n + 1)`, but that specialization is not the source-facing owner here;
-- * core/canonical bundled section owner in the chapter/mathlib ecosystem:
--   `ContMDiffSection`, written `Cₛ^∞⟮...⟯`;
-- * derived API for the boundary behavior: `IsInwardPointing` / `IsOutwardPointing`.
-- The source problem is about arbitrary smooth manifolds with boundary, including `n = 0`, so the
-- main statement stays over `leeBoundaryModelWithCorners n`. The primitive data is just the
-- bundled smooth tangent-bundle section.

local notation "IB" => leeBoundaryModelWithCorners n
local notation "SmoothBoundaryVectorField" =>
  Cₛ^∞⟮IB; EuclideanSpace ℝ (Fin n), fun p : M ↦ TangentSpace IB p⟯

/-- Helper for Problem 8-4: the distinguished boundary-coordinate component is affine-linear in
the tangent vector argument. -/
lemma boundaryCoordinateComponent_smul_add
    {k : ℕ} [NeZero k] {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace k) N] [IsManifold (𝓡∂ k) ∞ N]
    (e : OpenPartialHomeomorph N (EuclideanHalfSpace k)) (p : N)
    (a : ℝ) (v w : TangentSpace (𝓡∂ k) p) :
    boundary_coordinate_component e p (a • v + w) =
      a * boundary_coordinate_component e p v + boundary_coordinate_component e p w := by
  let A : TangentSpace (𝓡∂ k) p →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    mfderiv (𝓡∂ k) (𝓡 k) (e.extend (𝓡∂ k)) p
  -- Evaluate the linearity identity of the chart derivative in the distinguished coordinate.
  change (A (a • v + w)) 0 = a * (A v) 0 + (A w) 0
  rw [map_add, map_smul]
  simp [A]

/-- Helper for Problem 8-4: at a boundary point, the inward-pointing vectors form a convex subset
of the tangent space. -/
lemma convex_inwardPointingVectors
    {k : ℕ} [NeZero k] {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace k) N] [IsManifold (𝓡∂ k) ∞ N]
    {p : N} (hp : p ∈ (𝓡∂ k).boundary N) :
    Convex ℝ {v : TangentSpace (𝓡∂ k) p | IsInwardPointing p v} := by
  let e : OpenPartialHomeomorph N (EuclideanHalfSpace k) := chartAt (EuclideanHalfSpace k) p
  have he : e ∈ atlas (EuclideanHalfSpace k) N := chart_mem_atlas (EuclideanHalfSpace k) p
  have hpe : p ∈ e.source := mem_chart_source (EuclideanHalfSpace k) p
  -- In boundary coordinates, inward-pointing vectors are exactly an open half-space.
  rw [convex_iff_add_mem]
  intro v hv w hw a b ha hb hab
  rw [Set.mem_setOf_eq] at hv hw ⊢
  rw [inward_pointing_iff_boundary_coordinate_component_pos hp he hpe] at hv hw ⊢
  let A : TangentSpace (𝓡∂ k) p →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    mfderiv (𝓡∂ k) (𝓡 k) (e.extend (𝓡∂ k)) p
  have hcomponent :
      boundary_coordinate_component e p (a • v + b • w) =
        a * boundary_coordinate_component e p v +
          b * boundary_coordinate_component e p w := by
    change (A (a • v + b • w)) 0 = a * (A v) 0 + b * (A w) 0
    rw [map_add, map_smul, map_smul]
    simp [A]
  rw [hcomponent]
  have hbvw_nonneg : 0 ≤ b * boundary_coordinate_component e p w := by
    exact mul_nonneg hb (le_of_lt hw)
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    rw [ha0, hb1]
    linarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hav_pos : 0 < a * boundary_coordinate_component e p v := by
      exact mul_pos ha_pos hv
    linarith

/-- Helper for Problem 8-4: on Euclidean space, the inward normal field is the constant first
standard basis vector under the canonical tangent-space identification. -/
private def boundaryModelNormalField
    {k : ℕ} (y : EuclideanSpace ℝ (Fin (k + 1))) :
    TangentSpace (𝓡 (k + 1)) y :=
  (NormedSpace.fromTangentSpace y).symm
    ((EuclideanSpace.basisFun (Fin (k + 1)) ℝ) 0)

/-- Helper for Problem 8-4: the model-space inward normal field is smooth. -/
private lemma boundaryModelNormalField_smooth
    {k : ℕ} :
    ContMDiff (𝓡 (k + 1)) (𝓡 (k + 1)).tangent ∞
      (T% (boundaryModelNormalField (k := k))) := by
  intro y
  -- On the model space, the tangent-bundle trivialization sees the field as a constant vector.
  rw [Bundle.contMDiffAt_section y]
  simpa [boundaryModelNormalField] using
    (contMDiffAt_const :
      ContMDiffAt (𝓡 (k + 1)) (𝓡 (k + 1)) ∞
        (fun _ : EuclideanSpace ℝ (Fin (k + 1)) ↦
          (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) 0) y)

/-- Helper for Problem 8-4: pull the constant inward normal basis vector back through the
boundary chart at `p`. -/
private def boundaryChartNormalField
    {k : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) N] [IsManifold (𝓡∂ (k + 1)) ∞ N]
    (p : N) :
    (y : N) → TangentSpace (𝓡∂ (k + 1)) y :=
  VectorField.mpullback (𝓡∂ (k + 1)) (𝓡 (k + 1)) (extChartAt (𝓡∂ (k + 1)) p)
    (boundaryModelNormalField (k := k))

/-- Helper for Problem 8-4: pushing the chart-normal pullback field forward through `extChartAt`
recovers the constant model-space inward normal field. -/
private lemma boundaryChartNormalField_pushforward
    {k : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) N] [IsManifold (𝓡∂ (k + 1)) ∞ N]
    (p : N) {y : N} (hy : y ∈ (chartAt (EuclideanHalfSpace (k + 1)) p).source) :
    mfderiv (𝓡∂ (k + 1)) (𝓡 (k + 1)) (extChartAt (𝓡∂ (k + 1)) p) y
      (boundaryChartNormalField (k := k) p y) =
      boundaryModelNormalField ((extChartAt (𝓡∂ (k + 1)) p) y) := by
  have hyExt : y ∈ (extChartAt (𝓡∂ (k + 1)) p).source := by
    simpa [extChartAt_source] using hy
  -- Route correction: work with the raw `mfderiv` pushforward first, so the inverse derivative in
  -- `VectorField.mpullback` cancels before any coordinate evaluation.
  simpa [boundaryChartNormalField, VectorField.mpullback_apply] using
    (isInvertible_mfderiv_extChartAt hyExt).self_apply_inverse
      (boundaryModelNormalField ((extChartAt (𝓡∂ (k + 1)) p) y))

/-- Helper for Problem 8-4: on the source of the boundary chart at `p`, the chart-normal field has
constant chart coordinates equal to the distinguished inward normal basis vector. -/
private lemma boundaryChartNormalField_inChart
    {k : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) N] [IsManifold (𝓡∂ (k + 1)) ∞ N]
    (p : N) {y : N} (hy : y ∈ (chartAt (EuclideanHalfSpace (k + 1)) p).source) :
    NormedSpace.fromTangentSpace ((extChartAt (𝓡∂ (k + 1)) p) y)
      (mfderiv (𝓡∂ (k + 1)) (𝓡 (k + 1)) (extChartAt (𝓡∂ (k + 1)) p) y
        (boundaryChartNormalField (k := k) p y)) =
      (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) 0 := by
  -- Apply the tangent-space coordinate map to the pushforward identity, reducing the statement to
  -- the defining formula for the constant model normal field.
  simpa [boundaryModelNormalField] using
    congrArg (NormedSpace.fromTangentSpace ((extChartAt (𝓡∂ (k + 1)) p) y))
      (boundaryChartNormalField_pushforward (k := k) p hy)

/-- Helper for Problem 8-4: the distinguished boundary coordinate of the chart-normal field is
constantly `1` on the source of the boundary chart at `p`. -/
private lemma boundaryCoordinateComponent_boundaryChartNormalField
    {k : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) N] [IsManifold (𝓡∂ (k + 1)) ∞ N]
    (p : N) {y : N}
    (hys : y ∈ (chartAt (EuclideanHalfSpace (k + 1)) p).source) :
    boundary_coordinate_component (chartAt (EuclideanHalfSpace (k + 1)) p) y
      (boundaryChartNormalField (k := k) p y) = 1 := by
  -- Evaluate the already-normalized chart coordinates in the distinguished boundary component.
  simpa [boundary_coordinate_component] using
    congrArg (fun w : EuclideanSpace ℝ (Fin (k + 1)) ↦ w 0)
      (boundaryChartNormalField_inChart (k := k) p hys)

/-- Helper for Problem 8-4: the chart-normal pullback field is smooth on the source of the
boundary chart at `p`. -/
private lemma boundaryChartNormalField_smoothOnSource
    {k : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) N] [IsManifold (𝓡∂ (k + 1)) ∞ N]
    (p : N) :
    ContMDiffOn (𝓡∂ (k + 1)) (𝓡∂ (k + 1)).tangent ∞
      (T% (boundaryChartNormalField (k := k) p))
      (chartAt (EuclideanHalfSpace (k + 1)) p).source := by
  intro y hy
  have hyExt : y ∈ (extChartAt (𝓡∂ (k + 1)) p).source := by
    simpa [extChartAt_source] using hy
  have hModel :
      ContMDiffWithinAt (𝓡 (k + 1)) (𝓡 (k + 1)).tangent ∞
        (T% (boundaryModelNormalField (k := k))) Set.univ
        ((extChartAt (𝓡∂ (k + 1)) p) y) :=
    (boundaryModelNormalField_smooth (k := k)).contMDiffOn _ (by simp)
  have hChart :
      ContMDiffAt (𝓡∂ (k + 1)) (𝓡 (k + 1)) ∞
        (extChartAt (𝓡∂ (k + 1)) p) y :=
    contMDiffAt_extChartAt' hy
  have hInv :
      (mfderiv (𝓡∂ (k + 1)) (𝓡 (k + 1)) (extChartAt (𝓡∂ (k + 1)) p) y).IsInvertible :=
    isInvertible_mfderiv_extChartAt hyExt
  -- Pull back the smooth constant model field through the chart, using that `univ` is a
  -- neighborhood within the chosen chart source.
  exact
    (ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin hModel hChart hInv
      (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
      (by
        simp :
          (extChartAt (𝓡∂ (k + 1)) p) ⁻¹' (Set.univ : Set (EuclideanSpace ℝ (Fin (k + 1)))) ∈
            nhdsWithin y ((chartAt (EuclideanHalfSpace (k + 1)) p).source)))

/-- Helper for Problem 8-4: the boundary-chart normal field is smooth on the chart source and
lands in the inward-pointing target set there. -/
private lemma boundaryChartNormalField_hasLocalTargetValues
    {k : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) N] [IsManifold (𝓡∂ (k + 1)) ∞ N]
    (t : ∀ x : N, Set (TangentSpace (𝓡∂ (k + 1)) x))
    (ht_boundary :
      ∀ x : N, x ∈ (𝓡∂ (k + 1)).boundary N →
        t x = {v : TangentSpace (𝓡∂ (k + 1)) x | IsInwardPointing x v})
    (ht_interior :
      ∀ x : N, x ∉ (𝓡∂ (k + 1)).boundary N → t x = Set.univ)
    {p : N} (_hp : p ∈ (𝓡∂ (k + 1)).boundary N) :
    let e : OpenPartialHomeomorph N (EuclideanHalfSpace (k + 1)) :=
      chartAt (EuclideanHalfSpace (k + 1)) p
    ContMDiffOn (𝓡∂ (k + 1)) (𝓡∂ (k + 1)).tangent ∞
        (T% (boundaryChartNormalField (k := k) p)) e.source ∧
      ∀ y ∈ e.source, boundaryChartNormalField (k := k) p y ∈ t y := by
  dsimp
  refine ⟨boundaryChartNormalField_smoothOnSource (k := k) p, ?_⟩
  intro y hy
  by_cases hyb : y ∈ (𝓡∂ (k + 1)).boundary N
  · have he : chartAt (EuclideanHalfSpace (k + 1)) p ∈ atlas (EuclideanHalfSpace (k + 1)) N :=
      chart_mem_atlas (EuclideanHalfSpace (k + 1)) p
    rw [ht_boundary y hyb]
    change IsInwardPointing y (boundaryChartNormalField (k := k) p y)
    -- Boundary points use Proposition 5.41 once the chart-normal field is normalized.
    rw [inward_pointing_iff_boundary_coordinate_component_pos hyb he hy]
    rw [boundaryCoordinateComponent_boundaryChartNormalField (k := k) p hy]
    norm_num
  · rw [ht_interior y hyb]
    simp

/-- Helper for Problem 8-4: every point has a neighborhood carrying a smooth vector field with
values in the local inward-pointing target family. -/
lemma exists_local_inwardTargetWitness
    {k : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) N] [IsManifold (𝓡∂ (k + 1)) ∞ N]
    (t : ∀ x : N, Set (TangentSpace (𝓡∂ (k + 1)) x))
    (ht_boundary :
      ∀ x : N, x ∈ (𝓡∂ (k + 1)).boundary N →
        t x = {v : TangentSpace (𝓡∂ (k + 1)) x | IsInwardPointing x v})
    (ht_interior :
      ∀ x : N, x ∉ (𝓡∂ (k + 1)).boundary N → t x = Set.univ)
    (p : N) :
    ∃ U ∈ nhds p, ∃ s_loc : (x : N) → TangentSpace (𝓡∂ (k + 1)) x,
      ContMDiffOn (𝓡∂ (k + 1)) (𝓡∂ (k + 1)).tangent ∞ (T% s_loc) U ∧
        ∀ y ∈ U, s_loc y ∈ t y := by
  -- Route correction: the global convex-gluing skeleton is already fixed. The remaining work is
  -- to package the boundary-chart normal field as a smooth local section landing in `t`, while the
  -- interior branch can then use the zero field on the boundary complement.
  by_cases hp : p ∈ (𝓡∂ (k + 1)).boundary N
  · let e : OpenPartialHomeomorph N (EuclideanHalfSpace (k + 1)) :=
      chartAt (EuclideanHalfSpace (k + 1)) p
    have hLocal :
        ContMDiffOn (𝓡∂ (k + 1)) (𝓡∂ (k + 1)).tangent ∞
            (T% (boundaryChartNormalField (k := k) p)) e.source ∧
          ∀ y ∈ e.source, boundaryChartNormalField (k := k) p y ∈ t y := by
      simpa [e] using
      boundaryChartNormalField_hasLocalTargetValues
        (k := k) (N := N) t ht_boundary ht_interior hp
    have hNhds : e.source ∈ nhds p := by
      simpa [e] using
        (chartAt (EuclideanHalfSpace (k + 1)) p).open_source.mem_nhds
          (mem_chart_source (EuclideanHalfSpace (k + 1)) p)
    -- On the boundary, use the chart-normal pullback field on the source of the preferred chart.
    refine ⟨e.source, hNhds, boundaryChartNormalField (k := k) p, ?_, ?_⟩
    · simpa [e] using hLocal.1
    · simpa [e] using hLocal.2
  · have hClosedBoundary : IsClosed ((𝓡∂ (k + 1)).boundary N) :=
      (𝓡∂ (k + 1)).isClosed_boundary (M := N) (n := ∞) (by simp)
    have hNhds : ((𝓡∂ (k + 1)).boundary N)ᶜ ∈ nhds p := by
      exact hClosedBoundary.isOpen_compl.mem_nhds hp
    let Z : (x : N) → TangentSpace (𝓡∂ (k + 1)) x := fun _ ↦ 0
    -- Off the boundary, the zero field is smooth and the target family is unconstrained.
    refine ⟨((𝓡∂ (k + 1)).boundary N)ᶜ, hNhds, Z, ?_, ?_⟩
    · simpa [Z] using
        ((0 :
          Cₛ^∞⟮𝓡∂ (k + 1); EuclideanSpace ℝ (Fin (k + 1)),
            fun x : N ↦ TangentSpace (𝓡∂ (k + 1)) x⟯).contMDiff.contMDiffOn
            (s := ((𝓡∂ (k + 1)).boundary N)ᶜ))
    · intro y hy
      rw [ht_interior y hy]
      simp [Z]

/-- Problem 8-4 (1): every smooth manifold with boundary admits a global smooth vector field whose
restriction to the boundary is everywhere inward-pointing. -/
theorem exists_smooth_vectorField_boundary_inward_pointing :
    ∃ X : SmoothBoundaryVectorField,
      ∀ p : M, p ∈ (leeBoundaryModelWithCorners n).boundary M → IsInwardPointing p (X p) := by
  cases n with
  | zero =>
      -- In dimension `0`, the boundary is empty, so the zero vector field is enough.
      refine ⟨0, ?_⟩
      intro p hp
      have hp0 : p ∈ (𝓡 0).boundary M := by
        simpa [leeBoundaryModelWithCorners] using hp
      have hempty : IsEmpty ((𝓡 0).boundary M) := inferInstance
      have hfalse : False := hempty.false ⟨p, hp0⟩
      exact False.elim hfalse
  | succ k =>
      classical
      haveI : T2Space M := inferInstance
      letI : TopologicalManifoldWithBoundary (k + 1) M := inferInstance
      letI : LocallyCompactSpace M := topologicalManifoldWithBoundary_locallyCompactSpace
      letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
      let t : ∀ x : M, Set (TangentSpace (𝓡∂ (k + 1)) x) := fun x ↦
        if hx : x ∈ (𝓡∂ (k + 1)).boundary M then
          {v : TangentSpace (𝓡∂ (k + 1)) x | IsInwardPointing x v}
        else
          Set.univ
      have ht_boundary :
          ∀ x : M, x ∈ (𝓡∂ (k + 1)).boundary M →
            t x = {v : TangentSpace (𝓡∂ (k + 1)) x | IsInwardPointing x v} := by
        intro x hx
        simp [t, hx]
      have ht_interior :
          ∀ x : M, x ∉ (𝓡∂ (k + 1)).boundary M → t x = Set.univ := by
        intro x hx
        simp [t, hx]
      have htConv : ∀ x : M, Convex ℝ (t x) := by
        intro x
        by_cases hx : x ∈ (𝓡∂ (k + 1)).boundary M
        · simpa [t, hx] using convex_inwardPointingVectors (k := k + 1) (N := M) hx
        · simpa [t, hx] using
            (convex_univ : Convex ℝ (Set.univ : Set (TangentSpace (𝓡∂ (k + 1)) x)))
      have hLocal :
          ∀ p : M, ∃ U ∈ nhds p, ∃ s_loc : (x : M) → TangentSpace (𝓡∂ (k + 1)) x,
            ContMDiffOn (𝓡∂ (k + 1)) (𝓡∂ (k + 1)).tangent ∞ (T% s_loc) U ∧
              ∀ y ∈ U, s_loc y ∈ t y :=
        exists_local_inwardTargetWitness (k := k) (N := M) t ht_boundary ht_interior
      have hGlobal :
          ∃ X : Cₛ^∞⟮𝓡∂ (k + 1); EuclideanSpace ℝ (Fin (k + 1)),
            fun p : M ↦ TangentSpace (𝓡∂ (k + 1)) p⟯,
            ∀ p : M, X p ∈ t p := by
        simpa using
          (exists_contMDiffSection_forall_mem_convex_of_local
            (I := 𝓡∂ (k + 1))
            (V := TangentSpace (𝓡∂ (k + 1))) (t := t) htConv hLocal)
      -- Globalize the local convex family of inward-pointing choices into a smooth section.
      obtain ⟨X, hXmem⟩ := hGlobal
      refine ⟨X, ?_⟩
      intro p hp
      have hXp : X p ∈ t p := hXmem p
      rw [ht_boundary p hp] at hXp
      exact hXp

/-- Problem 8-4 (2): every smooth manifold with boundary admits a global smooth vector field whose
restriction to the boundary is everywhere outward-pointing. -/
theorem exists_smooth_vectorField_boundary_outward_pointing :
    ∃ X : SmoothBoundaryVectorField,
      ∀ p : M, p ∈ (leeBoundaryModelWithCorners n).boundary M → IsOutwardPointing p (X p) := by
  cases n with
  | zero =>
      -- In dimension `0`, the boundary is empty, so the zero vector field is enough here as well.
      refine ⟨0, ?_⟩
      intro p hp
      have hp0 : p ∈ (𝓡 0).boundary M := by
        simpa [leeBoundaryModelWithCorners] using hp
      have hempty : IsEmpty ((𝓡 0).boundary M) := inferInstance
      have hfalse : False := hempty.false ⟨p, hp0⟩
      exact False.elim hfalse
  | succ k =>
      let hSmooth : SmoothManifoldWithBoundary (k + 1) M := inferInstance
      letI : SmoothManifoldWithBoundary (k + 1) M := hSmooth
      letI : ChartedSpace (ℍ^{(k + 1)}) M := hSmooth.toTopologicalManifoldWithBoundary.toChartedSpace
      have hInward :
          ∃ X : Cₛ^∞⟮𝓡∂ (k + 1); EuclideanSpace ℝ (Fin (k + 1)),
            fun p : M ↦ TangentSpace (𝓡∂ (k + 1)) p⟯,
            ∀ p : M, p ∈ (𝓡∂ (k + 1)).boundary M → IsInwardPointing p (X p) := by
        simpa [leeBoundaryModelWithCorners] using
          (exists_smooth_vectorField_boundary_inward_pointing (n := k + 1) (M := M))
      obtain ⟨X, hX⟩ := hInward
      refine ⟨?_, ?_⟩
      · simpa [leeBoundaryModelWithCorners] using
          (-X :
            Cₛ^∞⟮𝓡∂ (k + 1); EuclideanSpace ℝ (Fin (k + 1)),
              fun p : M ↦ TangentSpace (𝓡∂ (k + 1)) p⟯)
      intro p hp
      -- Negating an inward-pointing boundary field produces an outward-pointing one.
      change IsOutwardPointing p (-(X p))
      simpa using
        (inward_pointing_iff_neg_outward_pointing (p := p) (v := X p)).mp (hX p hp)

end
