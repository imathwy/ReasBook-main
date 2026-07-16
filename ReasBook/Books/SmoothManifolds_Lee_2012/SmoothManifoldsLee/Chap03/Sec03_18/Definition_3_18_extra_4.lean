import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_15.Remark_3_15_extra_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Bundle
open scoped Manifold

universe u𝕜 uE uH uM

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable (I)

/-- Definition 3.18-extra-4: a coordinate tangent vector at `p` is a choice of model-space
component in every preferred chart containing `p`, compatible under the tangent-coordinate change
maps on overlaps. This is the coordinate-family view of the canonical tangent space
`TangentSpace I p`, not a second owner type. -/
def IsCoordinateTangentVector (p : M)
    (component : {x : M // p ∈ (chartAt H x).source} → E) : Prop :=
  ∀ x y : {x : M // p ∈ (chartAt H x).source},
    tangentCoordChange I x.1 y.1 p (component x) = component y

/-- The coordinate-family realization of `TangentSpace I p` as compatible preferred-chart
components. -/
structure CoordinateTangentVector (p : M) where
  component : {x : M // p ∈ (chartAt H x).source} → E
  compatible : IsCoordinateTangentVector I p component

namespace CoordinateTangentVector

instance {p : M} : CoeFun (CoordinateTangentVector I p)
    (fun _ ↦ {x : M // p ∈ (chartAt H x).source} → E) := ⟨component⟩

@[simp] theorem component_apply {p : M} (v : CoordinateTangentVector I p)
    (x : {x : M // p ∈ (chartAt H x).source}) : v.component x = v x := rfl

theorem compatible_apply {p : M} (v : CoordinateTangentVector I p)
    (x y : {x : M // p ∈ (chartAt H x).source}) :
    tangentCoordChange I x.1 y.1 p (v x) = v y :=
  v.compatible x y

@[ext] theorem ext {p : M} {v w : CoordinateTangentVector I p}
    (h : ∀ x, v x = w x) : v = w := by
  cases v with
  | mk componentv hv =>
      cases w with
      | mk componentw hw =>
          have hcomponent : componentv = componentw := funext h
          cases hcomponent
          have hproof : hv = hw := Subsingleton.elim _ _
          cases hproof
          rfl

end CoordinateTangentVector

variable {I}

namespace TangentSpace

/-- The component of a tangent vector in the preferred chart centered at `x`, written in the model
vector space. -/
def coordinateComponent {p : M} (v : TangentSpace I p)
    (x : {x : M // p ∈ (chartAt H x).source}) : E :=
  (trivializationAt E (TangentSpace I) x.1).linearEquivAt 𝕜 p x.2 v

/-- The chart components of a tangent vector satisfy the usual coordinate transformation rule on
overlapping charts. -/
theorem coordinateComponent_isCoordinateTangentVector {p : M} (v : TangentSpace I p) :
    IsCoordinateTangentVector I p (coordinateComponent v) := by
  intro x y
  let ex := trivializationAt E (TangentSpace I) x.1
  let ey := trivializationAt E (TangentSpace I) y.1
  have hp : p ∈ ex.baseSet ∩ ey.baseSet := by
    change p ∈ (chartAt H x.1).source ∩ (chartAt H y.1).source
    exact ⟨x.2, y.2⟩
  have hchange : ex.coordChangeL 𝕜 ey p = tangentCoordChange I x.1 y.1 p := by
    simpa [ex, ey] using tangent_coordinates_change hp
  calc
    tangentCoordChange I x.1 y.1 p (coordinateComponent v x)
      = ex.coordChangeL 𝕜 ey p (coordinateComponent v x) := by
          simpa using congrArg (fun f : E →L[𝕜] E ↦ f (coordinateComponent v x)) hchange.symm
    _ = coordinateComponent v y := by
          rw [Bundle.Trivialization.coordChangeL_apply ex ey hp]
          have hx : ex.symm p (coordinateComponent v x) = v := by
            simpa [coordinateComponent, ex] using
              (ex.symm_apply_apply_mk x.2 v : ex.symm p (ex ⟨p, v⟩).2 = v)
          simpa [coordinateComponent, ey] using
            congrArg (fun w : TangentSpace I p ↦ (ey ⟨p, w⟩).2) hx

/-- The compatible preferred-chart components of a tangent vector. -/
def toCoordinateTangentVector {p : M} (v : TangentSpace I p) : CoordinateTangentVector I p :=
  ⟨coordinateComponent v, coordinateComponent_isCoordinateTangentVector v⟩

end TangentSpace

namespace CoordinateTangentVector

/-- Reconstruct a tangent vector from a compatible family of preferred-chart components by reading
the family in the preferred chart centered at the base point. -/
def toTangentSpace {p : M} (v : CoordinateTangentVector I p) : TangentSpace I p :=
  let x : {x : M // p ∈ (chartAt H x).source} := ⟨p, mem_chart_source H p⟩
  (trivializationAt E (TangentSpace I) p).symm p (v x)

@[simp] theorem coordinateComponent_toTangentSpace {p : M} (v : CoordinateTangentVector I p)
    (y : {x : M // p ∈ (chartAt H x).source}) :
    TangentSpace.coordinateComponent (toTangentSpace v) y = v y := by
  let x : {x : M // p ∈ (chartAt H x).source} := ⟨p, mem_chart_source H p⟩
  let ep := trivializationAt E (TangentSpace I) p
  let ey := trivializationAt E (TangentSpace I) y.1
  have hpy : p ∈ ep.baseSet ∩ ey.baseSet := by
    change p ∈ (chartAt H p).source ∩ (chartAt H y.1).source
    exact ⟨mem_chart_source H p, y.2⟩
  have hchange : ep.coordChangeL 𝕜 ey p = tangentCoordChange I p y.1 p := by
    simpa [ep, ey] using tangent_coordinates_change hpy
  calc
    TangentSpace.coordinateComponent (toTangentSpace v) y
      = (ey ⟨p, ep.symm p (v x)⟩).2 := by
          simp [TangentSpace.coordinateComponent, toTangentSpace, ep, ey, x]
    _ = ep.coordChangeL 𝕜 ey p (v x) := by
          symm
          exact Bundle.Trivialization.coordChangeL_apply ep ey hpy (v x)
    _ = tangentCoordChange I p y.1 p (v x) := by
          simpa using congrArg (fun f : E →L[𝕜] E ↦ f (v x)) hchange
    _ = v y := v.compatible x y

@[simp] theorem toTangentSpace_toCoordinateTangentVector {p : M} (v : TangentSpace I p) :
    toTangentSpace (TangentSpace.toCoordinateTangentVector v) = v := by
  let x : {x : M // p ∈ (chartAt H x).source} := ⟨p, mem_chart_source H p⟩
  let ep := trivializationAt E (TangentSpace I) p
  change ep.symm p ((ep ⟨p, v⟩).2) = v
  exact ep.symm_apply_apply_mk x.2 v

@[simp] theorem toCoordinateTangentVector_toTangentSpace {p : M} (v : CoordinateTangentVector I p) :
    TangentSpace.toCoordinateTangentVector (toTangentSpace v) = v := by
  ext y
  exact coordinateComponent_toTangentSpace v y

/-- The coordinate-family realization of tangent vectors is canonically equivalent to the tangent
space itself. -/
noncomputable def equivTangentSpace (p : M) : CoordinateTangentVector I p ≃ TangentSpace I p where
  toFun := toTangentSpace
  invFun := TangentSpace.toCoordinateTangentVector
  left_inv := toCoordinateTangentVector_toTangentSpace
  right_inv := toTangentSpace_toCoordinateTangentVector

end CoordinateTangentVector
