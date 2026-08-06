import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Construction_10_5_4

open CategoryTheory Limits
open scoped Topology unitInterval

noncomputable section

universe u

-- Semantic recall via `lean_leansearch`: no canonical owner surfaced for the pair-approximation
-- stage that starts from `ΓA`, wedges on generator spheres for `π_q(X)`, and then chooses
-- connecting `1`-cells by path components. The local owners `SelectedPiGenerators`,
-- `CWApproximationFirstStage`, `underTopOfPoint`, and `ZerothHomotopy` therefore give the
-- source-faithful statement surface here.

/-- The based wedge of `ΓA` with one sphere summand for each chosen generator of `π_q(X, x₀)`. -/
abbrev cwPairApproximationInitialWedge
    {X ΓA : TopCat.{u}} (x₀ : X) (γa₀ : ΓA)
    (chosenGenerators : SelectedPiGenerators (underTopOfPoint X x₀)) : BasedSpace.{u} :=
  ∐ fun j : Option chosenGenerators.generator ↦
    match j with
    | none => underTopOfPoint ΓA γa₀
    | some i => basedSphere (chosenGenerators.degree i)

/-- The basepoint path component of `cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators`. -/
abbrev cwPairApproximationInitialWedgeBaseComponent
    {X ΓA : TopCat.{u}} (x₀ : X) (γa₀ : ΓA)
    (chosenGenerators : SelectedPiGenerators (underTopOfPoint X x₀)) :
    ZerothHomotopy (cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators).right :=
  ⟦underTopBasepoint (cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators)⟧

/-- The non-basepoint path components of the initial wedge in Construction 10.6.4. These index
the connecting `1`-cells. -/
abbrev cwPairApproximationInitialWedgeNonBasepointComponent
    {X ΓA : TopCat.{u}} (x₀ : X) (γa₀ : ΓA)
    (chosenGenerators : SelectedPiGenerators (underTopOfPoint X x₀)) : Type u :=
  {c : ZerothHomotopy (cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators).right //
    c ≠ cwPairApproximationInitialWedgeBaseComponent x₀ γa₀ chosenGenerators}

/-- The canonical map from the initial wedge in Construction 10.6.4 to `X`, obtained by descending
the given map `ΓA → X` and the sphere maps representing the chosen generators. -/
abbrev cwPairApproximationInitialWedgeToTarget
    {X ΓA : TopCat.{u}} (x₀ : X) (γa₀ : ΓA)
    (fA : underTopOfPoint ΓA γa₀ ⟶ underTopOfPoint X x₀)
    (chosenGenerators : SelectedPiGenerators (underTopOfPoint X x₀))
    (sphereStage :
      CWApproximationFirstStage (underTopOfPoint X x₀) chosenGenerators) :
    cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators ⟶ underTopOfPoint X x₀ :=
  Limits.Sigma.desc fun j : Option chosenGenerators.generator ↦
    match j with
    | none => fA
    | some i => sphereStage.representingMap i

/-- The boundary object `S⁰` for one connecting `1`-cell in Construction 10.6.4, modeled as two
copies of `PUnit`. -/
abbrev cwPairApproximationConnectingBoundary : TopCat.{u} :=
  TopCat.of (ULift.{u, 0} PUnit ⊕ ULift.{u, 0} PUnit)

/-- The interval object `D¹` for one connecting `1`-cell in Construction 10.6.4. -/
abbrev cwPairApproximationConnectingInterval : TopCat.{u} :=
  TopCat.of (ULift.{u} I)

/-- The endpoint inclusion `S⁰ ⟶ D¹` used for each connecting `1`-cell. -/
abbrev cwPairApproximationConnectingBoundaryInclusion :
    cwPairApproximationConnectingBoundary ⟶ cwPairApproximationConnectingInterval :=
  TopCat.ofHom
    { toFun :=
        Sum.elim
          (fun _ : ULift.{u, 0} PUnit ↦ (ULift.up (0 : I)))
          (fun _ : ULift.{u, 0} PUnit ↦ (ULift.up (1 : I)))
      continuous_toFun :=
        Continuous.sumElim
          (ContinuousMap.const (ULift.{u, 0} PUnit) (ULift.up (0 : I))).continuous
          (ContinuousMap.const (ULift.{u, 0} PUnit) (ULift.up (1 : I))).continuous }

/-- The coproduct of the boundary objects of all connecting `1`-cells in Construction 10.6.4. -/
abbrev cwPairApproximationConnectingBoundaryFamily (J : Type u) : TopCat.{u} :=
  ∐ fun _ : J ↦ cwPairApproximationConnectingBoundary

/-- The coproduct of the interval objects of all connecting `1`-cells in Construction 10.6.4. -/
abbrev cwPairApproximationConnectingIntervalFamily (J : Type u) : TopCat.{u} :=
  ∐ fun _ : J ↦ cwPairApproximationConnectingInterval

/-- The coproduct of the endpoint inclusions `S⁰ ⟶ D¹` for all connecting `1`-cells. -/
abbrev cwPairApproximationConnectingBoundaryFamilyInclusion (J : Type u) :
    cwPairApproximationConnectingBoundaryFamily J ⟶
      cwPairApproximationConnectingIntervalFamily J :=
  Limits.Sigma.desc fun j : J ↦
    cwPairApproximationConnectingBoundaryInclusion ≫
      Sigma.ι (fun _ : J ↦ cwPairApproximationConnectingInterval) j

/-- The attaching map sending one endpoint of each connecting `1`-cell to the wedge basepoint and
the other endpoint to the chosen non-basepoint endpoint. -/
abbrev cwPairApproximationConnectingBoundaryMap
    {X ΓA : TopCat.{u}} (x₀ : X) (γa₀ : ΓA)
    (chosenGenerators : SelectedPiGenerators (underTopOfPoint X x₀))
    {J : Type u}
    (connectingEndpoint :
      J → (cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators).right) :
    cwPairApproximationConnectingBoundaryFamily J ⟶
      (cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators).right :=
  Limits.Sigma.desc fun j : J ↦
    TopCat.ofHom
      { toFun :=
        Sum.elim
            (fun _ : ULift.{u, 0} PUnit ↦
              underTopBasepoint (cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators))
            (fun _ : ULift.{u, 0} PUnit ↦ connectingEndpoint j)
        continuous_toFun :=
          Continuous.sumElim
            (ContinuousMap.const (ULift.{u, 0} PUnit)
              (underTopBasepoint
                (cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators))).continuous
            (ContinuousMap.const (ULift.{u, 0} PUnit) (connectingEndpoint j)).continuous }

/-- The interval map to `X` determined by the chosen connecting paths for the added `1`-cells. -/
abbrev cwPairApproximationConnectingPathMap
    {X : TopCat.{u}} (x₀ : X) {J : Type u} {endpoint : J → X}
    (connectingPath : ∀ j : J, Path x₀ (endpoint j)) :
    cwPairApproximationConnectingIntervalFamily J ⟶ X :=
  Limits.Sigma.desc fun j : J ↦
    TopCat.ofHom
      { toFun := fun t : ULift I ↦ (connectingPath j).toContinuousMap t.down
        continuous_toFun :=
          (connectingPath j).toContinuousMap.continuous.comp continuous_uliftDown }

/-- Construction 10.6.4: fixing a based map `fA : ΓA → X`, a chosen point `γa₀ : ΓA`, and a
basepoint `x₀ : X`, the initial connected stage in constructing `ΓX` from `ΓA` is obtained by
wedging `ΓA` with one sphere `S^q` for each chosen generator of `π_q(X, x₀)`, then adjoining one
connecting `1`-cell indexed by each non-basepoint path component of that wedge. This structure
records the initial wedge, the chosen boundary endpoints of those connecting `1`-cells,
explicit chosen paths in `X` for those cells, and a post-attachment stage specified as the
corresponding topological pushout together with its map to `X`. -/
structure CWPairApproximationInitialConnectedStage
    (X ΓA : TopCat.{u}) (x₀ : X) (γa₀ : ΓA)
    (fA : underTopOfPoint ΓA γa₀ ⟶ underTopOfPoint X x₀) where
  /-- The chosen generators of the homotopy groups `π_q(X, x₀)` used for the first wedge stage. -/
  chosenGenerators : SelectedPiGenerators (underTopOfPoint X x₀)
  /-- The sphere summands and chosen maps from those summands into `X` used for the first wedge
  stage. -/
  sphereStage :
    CWApproximationFirstStage (underTopOfPoint X x₀) chosenGenerators
  /-- For each non-basepoint path component of the initial wedge, the chosen non-basepoint
  endpoint of the connecting `1`-cell attached to that component. -/
  connectingEndpoint :
    cwPairApproximationInitialWedgeNonBasepointComponent x₀ γa₀ chosenGenerators →
      (cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators).right
  /-- The chosen endpoint of the connecting `1`-cell indexed by a non-basepoint component lies in
  that component. -/
  connectingEndpoint_component :
    ∀ j : cwPairApproximationInitialWedgeNonBasepointComponent x₀ γa₀ chosenGenerators,
      ⟦connectingEndpoint j⟧ = j.1
  /-- For each non-basepoint path component of the initial wedge, a chosen path in `X` from the
  basepoint `x₀` to the image of the selected non-basepoint endpoint of the corresponding
  connecting `1`-cell. -/
  connectingPath :
    ∀ j : cwPairApproximationInitialWedgeNonBasepointComponent x₀ γa₀ chosenGenerators,
      Path (underTopBasepoint (underTopOfPoint X x₀))
        ((cwPairApproximationInitialWedgeToTarget x₀ γa₀ fA chosenGenerators
          sphereStage).right.hom (connectingEndpoint j))
  /-- The actual post-attachment based space obtained after adjoining the chosen connecting
  `1`-cells to the initial wedge. -/
  connectedStage : BasedSpace.{u}
  /-- The canonical map from the initial wedge into the post-attachment connected stage. -/
  initialWedgeInclusion :
    cwPairApproximationInitialWedge x₀ γa₀ chosenGenerators ⟶ connectedStage
  /-- The canonical map from the coproduct of the attached intervals into the post-attachment
  stage. -/
  connectingIntervalInclusion :
    cwPairApproximationConnectingIntervalFamily
      (cwPairApproximationInitialWedgeNonBasepointComponent x₀ γa₀ chosenGenerators) ⟶
        connectedStage.right
  /-- The post-attachment stage is obtained from the initial wedge by adjoining the chosen
  connecting `1`-cells, formalized as the pushout of the endpoint inclusions into the intervals
  and the attaching map sending one endpoint to the wedge basepoint and the other to the chosen
  connecting endpoint. -/
  attachment_isPushout :
    IsPushout
      (cwPairApproximationConnectingBoundaryMap x₀ γa₀ chosenGenerators connectingEndpoint)
      (cwPairApproximationConnectingBoundaryFamilyInclusion
        (cwPairApproximationInitialWedgeNonBasepointComponent x₀ γa₀ chosenGenerators))
      initialWedgeInclusion.right
      connectingIntervalInclusion
  /-- The post-attachment connected stage maps to `X`. -/
  connectedStageToTarget :
    connectedStage ⟶ underTopOfPoint X x₀
  /-- On the initial wedge, the post-attachment map to `X` agrees with the map determined by
  `fA` and the chosen sphere representatives. -/
  initialWedgeInclusion_comp_connectedStageToTarget :
    initialWedgeInclusion ≫ connectedStageToTarget =
      cwPairApproximationInitialWedgeToTarget x₀ γa₀ fA chosenGenerators sphereStage
  /-- On each attached interval, the map to `X` is the chosen path for that connecting
  `1`-cell. -/
  connectingIntervalInclusion_comp_connectedStageToTarget :
    connectingIntervalInclusion ≫ connectedStageToTarget.right =
      cwPairApproximationConnectingPathMap
        (underTopBasepoint (underTopOfPoint X x₀))
        connectingPath
  /-- The post-attachment stage is connected. -/
  connectedStage_connected : ConnectedSpace connectedStage.right

/- The initial wedge in Construction 10.6.4 is `ΓA` together with the chosen generator spheres of
`π_q(X, x₀)`. -/
namespace CWPairApproximationInitialConnectedStage

variable {X ΓA : TopCat.{u}} {x₀ : X} {γa₀ : ΓA}
variable {fA : underTopOfPoint ΓA γa₀ ⟶ underTopOfPoint X x₀}

abbrev initialWedge (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) :
    BasedSpace.{u} :=
  cwPairApproximationInitialWedge x₀ γa₀ S.chosenGenerators

/-- The connecting `1`-cells of `S`, indexed by the non-basepoint path components of its initial
wedge. -/
abbrev connectingCell (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) : Type u :=
  cwPairApproximationInitialWedgeNonBasepointComponent x₀ γa₀ S.chosenGenerators

/-- A `CWPairApproximationInitialConnectedStage` canonically coerces to its underlying
post-attachment connected stage. -/
instance instCoeToBasedSpace :
    CoeTC (CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) BasedSpace.{u} where
  coe S := S.connectedStage

/-- The post-attachment stage in Construction 10.6.4 is connected. -/
instance instConnectedSpace
    (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) :
    ConnectedSpace S.connectedStage.right :=
  S.connectedStage_connected

/-- The initial wedge of Construction 10.6.4 maps to `X` by descending the given map `ΓA → X`
and the sphere maps representing the chosen generators. -/
abbrev initialWedgeToTarget
    (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) :
    S.initialWedge ⟶ underTopOfPoint X x₀ :=
  cwPairApproximationInitialWedgeToTarget x₀ γa₀ fA S.chosenGenerators S.sphereStage

/-- The attaching map for the connecting `1`-cells sends one endpoint of each interval to the
wedge basepoint and the other to the chosen connecting endpoint. -/
abbrev connectingBoundaryMap
    (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) :
    cwPairApproximationConnectingBoundaryFamily S.connectingCell ⟶ S.initialWedge.right :=
  cwPairApproximationConnectingBoundaryMap x₀ γa₀ S.chosenGenerators S.connectingEndpoint

/-- The attached intervals map to `X` by the chosen connecting paths. -/
abbrev connectingPathMap
    (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) :
    cwPairApproximationConnectingIntervalFamily S.connectingCell ⟶ X :=
  cwPairApproximationConnectingPathMap x₀ S.connectingPath

/-- The connected stage of Construction 10.6.4 maps to `X`, extending the map from the initial
wedge. -/
abbrev toTarget (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) :
    S.connectedStage ⟶ underTopOfPoint X x₀ :=
  S.connectedStageToTarget

/-- The chosen attachment square for the connecting `1`-cells is a pushout square. -/
theorem isPushout (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) :
    IsPushout
      S.connectingBoundaryMap
      (cwPairApproximationConnectingBoundaryFamilyInclusion S.connectingCell)
      S.initialWedgeInclusion.right
      S.connectingIntervalInclusion :=
  S.attachment_isPushout

/-- On the initial wedge, the attached-stage map to `X` agrees with the original wedge map. -/
@[simp] theorem initialWedgeInclusion_comp_toTarget
    (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) :
    S.initialWedgeInclusion ≫ S.toTarget = S.initialWedgeToTarget :=
  S.initialWedgeInclusion_comp_connectedStageToTarget

/-- On each attached interval, the attached-stage map to `X` is the chosen connecting path. -/
@[simp] theorem connectingIntervalInclusion_comp_toTarget
    (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA) :
    S.connectingIntervalInclusion ≫ S.toTarget.right = S.connectingPathMap :=
  S.connectingIntervalInclusion_comp_connectedStageToTarget

/-- If the chosen sphere maps in the first wedge stage realize the selected generators relative to
`comparison`, then the sphere summand indexed by `i` in Construction 10.6.4 represents the chosen
generator of `π_q(X, x₀)` indexed by `i`. -/
theorem representsGenerator
    (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA)
    (comparison :
      ∀ i : S.chosenGenerators.generator,
        HurewiczComparison (S.chosenGenerators.degree i) (underTopOfPoint X x₀))
    (hSphereStage : S.sphereStage.representsChosenGenerators comparison)
    (i : S.chosenGenerators.generator) :
    sphereMapRepresentsPiElement
      (comparison i)
      (S.chosenGenerators.piElement i)
      (S.sphereStage.representingMap i) :=
  hSphereStage i

/-- Every non-basepoint path component of the initial wedge in Construction 10.6.4 is assigned a
connecting `1`-cell. -/
theorem exists_connectingCell
    (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA)
    (c : ZerothHomotopy S.initialWedge.right)
    (hc : c ≠ cwPairApproximationInitialWedgeBaseComponent x₀ γa₀ S.chosenGenerators) :
    ∃ j : S.connectingCell, j.1 = c :=
  ⟨⟨c, hc⟩, rfl⟩

/-- Every non-basepoint path component of the initial wedge indexes a unique connecting `1`-cell. -/
theorem exists_connectingCell_component
    (S : CWPairApproximationInitialConnectedStage X ΓA x₀ γa₀ fA)
    (c : ZerothHomotopy S.initialWedge.right)
    (hc : c ≠ cwPairApproximationInitialWedgeBaseComponent x₀ γa₀ S.chosenGenerators) :
    ∃! j : S.connectingCell, j.1 = c := by
  refine ⟨⟨c, hc⟩, rfl, ?_⟩
  intro j hj
  apply Subtype.ext
  exact hj

end CWPairApproximationInitialConnectedStage
