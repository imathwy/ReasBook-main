import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Reformulation_7_1_4

open scoped unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- A continuous path lifting function for `p : C(E, B)` is a bundled continuous lift of the
universal path-space square over `MappingPathSpace p`. -/
structure ContinuousPathLiftingFunction (p : C(E, B)) where
  toContinuousMap : C(MappingPathSpace p, C(I, E))
  source_eq (x : MappingPathSpace p) : toContinuousMap x 0 = x.point
  proj_comp_eq (x : MappingPathSpace p) : p ∘ toContinuousMap x = x.path

namespace ContinuousPathLiftingFunction

variable {p : C(E, B)}

/-- Forgetting continuity recovers the ordinary path lifting function associated to `s`. -/
def toPathLiftingFunction (s : ContinuousPathLiftingFunction p) : PathLiftingFunction p where
  toFun := s.toContinuousMap
  source_eq := s.source_eq
  proj_comp_eq := s.proj_comp_eq

end ContinuousPathLiftingFunction

/-- A map `p` admits a path lifting function when the universal mapping-path-space square admits
a continuous lift into `E^I`. This is the source-facing path-lifting criterion used in
Criterion 7.2.3. -/
def AdmitsPathLiftingFunction (p : C(E, B)) : Prop :=
  Nonempty (ContinuousPathLiftingFunction p)

/-- Admitting a path lifting function is exactly the existence of a continuous path lifting
function on the universal mapping-path-space square. -/
theorem admitsPathLiftingFunction_iff_nonempty_continuousPathLiftingFunction (p : C(E, B)) :
    AdmitsPathLiftingFunction p ↔ Nonempty (ContinuousPathLiftingFunction p) := by
  -- This is just the defining expansion of `AdmitsPathLiftingFunction`.
  rfl

/-- A map admitting a path lifting function in the criterion sense also admits an ordinary path
lifting function in the sense of Definition 7.2.2. -/
theorem nonempty_pathLiftingFunction_of_admitsPathLiftingFunction (p : C(E, B)) :
    AdmitsPathLiftingFunction p → Nonempty (PathLiftingFunction p) := by
  -- Unpack the continuous lift and forget continuity.
  intro h
  rcases h with ⟨s⟩
  exact ⟨s.toPathLiftingFunction⟩

/-- Helper for Criterion 7.2.3: the point projection `MappingPathSpace p → E` is continuous. -/
theorem mappingPathSpacePointContinuous (p : C(E, B)) :
    Continuous fun x : MappingPathSpace p ↦ x.point := by
  -- The point coordinate is the first projection from the defining subtype.
  simpa [MappingPathSpace.point] using
    (continuous_fst.comp (MappingPathSpace.continuous_subtypeVal (p := p)) :
      Continuous fun x : MappingPathSpace p ↦ ((x : E × C(I, B)).1))

/-- Helper for Criterion 7.2.3: the path projection `MappingPathSpace p → C(I, B)` is
continuous. -/
theorem mappingPathSpacePathContinuous (p : C(E, B)) :
    Continuous fun x : MappingPathSpace p ↦ x.path := by
  -- The path coordinate is the second projection from the defining subtype.
  simpa [MappingPathSpace.path] using
    (continuous_snd.comp (MappingPathSpace.continuous_subtypeVal (p := p)) :
      Continuous fun x : MappingPathSpace p ↦ ((x : E × C(I, B)).2))

variable [WeaklyHausdorffSpace.{u, u} E]
variable [WeaklyHausdorffSpace.{v, v} B]

namespace HasCoveringHomotopyProperty

/-- In the path-space reformulation, a map `p` has the covering homotopy property exactly when it
admits a continuous path lifting function. Definition 7.1.2 packages surjectivity separately into
`IsFibration`. -/
theorem iff_nonempty_continuousPathLiftingFunction (p : C(E, B)) :
    HasCoveringHomotopyProperty.{u, v, max u v} p ↔
      Nonempty (ContinuousPathLiftingFunction p) := by
  let _ : CompactlyGeneratedWeakHausdorffSpace (MappingPathSpace p) :=
    mappingPathSpaceCompactlyGeneratedWeakHausdorffSpace p
  constructor
  · intro hp
    let pointMap : C(MappingPathSpace p, E) :=
      ⟨fun x ↦ x.point, mappingPathSpacePointContinuous p⟩
    let pathMap : C(MappingPathSpace p, C(I, B)) :=
      ⟨fun x ↦ x.path, mappingPathSpacePathContinuous p⟩
    have hsquare : (pathSpaceEvalAtZero B).comp pathMap = p.comp pointMap := by
      -- The universal square commutes because each stored path starts at `p x.point`.
      apply ContinuousMap.ext
      intro x
      simpa [pointMap, pathMap] using x.path_zero_eq
    obtain ⟨D, hD₀, hDproj⟩ :=
      (hasCoveringHomotopyProperty_iff_lift_pathSpaceEvalAtZero (p := p)).1 hp pointMap pathMap
        hsquare
    have hsource (x : MappingPathSpace p) : D x 0 = x.point := by
      -- Evaluating the lifted family at `0` recovers the stored starting point.
      simpa [pointMap] using ContinuousMap.congr_fun hD₀ x
    have hproj (x : MappingPathSpace p) : p ∘ D x = x.path := by
      -- Postcomposing the lifted path with `p` recovers the stored path in `B`.
      funext t
      simpa [pathMap, pathSpacePostcompose] using
        ContinuousMap.congr_fun (ContinuousMap.congr_fun hDproj x) t
    exact ⟨
      { toContinuousMap := D
        source_eq := hsource
        proj_comp_eq := hproj }⟩
  · rintro ⟨s⟩
    refine (hasCoveringHomotopyProperty_iff_lift_pathSpaceEvalAtZero (p := p)).2 ?_
    intro A _ _ g₀ d hd
    have hstart (a : A) : d a 0 = p (g₀ a) := by
      -- Pointwise, the commutative square says the path starts over `p (g₀ a)`.
      simpa using ContinuousMap.congr_fun hd a
    have hfamilyMem (a : A) :
        ((g₀ a, d a) : E × C(I, B)).2 0 = p (((g₀ a, d a) : E × C(I, B)).1) := by
      -- Rephrase the compatibility equation in the ambient product used by the subtype.
      simpa using hstart a
    have hfamilyContinuous :
        Continuous fun a : A ↦ MappingPathSpace.mk (g₀ a) (d a) (hfamilyMem a) := by
      -- A compatible pair `(g₀ a, d a)` lands continuously in the mapping path space.
      exact MappingPathSpace.continuous_mk g₀.continuous d.continuous hfamilyMem
    let family : C(A, MappingPathSpace p) :=
      ⟨fun a ↦ MappingPathSpace.mk (g₀ a) (d a) (hfamilyMem a), hfamilyContinuous⟩
    let D : C(A, C(I, E)) := s.toContinuousMap.comp family
    have hD₀ : (pathSpaceEvalAtZero E).comp D = g₀ := by
      -- The chosen continuous lift starts at the specified point.
      apply ContinuousMap.ext
      intro a
      simpa [D, family] using s.source_eq (family a)
    have hDproj : (pathSpacePostcompose p).comp D = d := by
      -- The chosen continuous lift projects to the prescribed path family.
      apply ContinuousMap.ext
      intro a
      ext t
      simpa [D, family, pathSpacePostcompose] using
        congrArg (fun γ : I → B ↦ γ t) (s.proj_comp_eq (family a))
    exact ⟨D, hD₀, hDproj⟩

/-- A map admitting a continuous path lifting function has the covering homotopy property. -/
instance instOfNonemptyContinuousPathLiftingFunction (p : C(E, B))
    [Nonempty (ContinuousPathLiftingFunction p)] :
    HasCoveringHomotopyProperty.{u, v, max u v} p :=
  (iff_nonempty_continuousPathLiftingFunction p).2 inferInstance

end HasCoveringHomotopyProperty

namespace IsFibration

/-- Criterion 7.2.3 in the local API. Since Definition 7.1.2 packages surjectivity into
`IsFibration` separately from the covering homotopy property, a path-lifting function must be
accompanied by surjectivity. -/
theorem iff_admitsPathLiftingFunction (p : C(E, B)) :
    IsFibration.{u, v, max u v} p ↔
      Function.Surjective p ∧ AdmitsPathLiftingFunction p := by
  constructor
  · intro hp
    have hpath : Nonempty (ContinuousPathLiftingFunction p) :=
      (HasCoveringHomotopyProperty.iff_nonempty_continuousPathLiftingFunction p).1
        hp.toHasCoveringHomotopyProperty
    -- A fibration contributes surjectivity and the universal continuous path lift.
    exact ⟨hp.surjective, (admitsPathLiftingFunction_iff_nonempty_continuousPathLiftingFunction p).2
      hpath⟩
  · rintro ⟨hsurj, hadmits⟩
    have hpath : Nonempty (ContinuousPathLiftingFunction p) :=
      (admitsPathLiftingFunction_iff_nonempty_continuousPathLiftingFunction p).1 hadmits
    have hchp : HasCoveringHomotopyProperty.{u, v, max u v} p :=
      (HasCoveringHomotopyProperty.iff_nonempty_continuousPathLiftingFunction p).2 hpath
    -- Repackage surjectivity together with the recovered covering homotopy property.
    exact
      { toHasCoveringHomotopyProperty := hchp
        surjective := hsurj }

/-- Expanding `AdmitsPathLiftingFunction` and Definition 7.1.2, a map `p` is a fibration exactly
when it is surjective and admits a continuous path lifting function. -/
theorem iff_surjective_and_nonempty_continuousPathLiftingFunction (p : C(E, B)) :
    IsFibration.{u, v, max u v} p ↔
      Function.Surjective p ∧ Nonempty (ContinuousPathLiftingFunction p) := by
  constructor
  · intro hp
    rcases (iff_admitsPathLiftingFunction p).1 hp with ⟨hsurj, hadmits⟩
    -- Expand the path-lifting criterion to the continuous witness it abbreviates.
    exact
      ⟨hsurj,
        (admitsPathLiftingFunction_iff_nonempty_continuousPathLiftingFunction p).1 hadmits⟩
  · rintro ⟨hsurj, hpath⟩
    -- Recompress the continuous witness into the criterion statement from above.
    exact (iff_admitsPathLiftingFunction p).2
      ⟨hsurj, (admitsPathLiftingFunction_iff_nonempty_continuousPathLiftingFunction p).2 hpath⟩

/-- A surjective map admitting a continuous path lifting function is a fibration. -/
instance instOfSurjectiveAndNonemptyContinuousPathLiftingFunction (p : C(E, B))
    (hsurj : Function.Surjective p) [Nonempty (ContinuousPathLiftingFunction p)] :
    IsFibration.{u, v, max u v} p :=
  (iff_surjective_and_nonempty_continuousPathLiftingFunction p).2 ⟨hsurj, inferInstance⟩

end IsFibration
