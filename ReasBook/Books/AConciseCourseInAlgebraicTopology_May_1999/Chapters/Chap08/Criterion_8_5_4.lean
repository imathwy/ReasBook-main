import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_3_4

open CategoryTheory
open scoped unitInterval

noncomputable section

/-- Helper for Criterion 8.5.4: a based map sends the chosen basepoint of its source to the
chosen basepoint of its target. -/
private theorem criterion_map_underTopBasepoint {A X : BasedSpace} (i : A ⟶ X) :
    i.right.hom (underTopBasepoint A) = underTopBasepoint X := by
  -- Evaluate the `Under` commutativity condition at the unique point of the terminal object.
  have hw :=
    congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      (Under.w i)
  simpa [underTopBasepoint] using hw

/-- Helper for Criterion 8.5.4: a continuous map carrying the source basepoint to a chosen point
packages as a based map. -/
private def criterionBasedMapOfMapAtBasepoint {Z : BasedSpace} {S : TopCat}
    (f : C(Z.right, S)) (b : S)
    (hf : f (underTopBasepoint Z) = b) :
    Z ⟶ basedSpaceAtPoint S b :=
  Under.homMk (TopCat.ofHom f) (by
    -- Two terminal-domain maps agree once they agree on the unique point.
    ext u
    have hu : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
      cases h : TopCat.terminalIsoPUnit.hom u
      rfl
    have hu' : u = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u) := by
      exact (congrArg (fun g ↦ g u) TopCat.terminalIsoPUnit.hom_inv_id).symm
    calc
      (Z.hom ≫ TopCat.ofHom f) u = f (Z.hom u) := rfl
      _ = f (Z.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u))) := by
        rw [hu']
      _ = f (Z.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)) := by
        rw [hu]
      _ = b := hf
      _ = (basedSpaceAtPoint S b).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
      _ = (basedSpaceAtPoint S b).hom
            (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u)) := by
            rw [hu]
      _ = (basedSpaceAtPoint S b).hom u := by
            simp)

/-- Helper for Criterion 8.5.4: the underlying continuous map of `basedMapOfMapAtBasepoint` is
the original continuous map. -/
@[simp] private theorem criterionBasedMapOfMapAtBasepoint_hom {Z : BasedSpace} {S : TopCat}
    (f : C(Z.right, S)) (b : S) (hf : f (underTopBasepoint Z) = b) :
    (criterionBasedMapOfMapAtBasepoint f b hf).right.hom = f := by
  rfl

/-- Helper for Criterion 8.5.4: a continuous map into an existing based space packages as a based
map once it preserves the chosen basepoint. -/
def basedMapOfMapToBasedSpace {Z E : BasedSpace} (f : C(Z.right, E.right))
    (hf : f (underTopBasepoint Z) = underTopBasepoint E) :
    Z ⟶ E :=
  Under.homMk (TopCat.ofHom f) (by
    -- Two terminal-domain maps into `E` agree once they agree at the unique point.
    ext u
    have hu : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
      cases h : TopCat.terminalIsoPUnit.hom u
      rfl
    have hu' : u = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u) := by
      exact (congrArg (fun g ↦ g u) TopCat.terminalIsoPUnit.hom_inv_id).symm
    calc
      (Z.hom ≫ TopCat.ofHom f) u = f (Z.hom u) := rfl
      _ = f (Z.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u))) := by
        rw [hu']
      _ = f (Z.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)) := by
        rw [hu]
      _ = underTopBasepoint E := hf
      _ = E.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
      _ = E.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u)) := by
        rw [hu]
      _ = E.hom u := by
        simp)

/-- Helper for Criterion 8.5.4: the underlying continuous map of
`basedMapOfMapToBasedSpace` is the original map. -/
@[simp] theorem basedMapOfMapToBasedSpace_hom {Z E : BasedSpace} (f : C(Z.right, E.right))
    (hf : f (underTopBasepoint Z) = underTopBasepoint E) :
    (basedMapOfMapToBasedSpace f hf).right.hom = f := by
  rfl

/-- Helper for Criterion 8.5.4: an explicit path family with prescribed endpoints and singleton
basepoint constancy determines a based relative homotopy. -/
private def criterionHomotopyRelOfPathFamily {A B : BasedSpace} {f₀ f₁ : C(A.right, B.right)}
    (d : C(A.right, C(I, B.right)))
    (h₀ : ∀ a : A.right, d a 0 = f₀ a)
    (h₁ : ∀ a : A.right, d a 1 = f₁ a)
    (hrel : ∀ a : A.right, a ∈ basedBasepointSet A →
      d a = ContinuousMap.const I (f₀ a)) :
    f₀ HRel[A] f₁ := by
  -- Uncurrying the path family produces the underlying homotopy.
  refine
    { toHomotopy := ?_
      prop' := ?_ }
  · refine
      { toFun := fun p ↦ d p.2 p.1
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }
    · -- The compact-open adjunction packages continuity of `d` into continuity on `I × A`.
      exact
        (ContinuousMap.continuous_uncurry_of_continuous d).comp
          (Homeomorph.prodComm I A.right).continuous_toFun
    · intro a
      simpa using h₀ a
    · intro a
      simpa using h₁ a
  · intro t a ha
    -- On the singleton basepoint subset, the path family is literally constant.
    have hconst := hrel a ha
    simp [hconst]

/-- The based mapping path space `N_p` from Definition 8.5.3, specialized to a based map
`p : E ⟶ B`. It stores a point of `E` together with a path in `B` starting at its image under
`p`. -/
def BasedMappingPathSpace {E B : BasedSpace} (p : E ⟶ B) : Type _ :=
  { xγ : E.right × C(I, B.right) // xγ.2 0 = p.right.hom xγ.1 }

namespace BasedMappingPathSpace

variable {E B : BasedSpace} {p : E ⟶ B}

@[reducible] instance instTopologicalSpace (p : E ⟶ B) :
    TopologicalSpace (BasedMappingPathSpace p) :=
  TopologicalSpace.induced Subtype.val inferInstance

/-- The point of `E` underlying an element of `N_p`. -/
def point (x : BasedMappingPathSpace p) : E.right :=
  x.1.1

/-- The path in `B` underlying an element of `N_p`. -/
def path (x : BasedMappingPathSpace p) : C(I, B.right) :=
  x.1.2

/-- The source condition defining `N_p`. -/
theorem source_eq (x : BasedMappingPathSpace p) :
    x.path 0 = p.right.hom x.point :=
  x.2

end BasedMappingPathSpace

/-- Helper for Criterion 8.5.4: the canonical basepoint of `N_p` is the basepoint of `E` together
with the constant path at the basepoint of `B`. -/
def basedMappingPathSpaceBasepoint {E B : BasedSpace} (p : E ⟶ B) :
    BasedMappingPathSpace p :=
  ⟨(underTopBasepoint E, ContinuousMap.const I (underTopBasepoint B)), by
    simpa using (criterion_map_underTopBasepoint p).symm⟩

/-- Helper for Criterion 8.5.4: regard `N_p` as a based space using its canonical basepoint. -/
abbrev basedMappingPathSpaceAtPoint {E B : BasedSpace} (p : E ⟶ B) : BasedSpace :=
  basedSpaceAtPoint (TopCat.of (BasedMappingPathSpace p)) (basedMappingPathSpaceBasepoint p)

/-- Helper for Criterion 8.5.4: forgetting the path coordinate defines a continuous projection
`N_p → E`. -/
def basedMappingPathSpacePointProjection {E B : BasedSpace} (p : E ⟶ B) :
    C(BasedMappingPathSpace p, E.right) where
  toFun x := x.point
  continuous_toFun := by
    exact continuous_fst.comp
      (show Continuous (fun x : BasedMappingPathSpace p ↦ x.1) from continuous_induced_dom)

/-- Helper for Criterion 8.5.4: evaluating the point projection returns the stored point. -/
@[simp] theorem basedMappingPathSpacePointProjection_apply {E B : BasedSpace} (p : E ⟶ B)
    (x : BasedMappingPathSpace p) :
    basedMappingPathSpacePointProjection p x = x.point :=
  rfl

/-- Helper for Criterion 8.5.4: forgetting the point coordinate defines the stored path family
`N_p → B^I`. -/
def basedMappingPathSpacePathProjection {E B : BasedSpace} (p : E ⟶ B) :
    C(BasedMappingPathSpace p, C(I, B.right)) where
  toFun x := x.path
  continuous_toFun := by
    exact continuous_snd.comp
      (show Continuous (fun x : BasedMappingPathSpace p ↦ x.1) from continuous_induced_dom)

/-- Helper for Criterion 8.5.4: evaluating the path projection returns the stored path. -/
@[simp] theorem basedMappingPathSpacePathProjection_apply {E B : BasedSpace} (p : E ⟶ B)
    (x : BasedMappingPathSpace p) :
    basedMappingPathSpacePathProjection p x = x.path :=
  rfl

/-- Helper for Criterion 8.5.4: the point projection `N_p → E` is a based map. -/
def basedMappingPathSpacePointMap {E B : BasedSpace} (p : E ⟶ B) :
    basedMappingPathSpaceAtPoint p ⟶ E :=
  basedMapOfMapToBasedSpace
    (basedMappingPathSpacePointProjection p :
      C((basedMappingPathSpaceAtPoint p).right, E.right)) (by
    -- Evaluating the point projection at the canonical basepoint recovers the basepoint of `E`.
    have hbase :
        underTopBasepoint (basedMappingPathSpaceAtPoint p) = basedMappingPathSpaceBasepoint p := by
      simp [basedMappingPathSpaceAtPoint]
    rw [hbase]
    rfl)

/-- Helper for Criterion 8.5.4: the underlying continuous map of the based point projection is
the ordinary point projection. -/
@[simp] theorem basedMappingPathSpacePointMap_hom {E B : BasedSpace} (p : E ⟶ B) :
    (basedMappingPathSpacePointMap p).right.hom =
      (basedMappingPathSpacePointProjection p :
        C((basedMappingPathSpaceAtPoint p).right, E.right)) := by
  rfl

/-- Helper for Criterion 8.5.4: evaluating the stored path at `1` gives a based map
`N_p → B`. -/
def basedMappingPathSpaceEndpointMap {E B : BasedSpace} (p : E ⟶ B) :
    basedMappingPathSpaceAtPoint p ⟶ B :=
  basedMapOfMapToBasedSpace
    ((pathSpaceEvalAt 1 B.right).comp
      (basedMappingPathSpacePathProjection p :
        C((basedMappingPathSpaceAtPoint p).right, C(I, B.right)))) (by
      -- The canonical basepoint of `N_p` stores the constant path at the basepoint of `B`.
      have hbase :
          underTopBasepoint (basedMappingPathSpaceAtPoint p) = basedMappingPathSpaceBasepoint p := by
        simp [basedMappingPathSpaceAtPoint]
      rw [hbase]
      rfl)

/-- Helper for Criterion 8.5.4: the underlying continuous map of the endpoint projection is
evaluation of the stored path at `1`. -/
@[simp] theorem basedMappingPathSpaceEndpointMap_hom {E B : BasedSpace} (p : E ⟶ B) :
    (basedMappingPathSpaceEndpointMap p).right.hom =
      (pathSpaceEvalAt 1 B.right).comp
        (basedMappingPathSpacePathProjection p :
          C((basedMappingPathSpaceAtPoint p).right, C(I, B.right))) := by
  rfl

/-- A based path lifting function for `p : E ⟶ B` is a continuous choice of paths in `E`
lifting the path families in `N_p`, and carrying the canonical basepoint of `N_p` to the constant
path at the basepoint of `E`. -/
structure BasedPathLiftingFunction {E B : BasedSpace} (p : E ⟶ B) where
  toContinuousMap : C(BasedMappingPathSpace p, C(I, E.right))
  source_eq (x : BasedMappingPathSpace p) :
    toContinuousMap x 0 = x.point
  proj_comp_eq (x : BasedMappingPathSpace p) :
    p.right.hom ∘ toContinuousMap x = x.path
  map_basepoint :
    toContinuousMap (basedMappingPathSpaceBasepoint p) =
      ContinuousMap.const I (underTopBasepoint E)

namespace BasedPathLiftingFunction

variable {E B : BasedSpace} {p : E ⟶ B}

/-- A based path lifting function may be used as its underlying map
`BasedMappingPathSpace p → C(I, E.right)`. -/
instance instCoeFun : CoeFun (BasedPathLiftingFunction p)
    (fun _ ↦ BasedMappingPathSpace p → C(I, E.right)) where
  coe s := s.toContinuousMap

/-- Evaluating a based path lifting function at time `0` recovers the prescribed point of
`E`. -/
theorem apply_zero (s : BasedPathLiftingFunction p) (x : BasedMappingPathSpace p) :
    s x 0 = x.point :=
  s.source_eq x

/-- Evaluating a based path lifting function at the canonical basepoint of `N_p` gives the
constant path at the basepoint of `E`. -/
theorem apply_basepoint (s : BasedPathLiftingFunction p) :
    s (basedMappingPathSpaceBasepoint p) =
      ContinuousMap.const I (underTopBasepoint E) :=
  s.map_basepoint

/-- Evaluating the projection identity pointwise recovers the prescribed path in `B`. -/
theorem proj_apply (s : BasedPathLiftingFunction p) (x : BasedMappingPathSpace p) (t : I) :
    p.right.hom (s x t) = x.path t := by
  have h := congrArg (fun γ : I → B.right ↦ γ t) (s.proj_comp_eq x)
  simpa using h

/-- The defining conditions of a based path lifting function expose its source and projected path.
-/
theorem spec (s : BasedPathLiftingFunction p) (x : BasedMappingPathSpace p) :
    s x 0 = x.point ∧ p.right.hom ∘ s x = x.path :=
  ⟨s.source_eq x, s.proj_comp_eq x⟩

end BasedPathLiftingFunction

/-- Helper for Criterion 8.5.4: an arbitrary based homotopy lifting problem determines a
classifying map into `N_p`. -/
def sigmaOfBasedHomotopy {A E B : BasedSpace} {p : E ⟶ B}
    {f₀ f₁ : A ⟶ B} (H : f₀.right.hom HRel[A] f₁.right.hom)
    (g₀ : A ⟶ E) (hg₀ : g₀ ≫ p = f₀) :
    C(A.right, BasedMappingPathSpace p) where
  toFun a :=
    ⟨(g₀.right.hom a, H.toHomotopy.toPathSpaceMap a), by
      -- The stored path begins at `f₀ a = p (g₀ a)`.
      have h₀ :
          H.toHomotopy.toPathSpaceMap a 0 = f₀.right.hom a := by
        simpa using
          ContinuousMap.congr_fun H.toHomotopy.pathSpaceEvalAtZero_comp_toPathSpaceMap a
      have hg₀a : p.right.hom (g₀.right.hom a) = f₀.right.hom a := by
        simpa [ContinuousMap.comp_apply] using congrArg (fun q : A ⟶ B ↦ q.right.hom a) hg₀
      exact h₀.trans hg₀a.symm⟩
  continuous_toFun := by
    -- First form the ambient map into `E × B^I`, then check the source condition pointwise.
    let F : A.right → E.right × C(I, B.right) :=
      fun a ↦ (g₀.right.hom a, H.toHomotopy.toPathSpaceMap a)
    have hF : Continuous F :=
      g₀.right.hom.continuous.prodMk H.toHomotopy.toPathSpaceMap.continuous
    have hmem : ∀ a : A.right, (F a).2 0 = p.right.hom (F a).1 := by
      intro a
      have h₀ :
          H.toHomotopy.toPathSpaceMap a 0 = f₀.right.hom a := by
        simpa using
          ContinuousMap.congr_fun H.toHomotopy.pathSpaceEvalAtZero_comp_toPathSpaceMap a
      have hg₀a : p.right.hom (g₀.right.hom a) = f₀.right.hom a := by
        simpa [ContinuousMap.comp_apply] using congrArg (fun q : A ⟶ B ↦ q.right.hom a) hg₀
      exact h₀.trans hg₀a.symm
    apply (continuous_induced_rng (f := fun x : BasedMappingPathSpace p ↦ x.1)).2
    simpa [F, Function.comp_def] using hF

/-- Helper for Criterion 8.5.4: the classifying map of a based homotopy sends the source
basepoint to the canonical basepoint of `N_p`. -/
theorem sigmaOfBasedHomotopy_apply_basepoint {A E B : BasedSpace} {p : E ⟶ B}
    {f₀ f₁ : A ⟶ B} (H : f₀.right.hom HRel[A] f₁.right.hom)
    (g₀ : A ⟶ E) (hg₀ : g₀ ≫ p = f₀) :
    sigmaOfBasedHomotopy H g₀ hg₀ (underTopBasepoint A) =
      basedMappingPathSpaceBasepoint p := by
  -- Route correction: the source condition is now at time `0`, so the basepoint track is the
  -- constant path at the basepoint of `B`.
  apply Subtype.ext
  apply Prod.ext
  · -- The point coordinate is the source basepoint image of the based map `g₀`.
    simpa [sigmaOfBasedHomotopy, basedMappingPathSpaceBasepoint, BasedMappingPathSpace.point] using
      criterion_map_underTopBasepoint g₀
  · -- The path coordinate is constant because `H` is relative to the singleton basepoint set.
    apply ContinuousMap.ext
    intro t
    have hrel := H.prop' t (underTopBasepoint A) (by simp [basedBasepointSet])
    simpa [sigmaOfBasedHomotopy, ContinuousMap.Homotopy.toPathSpaceMap_apply,
      criterion_map_underTopBasepoint f₀] using hrel

/-- Helper for Criterion 8.5.4: a map with the based covering homotopy property admits a based
path lifting function. -/
theorem nonempty_basedPathLiftingFunction_of_hasBasedCoveringHomotopyProperty
    {E B : BasedSpace} {p : E ⟶ B} (hp : HasBasedCoveringHomotopyProperty p) :
    Nonempty (BasedPathLiftingFunction p) := by
  let A : BasedSpace := basedMappingPathSpaceAtPoint p
  let g₀ : A ⟶ E := basedMappingPathSpacePointMap p
  let f₁ : A ⟶ B := basedMappingPathSpaceEndpointMap p
  let d : C(A.right, C(I, B.right)) := basedMappingPathSpacePathProjection p
  have hH₀ : ∀ x : A.right, d x 0 = (g₀ ≫ p).right.hom x := by
    intro x
    simpa [d, g₀, ContinuousMap.comp_apply, basedMappingPathSpacePointMap_hom,
      basedMappingPathSpacePointProjection, BasedMappingPathSpace.path, BasedMappingPathSpace.point]
      using BasedMappingPathSpace.source_eq x
  have hH₁ : ∀ x : A.right, d x 1 = f₁.right.hom x := by
    intro x
    have h := ContinuousMap.congr_fun (basedMappingPathSpaceEndpointMap_hom p) x
    calc
      d x 1 = ((pathSpaceEvalAt 1 B.right).comp d) x := by
        rfl
      _ = f₁.right.hom x := by
        exact h.symm
  have hHrel :
      ∀ x : A.right, x ∈ basedBasepointSet A → d x = ContinuousMap.const I ((g₀ ≫ p).right.hom x) := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    ext t
    simpa [A, d, basedMappingPathSpaceBasepoint, pathSpaceEvalAt, ContinuousMap.comp_apply] using
      (criterion_map_underTopBasepoint (g₀ ≫ p)).symm
  let hH : (g₀ ≫ p).right.hom HRel[A] f₁.right.hom :=
    criterionHomotopyRelOfPathFamily d hH₀ hH₁ hHrel
  -- Apply the based CHP to the universal mapping-path-space square.
  obtain ⟨g₁, G, hG⟩ := hp.homotopyLift hH g₀ rfl
  refine ⟨{
    toContinuousMap := G.toHomotopy.toPathSpaceMap
    source_eq := ?_
    proj_comp_eq := ?_
    map_basepoint := ?_
  }⟩
  · intro x
    -- Evaluating the lifted homotopy at `0` recovers the initial lift `g₀`.
    calc
      G.toHomotopy.toPathSpaceMap x 0 = g₀.right.hom x := by
        simpa using ContinuousMap.congr_fun G.toHomotopy.pathSpaceEvalAtZero_comp_toPathSpaceMap x
      _ = x.point := by
        calc
          g₀.right.hom x = basedMappingPathSpacePointProjection p x := by
            simpa [g₀] using (ContinuousMap.congr_fun (basedMappingPathSpacePointMap_hom p) x)
          _ = x.point := by
            exact basedMappingPathSpacePointProjection_apply p x
  · intro x
    -- The lift projects back to the original stored path family.
    ext t
    have h := ContinuousMap.congr_fun hG (t, x)
    calc
      p.right.hom (G.toHomotopy.toPathSpaceMap x t) = p.right.hom (G.toHomotopy (t, x)) := by
        rfl
      _ = hH.toHomotopy (t, x) := h
      _ = d x t := by
        rfl
      _ = x.path t := by
        rfl
  · -- The relative condition forces the lifted path at the canonical basepoint to be constant.
    apply ContinuousMap.ext
    intro t
    have hrel := G.prop' t (underTopBasepoint A) (by simp [basedBasepointSet])
    calc
      G.toHomotopy.toPathSpaceMap (underTopBasepoint A) t = g₀.right.hom (underTopBasepoint A) := by
        simpa [ContinuousMap.Homotopy.toPathSpaceMap_apply] using hrel
      _ = underTopBasepoint E := criterion_map_underTopBasepoint g₀

/-- Helper for Criterion 8.5.4: a based path lifting function yields the based covering homotopy
property. -/
theorem hasBasedCoveringHomotopyProperty_of_nonempty_basedPathLiftingFunction
    {E B : BasedSpace} {p : E ⟶ B} (hs : Nonempty (BasedPathLiftingFunction p)) :
    HasBasedCoveringHomotopyProperty p := by
  classical
  let s := hs.some
  refine {
    homotopyLift := fun {A} {f₀} {f₁} H g₀ hg₀ => by
      let sigma : C(A.right, BasedMappingPathSpace p) := sigmaOfBasedHomotopy H g₀ hg₀
      let D : C(A.right, C(I, E.right)) := s.toContinuousMap.comp sigma
      have hsigmaBase :
          sigma (underTopBasepoint A) = basedMappingPathSpaceBasepoint p :=
        sigmaOfBasedHomotopy_apply_basepoint H g₀ hg₀
      have hD₀ : ∀ a : A.right, D a 0 = g₀.right.hom a := by
        intro a
        -- Each lifted path starts at the given initial lift.
        simpa [D, sigma, sigmaOfBasedHomotopy, s, BasedMappingPathSpace.point] using
          s.source_eq (sigma a)
      have hDbase :
          D (underTopBasepoint A) = ContinuousMap.const I (underTopBasepoint E) := by
        -- The chosen basepoint of `N_p` is sent to the constant basepoint path in `E`.
        calc
          D (underTopBasepoint A) = s.toContinuousMap (sigma (underTopBasepoint A)) := rfl
          _ = s.toContinuousMap (basedMappingPathSpaceBasepoint p) := by rw [hsigmaBase]
          _ = ContinuousMap.const I (underTopBasepoint E) := s.map_basepoint
      have hGbase :
          ((pathSpaceEvalAt 1 E.right).comp D) (underTopBasepoint A) = underTopBasepoint E := by
        have h := congrArg (fun γ : C(I, E.right) ↦ γ 1) hDbase
        simpa [pathSpaceEvalAt] using h
      let g₁ : A ⟶ E :=
        basedMapOfMapToBasedSpace ((pathSpaceEvalAt 1 E.right).comp D) hGbase
      have hg₁ :
          g₁.right.hom = (pathSpaceEvalAt 1 E.right).comp D := by
        simpa [g₁] using
          (basedMapOfMapToBasedSpace_hom ((pathSpaceEvalAt 1 E.right).comp D) hGbase)
      have hD₁ : ∀ a : A.right, D a 1 = g₁.right.hom a := by
        intro a
        simpa [hg₁, pathSpaceEvalAt] using (ContinuousMap.congr_fun hg₁ a).symm
      have hrel :
          ∀ a : A.right, a ∈ basedBasepointSet A → D a = ContinuousMap.const I (g₀.right.hom a) := by
        intro a ha
        rcases Set.mem_singleton_iff.mp ha with rfl
        -- The relative condition at the source basepoint comes from `σ(basepoint) = n₀`.
        calc
          D (underTopBasepoint A) = ContinuousMap.const I (underTopBasepoint E) := hDbase
          _ = ContinuousMap.const I (g₀.right.hom (underTopBasepoint A)) := by
            rw [criterion_map_underTopBasepoint g₀]
      let G : g₀.right.hom HRel[A] g₁.right.hom :=
        criterionHomotopyRelOfPathFamily D hD₀ hD₁ hrel
      refine ⟨g₁, G, ?_⟩
      -- Projecting the lifted path family back along `p` recovers the original homotopy.
      ext z
      rcases z with ⟨t, a⟩
      have h := congrArg (fun γ : I → B.right ↦ γ t) (s.proj_comp_eq (sigma a))
      simpa [G, D, sigma, sigmaOfBasedHomotopy, ContinuousMap.Homotopy.toPathSpaceMap_apply] using h
  }

/-- A based map has the based covering homotopy property exactly when it admits a based path
lifting function. -/
theorem hasBasedCoveringHomotopyProperty_iff_nonempty_basedPathLiftingFunction
    {E B : BasedSpace} (p : E ⟶ B) :
    HasBasedCoveringHomotopyProperty p ↔ Nonempty (BasedPathLiftingFunction p) := by
  constructor
  · intro hp
    exact nonempty_basedPathLiftingFunction_of_hasBasedCoveringHomotopyProperty hp
  · intro hs
    exact hasBasedCoveringHomotopyProperty_of_nonempty_basedPathLiftingFunction hs

namespace IsBasedFibration

/-- Criterion 8.5.4. A based map `p : E ⟶ B` is a based fibration exactly when it is surjective
and admits a based path lifting function. -/
theorem iff_surjective_and_nonempty_basedPathLiftingFunction {E B : BasedSpace} (p : E ⟶ B) :
    IsBasedFibration p ↔
      Function.Surjective p.right.hom ∧ Nonempty (BasedPathLiftingFunction p) := by
  constructor
  · intro hp
    -- Unpack surjectivity and then apply the path-lifting criterion for the based CHP part.
    exact ⟨hp.surjective,
      nonempty_basedPathLiftingFunction_of_hasBasedCoveringHomotopyProperty
        hp.toHasBasedCoveringHomotopyProperty⟩
  · rintro ⟨hsurj, hs⟩
    -- Repackage the criterion into the two fields of `IsBasedFibration`.
    exact
      { toHasBasedCoveringHomotopyProperty :=
          hasBasedCoveringHomotopyProperty_of_nonempty_basedPathLiftingFunction hs
        surjective := hsurj }

/-- A surjective based map admitting a based path lifting function is a based fibration. -/
instance instOfSurjectiveAndNonemptyBasedPathLiftingFunction {E B : BasedSpace} (p : E ⟶ B)
    (hsurj : Function.Surjective p.right.hom) [Nonempty (BasedPathLiftingFunction p)] :
    IsBasedFibration p :=
  (iff_surjective_and_nonempty_basedPathLiftingFunction p).2 ⟨hsurj, inferInstance⟩

end IsBasedFibration

namespace HasBasedCoveringHomotopyProperty

/-- A based map has the based covering homotopy property exactly when it admits a based path
lifting function. -/
theorem iff_nonempty_basedPathLiftingFunction {E B : BasedSpace} (p : E ⟶ B) :
    HasBasedCoveringHomotopyProperty p ↔ Nonempty (BasedPathLiftingFunction p) := by
  simpa using hasBasedCoveringHomotopyProperty_iff_nonempty_basedPathLiftingFunction p

/-- A based map admitting a based path lifting function has the based covering homotopy property.
-/
instance instOfNonemptyBasedPathLiftingFunction {E B : BasedSpace} (p : E ⟶ B)
    [Nonempty (BasedPathLiftingFunction p)] : HasBasedCoveringHomotopyProperty p :=
  (iff_nonempty_basedPathLiftingFunction p).2 inferInstance

end HasBasedCoveringHomotopyProperty
