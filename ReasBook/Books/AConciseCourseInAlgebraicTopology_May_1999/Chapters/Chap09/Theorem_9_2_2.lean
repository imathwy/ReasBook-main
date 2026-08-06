import Mathlib.Algebra.Exact
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Clopen
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.BasedHomotopyClassesPostcompose
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Theorem_8_6_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.OnePointBasedSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyInclusion
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap

open CategoryTheory
open scoped HomotopyClasses TopCat Topology Topology.Homotopy unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 9.2.2: every based map out of `onePointBasedSpace` is forced to be the
constant basepoint map. In particular, `Ho*[onePointBasedSpace, Z]` cannot model `π₀(Z)`. -/
private theorem onePointToSubsingleton (Z : CategoryTheory.Under (⊤_ TopCat)) :
    Subsingleton (onePointBasedSpace ⟶ Z) := by
  constructor
  intro f g
  -- The source has one point, and both based maps must send it to the distinguished basepoint.
  ext x
  cases x
  have hfbase :
      underTopBasepoint Z = f.right.hom PUnit.unit := by
    have hwf := congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      f.w
    simpa [onePointBasedSpace] using hwf
  have hgbase :
      underTopBasepoint Z = g.right.hom PUnit.unit := by
    have hwg := congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      g.w
    simpa [onePointBasedSpace] using hwg
  calc
    f.right.hom PUnit.unit = underTopBasepoint Z := hfbase.symm
    _ = g.right.hom PUnit.unit := hgbase

/-- Helper for Theorem 9.2.2: the concrete zero-sphere `S^0` pointed at `sphereBasepoint 0`. -/
private noncomputable abbrev sZeroBasedSpace : BasedSpace :=
  underTopOfPoint (𝕊 0) (sphereBasepoint 0)

/-- Helper for Theorem 9.2.2: the antipodal first basis vector is a point of `S^n`. -/
private theorem oppositeSphereBasepoint_mem (n : ℕ) :
    (-EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin (n + 1))) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  -- The antipodal first basis vector still has norm one.
  simp

/-- Helper for Theorem 9.2.2: a distinguished non-basepoint of `S^n`. -/
private noncomputable def oppositeSphereBasepoint (n : ℕ) : 𝕊 n :=
  ULift.up ⟨-EuclideanSpace.single 0 (1 : ℝ), oppositeSphereBasepoint_mem n⟩

/-- Helper for Theorem 9.2.2: the chosen basepoint of `S^n` is distinct from its antipode. -/
private theorem sphereBasepoint_ne_oppositeSphereBasepoint (n : ℕ) :
    sphereBasepoint n ≠ oppositeSphereBasepoint n := by
  -- Compare the zeroth Euclidean coordinates of the two concrete sphere points.
  intro h
  have h0 := congrArg (fun z : 𝕊 n ↦ ((ULift.down z).1 0 : ℝ)) h
  simp [sphereBasepoint, oppositeSphereBasepoint] at h0
  linarith

/-- Helper for Theorem 9.2.2: every point of `S^0` is either the chosen basepoint or its
antipode. -/
private theorem sphereZero_eq_basepoint_or_opposite (z : 𝕊 0) :
    z = sphereBasepoint 0 ∨ z = oppositeSphereBasepoint 0 := by
  -- A point of `S^0` has only one coordinate, whose square must be `1`.
  have hz : ‖((ULift.down z).1 : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    simpa using (ULift.down z).2
  rw [PiLp.norm_eq_of_L2] at hz
  have hx2 : (((ULift.down z).1 0 : ℝ)) ^ 2 = 1 := by
    simpa [Fin.sum_univ_one] using hz
  have hcases : (((ULift.down z).1 0 : ℝ)) = 1 ∨ (((ULift.down z).1 0 : ℝ)) = -1 := by
    -- Factor `x^2 - 1 = 0` as `(x - 1)(x + 1) = 0`.
    have hmul : ((((ULift.down z).1 0 : ℝ)) - 1) * ((((ULift.down z).1 0 : ℝ)) + 1) = 0 := by
      nlinarith [hx2]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hx | hx
    · left
      linarith
    · right
      linarith
  rcases hcases with hx | hx
  · left
    apply ULift.ext
    apply Subtype.ext
    ext i
    fin_cases i
    simpa [sphereBasepoint] using hx
  · right
    apply ULift.ext
    apply Subtype.ext
    ext i
    fin_cases i
    simpa [oppositeSphereBasepoint] using hx

/-- Helper for Theorem 9.2.2: `S^0` has decidable equality on its two points. -/
private noncomputable instance sZeroDecidableEq : DecidableEq (𝕊 0) :=
  Classical.decEq _

/-- Helper for Theorem 9.2.2: `S^0` is finite, with exactly the basepoint and antipode. -/
private noncomputable instance sZeroFintype : Fintype (𝕊 0) where
  elems := {sphereBasepoint 0, oppositeSphereBasepoint 0}
  complete z := by
    -- The explicit two-point classification exhausts the zero-sphere.
    rcases sphereZero_eq_basepoint_or_opposite z with h | h <;> simp [h]

/-- Helper for Theorem 9.2.2: the concrete zero-sphere inherits the `T1` topology of the metric
sphere. -/
private instance sZeroT1Space : T1Space (𝕊 0 : TopCat.{u}) := by
  -- Transport the separation property across the underlying `ULift` homeomorphism.
  letI : T1Space (EuclideanSpace ℝ (Fin 1)) :=
    ⟨fun z ↦ by
      rw [← Metric.closedBall_zero]
      exact Metric.isClosed_closedBall⟩
  letI : T1Space (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    Subtype.t1Space
  let e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ≃ₜ
      (𝕊 0 : TopCat.{u}) := Homeomorph.ulift.symm
  exact Homeomorph.t1Space e

/-- Helper for Theorem 9.2.2: the two-point sphere `S^0` is discrete. -/
private instance sZeroDiscreteTopology : DiscreteTopology (𝕊 0) := by
  infer_instance

/-- Helper for Theorem 9.2.2: the chosen based owner `sZeroBasedSpace` has discrete underlying
space. -/
private noncomputable instance sZeroBasedSpaceDecidableEq : DecidableEq sZeroBasedSpace.right := by
  change DecidableEq (𝕊 0)
  infer_instance

/-- Helper for Theorem 9.2.2: the chosen based owner `sZeroBasedSpace` has discrete underlying
space. -/
private instance sZeroBasedSpaceDiscreteTopology : DiscreteTopology sZeroBasedSpace.right := by
  change DiscreteTopology (𝕊 0)
  infer_instance

/-- Helper for Theorem 9.2.2: the family `(w, z) ↦ z ↦ if z = sphereBasepoint 0 then * else w`
is continuous on `W × S^0`. -/
private theorem continuous_sZeroPointFamily (W : BasedSpace) :
    Continuous fun p : W.right × sZeroBasedSpace.right ↦
      if p.2 = sphereBasepoint 0 then underTopBasepoint W else p.1 := by
  classical
  let s : Set (W.right × sZeroBasedSpace.right) := {p | p.2 = sphereBasepoint 0}
  have hsfrontier : frontier s = ∅ := by
    -- The slice where the second coordinate is the basepoint is clopen because `S^0` is discrete.
    have hsclopen : IsClopen s := by
      refine (isClopen_discrete {sphereBasepoint 0}).preimage continuous_snd
    exact hsclopen.frontier_eq
  have hsagree : ∀ p ∈ frontier s, (underTopBasepoint W : W.right) = p.1 := by
    -- There is no frontier to check.
    intro p hp
    rw [hsfrontier] at hp
    cases hp
  simpa [s] using
    (Continuous.piecewise (s := s)
      (f := fun _ : W.right × sZeroBasedSpace.right ↦ underTopBasepoint W)
      (g := fun p : W.right × sZeroBasedSpace.right ↦ p.1)
      hsagree
      continuous_const
      continuous_fst)

/-- Helper for Theorem 9.2.2: a fixed point of `W` determines the explicit based map `S^0 → W`
that sends the chosen basepoint to `underTopBasepoint W` and the antipode to that point. -/
private theorem continuous_sZeroPointMap (W : BasedSpace) (w : W.right) :
    Continuous fun z : sZeroBasedSpace.right ↦
      if z = sphereBasepoint 0 then underTopBasepoint W else w := by
  -- Freeze the `W`-coordinate in the continuous two-variable family from `continuous_sZeroPointFamily`.
  simpa using
    (continuous_sZeroPointFamily W).comp
      (Continuous.prodMk continuous_const continuous_id)

/-- Helper for Theorem 9.2.2: the explicit point-map `S^0 → W` is continuous. -/
private noncomputable def sZeroPointContinuousMap (W : BasedSpace) (w : W.right) :
    C(sZeroBasedSpace.right, W.right) :=
  { toFun := fun z ↦ if z = sphereBasepoint 0 then underTopBasepoint W else w
    continuous_toFun := continuous_sZeroPointMap W w }

/-- Helper for Theorem 9.2.2: the explicit point-map sends the chosen basepoint of `S^0` to the
chosen basepoint of `W`, so it packages into a based map. -/
private theorem sZeroPointToBasedMap_w (W : BasedSpace) (w : W.right) :
    sZeroBasedSpace.hom ≫ TopCat.ofHom (sZeroPointContinuousMap W w) = W.hom := by
  -- Evaluating the source terminal map lands at `sphereBasepoint 0`, where the explicit formula
  -- is forced to be the chosen basepoint of `W`.
  ext u
  have hu : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom u
    rfl
  calc
    (sZeroBasedSpace.hom ≫ TopCat.ofHom (sZeroPointContinuousMap W w)) u =
        sZeroPointContinuousMap W w (sphereBasepoint 0) := rfl
    _ = underTopBasepoint W := by
      change (if sphereBasepoint 0 = sphereBasepoint 0 then underTopBasepoint W else w) =
        underTopBasepoint W
      simp
    _ = W.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = W.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u)) := by
      rw [hu]
    _ = W.hom u := by
      simp

/-- Helper for Theorem 9.2.2: the explicit point-map `S^0 → W` regarded as a based map. -/
private noncomputable def sZeroPointToBasedMap (W : BasedSpace) (w : W.right) :
    sZeroBasedSpace ⟶ W :=
  CategoryTheory.Under.homMk
    (TopCat.ofHom (sZeroPointContinuousMap W w))
    (sZeroPointToBasedMap_w W w)

/-- Helper for Theorem 9.2.2: the underlying function of the explicit point-map is the expected
two-point formula. -/
@[simp] private theorem sZeroPointToBasedMap_apply (W : BasedSpace) (w : W.right)
    (z : sZeroBasedSpace.right) :
    (sZeroPointToBasedMap W w).right.hom z =
      if z = sphereBasepoint 0 then underTopBasepoint W else w :=
  rfl

/-- Helper for Theorem 9.2.2: the explicit point-map sends the antipode of `S^0` to the chosen
point `w`. -/
@[simp] private theorem sZeroPointToBasedMap_apply_opposite (W : BasedSpace) (w : W.right) :
    (sZeroPointToBasedMap W w).right.hom (oppositeSphereBasepoint 0) = w := by
  -- The antipode is not the chosen basepoint, so the explicit formula takes the `else` branch.
  rw [sZeroPointToBasedMap_apply]
  split_ifs with h
  · exact (sphereBasepoint_ne_oppositeSphereBasepoint 0 h.symm).elim
  · rfl

/-- Helper for Theorem 9.2.2: every based map `S^0 → W` sends the chosen basepoint of `S^0` to
the chosen basepoint of `W`. -/
@[simp] private theorem basedMap_apply_sZeroBasepoint {W : BasedSpace} (f : sZeroBasedSpace ⟶ W) :
    f.right.hom (sphereBasepoint 0) = underTopBasepoint W := by
  -- Evaluate the `Under` commutativity condition at the unique terminal point.
  have hw :=
    congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      (CategoryTheory.Under.w f)
  simpa [sZeroBasedSpace] using hw

/-- Helper for Theorem 9.2.2: the explicit point-map recovers any based map `S^0 → W` from its
value at the antipode. -/
private theorem sZeroPointToBasedMap_eq_of_eval {W : BasedSpace} (f : sZeroBasedSpace ⟶ W) :
    sZeroPointToBasedMap W (f.right.hom (oppositeSphereBasepoint 0)) = f := by
  -- A map out of the two-point space `S^0` is determined by its values on the basepoint and the
  -- antipode.
  ext z
  rcases sphereZero_eq_basepoint_or_opposite z with rfl | rfl
  · rw [sZeroPointToBasedMap_apply, basedMap_apply_sZeroBasepoint]
    simp
  · rw [sZeroPointToBasedMap_apply_opposite]

/-- Helper for Theorem 9.2.2: the quotient relation on based maps already collapses to a single
based homotopy because based homotopy is an equivalence relation. -/
private theorem basedHomotopyRel_of_setoid {A B : BasedSpace} {u v : A ⟶ B}
    (h : (basedHomotopySetoid A B).r u v) :
    basedHomotopyRel u v := by
  -- Unfold the equivalence-closure relation and collapse it by induction using the standard
  -- reflexive, symmetric, and transitive operations on `HomotopyRel`.
  rw [basedHomotopySetoid_iff] at h
  induction h with
  | rel _ _ huv =>
      exact huv
  | refl u =>
      exact ContinuousMap.HomotopicRel.refl u.right.hom
  | symm _ _ _ huv =>
      exact ContinuousMap.HomotopicRel.symm huv
  | trans _ _ _ _ _ huv hvw =>
      exact ContinuousMap.HomotopicRel.trans huv hvw

/-- Helper for Theorem 9.2.2: evaluating a based homotopy between maps `S^0 → W` at the antipode
produces a path between the corresponding points of `W`. -/
private theorem joined_eval_opposite_of_basedHomotopy {W : BasedSpace}
    {f g : sZeroBasedSpace ⟶ W} (hfg : basedHomotopyRel f g) :
    Joined (f.right.hom (oppositeSphereBasepoint 0)) (g.right.hom (oppositeSphereBasepoint 0)) := by
  obtain ⟨Hfg⟩ := hfg
  -- Evaluate the underlying ordinary homotopy at the antipodal point to obtain a path in `W`.
  refine ⟨Path.mk
    (Hfg.toHomotopy.toContinuousMap.comp
      ((ContinuousMap.id I).prodMk
        (ContinuousMap.const I (oppositeSphereBasepoint 0))))
    ?_ ?_⟩
  · change Hfg.toHomotopy (0, oppositeSphereBasepoint 0) =
        f.right.hom (oppositeSphereBasepoint 0)
    exact Hfg.toHomotopy.map_zero_left (oppositeSphereBasepoint 0)
  · change Hfg.toHomotopy (1, oppositeSphereBasepoint 0) =
        g.right.hom (oppositeSphereBasepoint 0)
    exact Hfg.toHomotopy.map_one_left (oppositeSphereBasepoint 0)

/-- Helper for Theorem 9.2.2: the class of a based map `S^0 → W` depends only on the path
component of its value at the antipode. -/
private theorem sZeroBasedHomotopyClassToZerothHomotopy_wellDefined
    {W : BasedSpace} {f g : sZeroBasedSpace ⟶ W}
    (hfg : (basedHomotopySetoid sZeroBasedSpace W).r f g) :
    (⟦f.right.hom (oppositeSphereBasepoint 0)⟧ : ZerothHomotopy W.right) =
      ⟦g.right.hom (oppositeSphereBasepoint 0)⟧ := by
  -- Collapse the setoid relation to an actual based homotopy, then evaluate that homotopy at the
  -- antipode.
  exact Quotient.sound
    (joined_eval_opposite_of_basedHomotopy (basedHomotopyRel_of_setoid hfg))

/-- Helper for Theorem 9.2.2: evaluation at the antipode defines a map
`Ho*[S^0, W] → ZerothHomotopy W.right`. -/
private noncomputable def sZeroBasedHomotopyClassToZerothHomotopy (W : BasedSpace) :
    Ho*[sZeroBasedSpace, W] → ZerothHomotopy W.right :=
  Quotient.lift
    (fun f : sZeroBasedSpace ⟶ W ↦
      (⟦f.right.hom (oppositeSphereBasepoint 0)⟧ : ZerothHomotopy W.right))
    (fun _ _ hfg ↦ sZeroBasedHomotopyClassToZerothHomotopy_wellDefined hfg)

/-- Helper for Theorem 9.2.2: a path in `W` between points `w₀` and `w₁` induces a based homotopy
between the corresponding explicit point-maps `S^0 → W`. -/
private theorem sZeroPointToBasedMap_homotopic_of_joined {W : BasedSpace}
    {w₀ w₁ : W.right} (hww : Joined w₀ w₁) :
    basedHomotopyRel (sZeroPointToBasedMap W w₀) (sZeroPointToBasedMap W w₁) := by
  rcases hww with ⟨γ⟩
  -- The basepoint branch stays fixed, while the antipodal branch follows the given path `γ`.
  refine ⟨{
    toHomotopy := {
      toFun := fun p : I × sZeroBasedSpace.right ↦
        if p.2 = sphereBasepoint 0 then underTopBasepoint W else γ p.1
      continuous_toFun := by
        simpa using
          (continuous_sZeroPointFamily W).comp
            (Continuous.prodMk (γ.continuous.comp continuous_fst) continuous_snd)
      map_zero_left := ?_
      map_one_left := ?_ }
    prop' := ?_ }⟩
  · intro z
    -- At time `0` the moving branch starts at `w₀`.
    symm
    rw [sZeroPointToBasedMap_apply]
    simp [γ.source]
  · intro z
    -- At time `1` the moving branch ends at `w₁`.
    symm
    rw [sZeroPointToBasedMap_apply]
    simp [γ.target]
  · intro t z hz
    -- The relative condition holds because the basepoint branch is fixed for all `t`.
    rcases Set.mem_singleton_iff.mp hz with rfl
    change (if sphereBasepoint 0 = sphereBasepoint 0 then underTopBasepoint W else γ t) =
      (if sphereBasepoint 0 = sphereBasepoint 0 then underTopBasepoint W else w₀)
    simp

/-- Helper for Theorem 9.2.2: the explicit point-map construction depends only on the path
component of the chosen point of `W`. -/
private theorem zerothHomotopyToSZeroBasedHomotopyClass_wellDefined
    {W : BasedSpace} {w₀ w₁ : W.right} (hww : Joined w₀ w₁) :
    ((Quotient.mk (basedHomotopySetoid sZeroBasedSpace W) (sZeroPointToBasedMap W w₀)) :
        Ho*[sZeroBasedSpace, W]) =
      (Quotient.mk (basedHomotopySetoid sZeroBasedSpace W) (sZeroPointToBasedMap W w₁)) := by
  -- The path between `w₀` and `w₁` gives the required based homotopy between the point-maps.
  exact Quotient.sound (Relation.EqvGen.rel _ _
    (sZeroPointToBasedMap_homotopic_of_joined hww))

/-- Helper for Theorem 9.2.2: sending a path component of `W` to the class of the corresponding
explicit point-map `S^0 → W`. -/
private noncomputable def zerothHomotopyToSZeroBasedHomotopyClass (W : BasedSpace) :
    ZerothHomotopy W.right → Ho*[sZeroBasedSpace, W] :=
  Quotient.lift
    (fun w : W.right ↦
      ((Quotient.mk (basedHomotopySetoid sZeroBasedSpace W) (sZeroPointToBasedMap W w)) :
        Ho*[sZeroBasedSpace, W]))
    (fun _ _ hww ↦ zerothHomotopyToSZeroBasedHomotopyClass_wellDefined hww)

/-- Helper for Theorem 9.2.2: the two-point owner `S^0` models path components of the codomain by
evaluation at the antipode. -/
private noncomputable def sZeroBasedHomotopyClassesEquivZerothHomotopy
    (W : BasedSpace) :
    Ho*[sZeroBasedSpace, W] ≃ ZerothHomotopy W.right where
  toFun := sZeroBasedHomotopyClassToZerothHomotopy W
  invFun := zerothHomotopyToSZeroBasedHomotopyClass W
  left_inv := by
    intro a
    -- Reduce to a represented class and then replace the representative by the explicit point-map
    -- determined by its antipodal value.
    refine Quotient.inductionOn a ?_
    intro f
    change
      ((Quotient.mk (basedHomotopySetoid sZeroBasedSpace W)
        (sZeroPointToBasedMap W (f.right.hom (oppositeSphereBasepoint 0)))) :
          Ho*[sZeroBasedSpace, W]) =
        Quotient.mk (basedHomotopySetoid sZeroBasedSpace W) f
    rw [sZeroPointToBasedMap_eq_of_eval]
  right_inv := by
    intro a
    -- Reduce to a represented path component and evaluate the corresponding explicit point-map at
    -- the antipode.
    refine Quotient.inductionOn a ?_
    intro w
    change
      (⟦(sZeroPointToBasedMap W w).right.hom (oppositeSphereBasepoint 0)⟧ :
          ZerothHomotopy W.right) = ⟦w⟧
    rw [sZeroPointToBasedMap_apply_opposite]

/-- Helper for Theorem 9.2.2: the `S^0`/`π₀` comparison is natural under postcomposition by a
based map. -/
private theorem sZeroBasedHomotopyClassesEquivZerothHomotopy_natural
    {W W' : BasedSpace} (g : W ⟶ W') :
    (sZeroBasedHomotopyClassesEquivZerothHomotopy W').toFun ∘
        (basedHomotopyClassesPostcompose sZeroBasedSpace g).toFun =
      zerothHomotopyMap g.right.hom ∘
        (sZeroBasedHomotopyClassesEquivZerothHomotopy W).toFun := by
  -- On a represented class `[f]`, both sides return the path component of `g (f(opp))`.
  funext a
  refine Quotient.inductionOn a ?_
  intro f
  change (⟦(f ≫ g).right.hom (oppositeSphereBasepoint 0)⟧ : ZerothHomotopy W'.right) =
    zerothHomotopyMap g.right.hom ⟦f.right.hom (oppositeSphereBasepoint 0)⟧
  rw [zerothHomotopyMap_mk]
  rfl

-- Semantic recall via `lean_leansearch`: the canonical owners surfaced were `HomotopyGroup.Pi`
-- and `HomotopyGroup.pi0EquivZerothHomotopy`. Repo precedent for long exact sequences packages
-- the evident inclusion-induced maps explicitly and leaves the connecting morphisms as named data
-- whose exactness properties are asserted.

/-- The continuous inclusion `A ↪ X` underlying the pair long exact sequence. -/
abbrev pairSubspaceInclusion (A : Set X) : C(A, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion-induced map `π_ n(A, x) → π_ n(X, x)` for the pair `(X, A)`. -/
def pairSubspaceInclusionHomotopyGroupMap (A : Set X) (x : A) (n : ℕ) :
    π_ n A x → π_ n X x.1 :=
  homotopyGroupMap (pairSubspaceInclusion A) n x

/-- The based loop map `Ω A ⟶ Ω X` induced by the inclusion `A ↪ X`. Its `π_ 0` identifies with
the inclusion-induced map `π_(q + 2)(A, x) ⟶ π_(q + 2)(X, x)` after the standard loop-space
identifications. -/
def pairLoopSubspaceInclusionMap (A : Set X) (x : A) : C(Ω A x, Ω X x.1) where
  toFun γ := γ.map continuous_subtype_val
  continuous_toFun :=
    continuous_induced_rng.2 <|
      (ContinuousMap.continuous_postcomp ⟨Subtype.val, continuous_subtype_val⟩).comp
        continuous_induced_dom

@[simp] theorem pairLoopSubspaceInclusionMap_refl (A : Set X) (x : A) :
    pairLoopSubspaceInclusionMap A x (Path.refl x) = Path.refl x.1 :=
  rfl

/-- The map on loop-space homotopy groups induced by `pairLoopSubspaceInclusionMap A x`. -/
def pairLoopSubspaceInclusionHomotopyGroupMap (A : Set X) (x : A) (q : ℕ) :
    π_ (q + 1) (Ω A x) (Path.refl x) → π_ (q + 1) (Ω X x.1) (Path.refl x.1) :=
  cast
    (congrArg
      (fun y ↦ π_ (q + 1) (Ω A x) (Path.refl x) → π_ (q + 1) (Ω X x.1) y)
      (pairLoopSubspaceInclusionMap_refl A x))
    (homotopyGroupMap (pairLoopSubspaceInclusionMap A x) (q + 1) (Path.refl x))

/-- The based loop map `Ω X ⟶ P(X; *, A)` coming from the fiber sequence of the inclusion
`A ↪ X`: a loop based at `x` is regarded as a path from `x` to the distinguished endpoint
`x ∈ A`. Its `π_ 0` identifies with the connecting map
`π_(q + 2)(X, x) ⟶ π_(q + 2)(X, A, x)`. -/
def pairLoopToRelativePathSpaceMap (A : Set X) (x : A) : C(Ω X x.1, PathToSet A x.1) where
  toFun γ :=
    { endpoint := x
      path := γ }
  continuous_toFun :=
    by
      rw [continuous_induced_rng]
      change Continuous fun γ : Ω X x.1 ↦ (x, γ.toContinuousMap)
      exact Continuous.prodMk continuous_const continuous_induced_dom

@[simp] theorem pairLoopToRelativePathSpaceMap_refl (A : Set X) (x : A) :
    pairLoopToRelativePathSpaceMap A x (Path.refl x.1) = PathToSet.refl x :=
  rfl

/-- The connecting map on homotopy groups induced by `pairLoopToRelativePathSpaceMap A x`. -/
def pairLoopToRelativeHomotopyGroupMap (A : Set X) (x : A) (q : ℕ) :
    π_ (q + 1) (Ω X x.1) (Path.refl x.1) → relativeHomotopyGroup (q + 1).succPNat A x :=
  cast
    ((congrArg
        (fun y ↦
          π_ (q + 1) (Ω X x.1) (Path.refl x.1) → π_ (q + 1) (PathToSet A x.1) y)
        (pairLoopToRelativePathSpaceMap_refl A x)).trans
      (congrArg
        (fun y ↦ π_ (q + 1) (Ω X x.1) (Path.refl x.1) → y)
        (relativeHomotopyGroup_succ (q + 1) A x).symm))
    (homotopyGroupMap (pairLoopToRelativePathSpaceMap A x) (q + 1) (Path.refl x.1))

/-- The endpoint map `P(X; *, A) ⟶ A` whose induced homotopy-group map is the boundary
homomorphism in the pair sequence. -/
def pairRelativeEndpointMap (A : Set X) (x : A) : C(PathToSet A x.1, A) where
  toFun γ := γ.endpoint
  continuous_toFun :=
    by
      change Continuous (Prod.fst ∘ PathToSet.endpointAndPath A x)
      exact continuous_fst.comp continuous_induced_dom

@[simp] theorem pairRelativeEndpointMap_refl (A : Set X) (x : A) :
    pairRelativeEndpointMap A x (PathToSet.refl x) = x :=
  rfl

/-- The boundary map `π_(q + 2)(X, A, x) ⟶ π_(q + 1)(A, x)` attached to the pair `(X, A)`. -/
def pairHomotopyBoundaryMap (A : Set X) (x : A) (q : ℕ) :
    relativeHomotopyGroup (q + 1).succPNat A x → π_ (q + 1) A x :=
  cast
    ((congrArg
        (fun y ↦ π_ (q + 1) (PathToSet A x.1) (PathToSet.refl x) → π_ (q + 1) A y)
        (pairRelativeEndpointMap_refl A x)).trans
      (congrArg
        (fun y ↦ y → π_ (q + 1) A x)
        (relativeHomotopyGroup_succ (q + 1) A x).symm))
    (homotopyGroupMap (pairRelativeEndpointMap A x) (q + 1) (PathToSet.refl x))

/-- The `π_ 0` loop-space model of `π_ 1(A, x)` used in the tail of the pair long exact sequence. -/
abbrev pairSubspaceLoopPiZeroHomotopyGroup (A : Set X) (x : A) :=
  π_ 0 (Ω A x) (Path.refl x)

/-- The `π_ 0` loop-space model of `π_ 1(X, x)` used in the tail of the pair long exact sequence. -/
abbrev pairAmbientLoopPiZeroHomotopyGroup (A : Set X) (x : A) :=
  π_ 0 (Ω X x.1) (Path.refl x.1)

/-- The `π_ 0` path-space model of `π_ 1(X, A, x)` used in the tail of the pair long exact
sequence. -/
abbrev pairRelativePiZeroHomotopyGroup (A : Set X) (x : A) :=
  π_ 0 (PathToSet A x.1) (PathToSet.refl x)

/-- The map `π_ 1(A, x) → π_ 1(X, x)` written on the canonical `π_ 0` loop-space models. -/
def pairLoopSubspaceInclusionPiZeroMap (A : Set X) (x : A) :
    pairSubspaceLoopPiZeroHomotopyGroup A x → pairAmbientLoopPiZeroHomotopyGroup A x :=
  cast
    (congrArg
      (fun y ↦ pairSubspaceLoopPiZeroHomotopyGroup A x → π_ 0 (Ω X x.1) y)
      (pairLoopSubspaceInclusionMap_refl A x))
    (homotopyGroupMap (pairLoopSubspaceInclusionMap A x) 0 (Path.refl x))

/-- The map `π_ 1(X, x) → π_ 1(X, A, x)` written on the canonical `π_ 0` loop/path-space
models. -/
def pairLoopToRelativePiZeroMap (A : Set X) (x : A) :
    pairAmbientLoopPiZeroHomotopyGroup A x → pairRelativePiZeroHomotopyGroup A x :=
  cast
    (congrArg
      (fun y ↦ pairAmbientLoopPiZeroHomotopyGroup A x → π_ 0 (PathToSet A x.1) y)
      (pairLoopToRelativePathSpaceMap_refl A x))
    (homotopyGroupMap (pairLoopToRelativePathSpaceMap A x) 0 (Path.refl x.1))

/-- The distinguished base component of the relative path-space model
`π_ 0 (PathToSet A x.1) (PathToSet.refl x)`, corresponding to the constant path at `x`. -/
def pairRelativePiZeroBasepoint (A : Set X) (x : A) :
    pairRelativePiZeroHomotopyGroup A x :=
  default

@[simp] theorem pairRelativePiZeroBasepoint_eq_default (A : Set X) (x : A) :
    pairRelativePiZeroBasepoint A x = default :=
  rfl

/-- The terminal boundary map `π_1(X, A, x) ⟶ π₀(A)` in the tail of the pair long exact
sequence. -/
def pairHomotopyBoundaryZeroMap (A : Set X) (x : A) :
    pairRelativePiZeroHomotopyGroup A x → ZerothHomotopy A :=
  ((HomotopyGroup.pi0EquivZerothHomotopy :
      π_ 0 A x ≃ ZerothHomotopy A)) ∘
    homotopyGroupMap (pairRelativeEndpointMap A x) 0 (PathToSet.refl x)

/-- Helper for Theorem 9.2.2: the induced map of the explicit inclusion owner
`pairSubspaceInclusion A` is exactly `pairSubspaceInclusionHomotopyGroupMap A x q`. -/
theorem pairSubspaceInclusion_eStar_eq_pairSubspaceInclusionHomotopyGroupMap
    (A : Set X) (x : A) (q : ℕ) :
    (pairSubspaceInclusion A).eStar q x = pairSubspaceInclusionHomotopyGroupMap A x q := by
  -- Both sides are induced by the same continuous inclusion `A ↪ X`.
  funext y
  rfl

/-- Helper for Theorem 9.2.2: under `π_ 0 ≃ ZerothHomotopy`, the degree-`0` inclusion-induced map
agrees with `zerothHomotopyInclusion A`. -/
theorem pairSubspaceInclusionPiZero_commutes (A : Set X) (x : A) :
    (HomotopyGroup.pi0EquivZerothHomotopy :
        π_ 0 X x.1 ≃ ZerothHomotopy X).toFun ∘
        pairSubspaceInclusionHomotopyGroupMap A x 0 =
      zerothHomotopyInclusion A ∘
        (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 A x ≃ ZerothHomotopy A).toFun := by
  -- Compare both sides on a representative generalized loop in the subspace.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  rfl

/-- Helper for Theorem 9.2.2: the positive-degree boundary map sends the identity relative class
to the identity in `π_(q + 1)(A, x)`. -/
@[simp] theorem pairHomotopyBoundaryMap_one (A : Set X) (x : A) (q : ℕ) :
    pairHomotopyBoundaryMap A x q 1 = 1 := by
  -- Unfold the casted induced map and reduce to the standard identity computation for `e_*`.
  cases relativeHomotopyGroup_succ (q + 1) A x
  change homotopyGroupMap (pairRelativeEndpointMap A x) (q + 1) (PathToSet.refl x) 1 = 1
  exact homotopyGroupMap_one (pairRelativeEndpointMap A x) q (PathToSet.refl x)

/-- Helper for Theorem 9.2.2: specialize a positive-degree homotopy-group map by choosing the
target basepoint with an explicit equality. -/
private def homotopyGroupMapOverEq
    {A : Type u} {B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ) :
    π_ (n + 1) A a → π_ (n + 1) B b :=
  match hf with
  | rfl => homotopyGroupMap f (n + 1) a

/-- Helper for Theorem 9.2.2: ordinary homotopy-group maps compose by postcomposition of the
underlying continuous maps. -/
private theorem homotopyGroupMap_comp
    {A : Type u} {B : Type u} {C : Type u}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (q : ℕ) (a : A) :
    homotopyGroupMap (g.comp f) q a =
      (homotopyGroupMap g q (f a)) ∘ homotopyGroupMap f q a := by
  -- Reduce to generalized-loop representatives, where both sides are literally the same map.
  funext x
  refine Quotient.inductionOn x ?_
  intro γ
  rfl

/-- Helper for Theorem 9.2.2: postcomposition on positive-degree homotopy groups respects
composition even after choosing a target basepoint by equality. -/
private theorem homotopyGroupMapOverEq_comp
    {A : Type u} {B : Type u} {C : Type u}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C))
    {a : A} {b : B} {c : C} (hf : f a = b) (hg : g b = c) (n : ℕ) :
    (homotopyGroupMapOverEq g hg n) ∘ (homotopyGroupMapOverEq f hf n) =
      homotopyGroupMapOverEq (g.comp f)
        (by simpa [ContinuousMap.comp_apply, hf] using hg) n := by
  -- First normalize the endpoint witnesses; then both sides are induced by the same composite map.
  funext x
  subst hf
  subst hg
  simpa [homotopyGroupMapOverEq] using
    congrFun (homotopyGroupMap_comp f g (n + 1) a).symm x

/-- Helper for Theorem 9.2.2: pointwise equal continuous maps induce the same transported
positive-degree homotopy-group map. -/
private theorem homotopyGroupMapOverEq_congr
    {A : Type u} {B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f g : C(A, B)) (hfg : f = g) (hf : f a = b) (hg : g a = b) (n : ℕ) :
    homotopyGroupMapOverEq f hf n = homotopyGroupMapOverEq g hg n := by
  -- After replacing the underlying map by an equal one, only the endpoint-proof witness remains,
  -- and that witness is propositionally irrelevant.
  subst hfg
  exact funext fun x ↦ by
    simpa using congrFun (homotopyGroupMapOverEq_comp (ContinuousMap.id A) f rfl hf n) x

/-- Helper for Theorem 9.2.2: changing only the proof of the target-basepoint equality does not
change `ContinuousMap.eStarMulHomOverEq`. -/
private theorem eStarMulHomOverEq_proofIrrel
    {A : Type u} {B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (n : ℕ) (h₁ h₂ : f a = b) :
    f.eStarMulHomOverEq n h₁ = f.eStarMulHomOverEq n h₂ := by
  -- The endpoint witness is proposition-valued, so the defining transport is proof irrelevant.
  cases h₁
  cases h₂
  rfl

/-- Helper for Theorem 9.2.2: applying `eStarMulHomOverEq` is the same as applying the
specialized positive-degree homotopy-group map with the same endpoint witness. -/
private theorem eStarMulHomOverEq_apply
    {A : Type u} {B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (n : ℕ) (x : π_ (n + 1) A a) :
    f.eStarMulHomOverEq n hf x = homotopyGroupMapOverEq f hf n x := by
  -- Normalize the endpoint witness so both sides reduce to the same transported map.
  cases hf
  rfl

/-- Helper for Theorem 9.2.2: composing the successor-degree transported monoid homs agrees with
transporting along the composite map. -/
private theorem eStarMulHomOverEq_comp
    {A : Type u} {B : Type u} {C : Type u}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {a : A} {b : B} {c : C}
    (f : C(A, B)) (hf : f a = b) (g : C(B, C)) (hg : g b = c) (n : ℕ) :
    (g.eStarMulHomOverEq n hg).comp (f.eStarMulHomOverEq n hf) =
    (g.comp f).eStarMulHomOverEq n
        (by simpa [ContinuousMap.comp_apply, hf] using hg) := by
  -- Reduce the bundled equality to the function-level transported composition statement.
  ext x
  rw [MonoidHom.comp_apply, eStarMulHomOverEq_apply g hg n, eStarMulHomOverEq_apply f hf n,
    eStarMulHomOverEq_apply (g.comp f) (by simpa [ContinuousMap.comp_apply, hf] using hg) n]
  exact congrFun (homotopyGroupMapOverEq_comp f g hf hg n) x

/-- Helper for Theorem 9.2.2: `pairLoopToRelativePathSpaceMap` records a loop by pairing the fixed
endpoint `x` with the same underlying path in `X`. -/
@[simp] private theorem pairLoopToRelativePathSpaceMap_endpointAndPath
    (A : Set X) (x : A) (γ : Ω X x.1) :
    PathToSet.endpointAndPath A x (pairLoopToRelativePathSpaceMap A x γ) =
      (x, γ.toContinuousMap) := by
  -- Unfold the explicit path-space model and compare endpoint/path coordinates directly.
  rfl

/-- Helper for Theorem 9.2.2: the endpoint of the explicit loop-to-relative map is constantly the
chosen basepoint `x`. -/
private theorem pairRelativeEndpointMap_comp_pairLoopToRelativePathSpaceMap
    (A : Set X) (x : A) :
    (pairRelativeEndpointMap A x).comp (pairLoopToRelativePathSpaceMap A x) =
      ContinuousMap.const (Ω X x.1) x := by
  -- Both sides forget the loop and return the chosen endpoint in `A`.
  ext γ
  rfl

/-- Helper for Theorem 9.2.2: the based inclusion `A ↪ X` at the chosen basepoint `x`. -/
private noncomputable def pairBasedInclusionMap (A : Set X) (x : A) :
    underTopOfPoint A x ⟶ underTopOfPoint X x.1 :=
  Under.homMk
    (TopCat.ofHom (pairSubspaceInclusion A))
    (by
      ext u
      rfl)

/-- Helper for Theorem 9.2.2: the underlying map of `pairBasedInclusionMap A x` is the subtype
inclusion `A ↪ X`. -/
@[simp] private theorem pairBasedInclusionMap_hom (A : Set X) (x : A) :
    (pairBasedInclusionMap A x).right.hom = pairSubspaceInclusion A :=
  rfl

/-- Helper for Theorem 9.2.2: a Chapter 8 homotopy-fiber point for the based inclusion
`A ↪ X` carries the same endpoint-and-path data as the modeled inclusion homotopy fiber. -/
private theorem pairFiberToInclusionHomotopyFiber_condition
    (A : Set X) (x : A) (z : HomotopyFiber (pairBasedInclusionMap A x)) :
    z.path 0 = x.1 ∧ z.path 1 = z.point.1 := by
  constructor
  · -- The stored path in the homotopy fiber starts at the chosen basepoint of `X`.
    simpa [pairBasedInclusionMap] using PathSpace.source_eq z.path
  · -- Its endpoint lands at the chosen fiber point in `A`.
    simpa [pairBasedInclusionMap] using (HomotopyFiber.endpoint_eq z).symm

/-- Helper for Theorem 9.2.2: forget the Chapter 8 packaging on the homotopy fiber of the based
inclusion `A ↪ X` and retain only the endpoint in `A` and the path in `X`. -/
private noncomputable def pairFiberToInclusionHomotopyFiber
    (A : Set X) (x : A) :
    HomotopyFiber (pairBasedInclusionMap A x) → inclusionHomotopyFiber A x
  | z =>
      ⟨(z.point, z.path.1), pairFiberToInclusionHomotopyFiber_condition A x z⟩

/-- Helper for Theorem 9.2.2: the modeled inclusion homotopy fiber point already satisfies the
endpoint equation needed to build a Chapter 8 homotopy-fiber point. -/
private theorem pairInclusionHomotopyFiberToFiber_condition
    (A : Set X) (x : A) (z : inclusionHomotopyFiber A x) :
    (pairBasedInclusionMap A x).right.hom z.endpoint = (PathSpace.ofPath z.path).endpoint := by
  -- The endpoint of `z.path` is exactly the chosen endpoint in `A`.
  rw [PathSpace.endpoint_ofPath]
  change z.endpoint.1 = z.endpoint.1
  rfl

/-- Helper for Theorem 9.2.2: repackage a modeled inclusion homotopy-fiber point as the Chapter 8
homotopy-fiber point for the based inclusion `A ↪ X`. -/
private noncomputable def pairInclusionHomotopyFiberToFiber
    (A : Set X) (x : A) :
    inclusionHomotopyFiber A x → HomotopyFiber (pairBasedInclusionMap A x)
  | z =>
      HomotopyFiber.mk z.endpoint (PathSpace.ofPath z.path)
        (pairInclusionHomotopyFiberToFiber_condition A x z)

/-- Helper for Theorem 9.2.2: the Chapter 8 and modeled inclusion homotopy-fiber presentations of
the based inclusion `A ↪ X` are inverse on the Chapter 8 side. -/
private theorem pairFiberToInclusionHomotopyFiber_leftInverse
    (A : Set X) (x : A) :
    Function.LeftInverse (pairInclusionHomotopyFiberToFiber A x)
      (pairFiberToInclusionHomotopyFiber A x) := by
  intro z
  -- Unpack the Chapter 8 fiber point so the round-trip only repackages the same coordinates.
  rcases z with ⟨⟨y, γ⟩, hγ⟩
  rfl

/-- Helper for Theorem 9.2.2: the Chapter 8 and modeled inclusion homotopy-fiber presentations of
the based inclusion `A ↪ X` are inverse on the modeled side. -/
private theorem pairFiberToInclusionHomotopyFiber_rightInverse
    (A : Set X) (x : A) :
    Function.RightInverse (pairInclusionHomotopyFiberToFiber A x)
      (pairFiberToInclusionHomotopyFiber A x) := by
  intro z
  -- Unpack the modeled inclusion fiber so the round-trip reduces to the stored endpoint and path.
  rcases z with ⟨⟨y, γ⟩, hγ₀, hγ₁⟩
  rfl

/-- Helper for Theorem 9.2.2: forgetting the Chapter 8 packaging on the based inclusion fiber is
continuous because it only projects to the endpoint and underlying path coordinates. -/
private theorem pairFiberToInclusionHomotopyFiber_continuous
    (A : Set X) (x : A) :
    Continuous (pairFiberToInclusionHomotopyFiber A x) := by
  -- Continuity is componentwise on the point coordinate and the stored path coordinate.
  exact
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk
        (fun z ↦ by simpa using pairFiberToInclusionHomotopyFiber_condition A x z)

/-- Helper for Theorem 9.2.2: repackaging the modeled inclusion fiber as the Chapter 8 homotopy
fiber is continuous because it only restores the source-condition witness on the same coordinates.
-/
private theorem pairInclusionHomotopyFiberToFiber_continuous
    (A : Set X) (x : A) :
    Continuous (pairInclusionHomotopyFiberToFiber A x) := by
  have hEndpoint : Continuous fun z : inclusionHomotopyFiber A x ↦ z.endpoint := by
    -- The endpoint is the first coordinate of the modeled inclusion fiber.
    simpa [inclusionHomotopyFiber.endpoint] using
      (continuous_fst.comp continuous_subtype_val :
        Continuous fun z : inclusionHomotopyFiber A x ↦ z.1.1)
  have hPath : Continuous fun z : inclusionHomotopyFiber A x ↦ PathSpace.ofPath z.path := by
    -- Forgetting the endpoint proof on the path keeps the same continuous map coordinate.
    exact (continuous_snd.comp continuous_subtype_val).subtype_mk
      (fun z ↦ by simpa [inclusionHomotopyFiber.path, PathSpace.ofPath] using z.2.1)
  exact (hEndpoint.prodMk hPath).subtype_mk
    (fun z ↦ pairInclusionHomotopyFiberToFiber_condition A x z)

/-- Helper for Theorem 9.2.2: the local comparison from the Chapter 8 homotopy fiber of the
based inclusion `A ↪ X` to the modeled inclusion homotopy fiber is a homeomorphism. -/
private noncomputable def pairFiberHomeomorphInclusionHomotopyFiber
    (A : Set X) (x : A) :
    HomotopyFiber (pairBasedInclusionMap A x) ≃ₜ inclusionHomotopyFiber A x :=
  { toEquiv :=
      { toFun := pairFiberToInclusionHomotopyFiber A x
        invFun := pairInclusionHomotopyFiberToFiber A x
        left_inv := pairFiberToInclusionHomotopyFiber_leftInverse A x
        right_inv := pairFiberToInclusionHomotopyFiber_rightInverse A x }
    continuous_toFun := pairFiberToInclusionHomotopyFiber_continuous A x
    continuous_invFun := pairInclusionHomotopyFiberToFiber_continuous A x }

/-- Helper for Theorem 9.2.2: the local homeomorphism to the modeled inclusion homotopy fiber acts
by forgetting the Chapter 8 packaging and retaining the endpoint-and-path coordinates. -/
@[simp] private theorem pairFiberHomeomorphInclusionHomotopyFiber_apply
    (A : Set X) (x : A) (z : HomotopyFiber (pairBasedInclusionMap A x)) :
    pairFiberHomeomorphInclusionHomotopyFiber A x z =
      pairFiberToInclusionHomotopyFiber A x z := by
  rfl

/-- Helper for Theorem 9.2.2: the Chapter 8 homotopy fiber of the based inclusion `A ↪ X` is
homeomorphic to the Chapter 9 path-space model `PathToSet A x.1`. -/
private noncomputable def pairFiberHomeomorphPathToSet
    (A : Set X) (x : A) :
    HomotopyFiber (pairBasedInclusionMap A x) ≃ₜ PathToSet A x.1 :=
  (pairFiberHomeomorphInclusionHomotopyFiber A x).trans
    (inclusionHomotopyFiberHomeomorphPathToSet A x)

/-- Helper for Theorem 9.2.2: the local homotopy-fiber/path-space comparison as a continuous
map. -/
private noncomputable def pairFiberHomeomorphPathToSetContinuousMap
    (A : Set X) (x : A) :
    C(HomotopyFiber (pairBasedInclusionMap A x), PathToSet A x.1) :=
  ⟨pairFiberHomeomorphPathToSet A x, (pairFiberHomeomorphPathToSet A x).continuous_toFun⟩

/-- Helper for Theorem 9.2.2: the local homotopy-fiber/path-space comparison records a Chapter 8
fiber point by the same endpoint and underlying path. -/
@[simp] private theorem pairFiberHomeomorphPathToSet_endpointAndPath
    (A : Set X) (x : A) (z : HomotopyFiber (pairBasedInclusionMap A x)) :
    PathToSet.endpointAndPath A x (pairFiberHomeomorphPathToSet A x z) =
      (z.point, z.path.1) := by
  -- Unfold the composite homeomorphism and then read off the modeled endpoint-and-path data.
  change
    PathToSet.endpointAndPath A x
        (inclusionHomotopyFiberHomeomorphPathToSet A x
          (pairFiberHomeomorphInclusionHomotopyFiber A x z)) =
      (z.point, z.path.1)
  rw [pairFiberHomeomorphInclusionHomotopyFiber_apply]
  rw [inclusionHomotopyFiberHomeomorphPathToSet_apply]
  rfl

/-- Helper for Theorem 9.2.2: the distinguished point of the Chapter 8 homotopy fiber of the
based inclusion `A ↪ X` corresponds to the constant path `PathToSet.refl x`. -/
@[simp] private theorem pairFiberHomeomorphPathToSet_basepoint
    (A : Set X) (x : A) :
    pairFiberHomeomorphPathToSet A x
        (HomotopyFiber.basepoint (pairBasedInclusionMap A x)) =
      PathToSet.refl x := by
  have hbase :
      pairFiberToInclusionHomotopyFiber A x
          (HomotopyFiber.basepoint (pairBasedInclusionMap A x)) =
        inclusionHomotopyFiber.mk x (Path.refl x.1) := by
    -- The Chapter 8 basepoint already has endpoint `x` and the constant path at `x.1`.
    rfl
  -- Unfold the composite comparison and then normalize the modeled inclusion-fiber input.
  change
    inclusionHomotopyFiberHomeomorphPathToSet A x
        (pairFiberHomeomorphInclusionHomotopyFiber A x
          (HomotopyFiber.basepoint (pairBasedInclusionMap A x))) =
      PathToSet.refl x
  rw [pairFiberHomeomorphInclusionHomotopyFiber_apply]
  rw [inclusionHomotopyFiberHomeomorphPathToSet_apply]
  rw [hbase]
  -- The Chapter 9 model sends the constant endpoint-plus-path data to `PathToSet.refl x`.
  rfl

/-- Helper for Theorem 9.2.2: after the local homotopy-fiber/path-space comparison, the Chapter 8
projection `F_i ⟶ A` becomes the public endpoint map `pairRelativeEndpointMap A x`. -/
private theorem pairFiberHomeomorphPathToSet_comp_projection
    (A : Set X) (x : A) :
    (pairRelativeEndpointMap A x).comp
        (pairFiberHomeomorphPathToSetContinuousMap A x) =
      ⟨fun z : HomotopyFiber (pairBasedInclusionMap A x) ↦ z.point, by
        simpa [HomotopyFiber.point] using
          (continuous_fst.comp continuous_subtype_val :
            Continuous fun z : HomotopyFiber (pairBasedInclusionMap A x) ↦ z.1.1)⟩ := by
  -- Project the coordinate formula from `pairFiberHomeomorphPathToSet_endpointAndPath` to the
  -- endpoint coordinate.
  ext z
  exact congrArg Subtype.val
    (congrArg Prod.fst (pairFiberHomeomorphPathToSet_endpointAndPath A x z))

/-- Helper for Theorem 9.2.2: after the local homotopy-fiber/path-space comparison, the Chapter 8
loop inclusion `ΩX ⟶ F_i` becomes the public path-space map
`pairLoopToRelativePathSpaceMap A x`. -/
private theorem pairFiberHomeomorphPathToSet_comp_loopInclusion
    (A : Set X) (x : A) :
    (pairFiberHomeomorphPathToSetContinuousMap A x).comp
        ⟨fun χ : Ω X x.1 ↦
            HomotopyFiber.mk x (PathSpace.ofPath χ) (by
              calc
                (pairBasedInclusionMap A x).right.hom x = x.1 := by
                  rfl
                _ = (PathSpace.ofPath χ).endpoint := by
                  simpa using χ.target.symm),
          by
            -- The endpoint proof is stable, so continuity reduces to the path coordinate.
            simpa [PathSpace.ofPath, PathSpace.mk] using
              (Continuous.prodMk continuous_const
                ((continuous_induced_dom :
                    Continuous fun χ : Ω X x.1 ↦ χ.toContinuousMap).subtype_mk
                      (fun χ ↦ χ.source'))).subtype_mk
                (fun χ ↦ by
                  calc
                    (pairBasedInclusionMap A x).right.hom x = x.1 := by
                      rfl
                    _ = (PathSpace.ofPath χ).endpoint := by
                      simpa using χ.target.symm)⟩ =
      pairLoopToRelativePathSpaceMap A x := by
  -- Compare both maps through the concrete endpoint-and-path coordinates in `PathToSet`.
  ext χ
  apply (PathToSet.endpointAndPath_injective (A := A) (x := x))
  let z : HomotopyFiber (pairBasedInclusionMap A x) :=
    HomotopyFiber.mk x (PathSpace.ofPath χ) (by
      calc
        (pairBasedInclusionMap A x).right.hom x = x.1 := by
          rfl
        _ = (PathSpace.ofPath χ).endpoint := by
          simpa using χ.target.symm)
  change
    PathToSet.endpointAndPath A x (pairFiberHomeomorphPathToSet A x z) =
      PathToSet.endpointAndPath A x (pairLoopToRelativePathSpaceMap A x χ)
  rw [pairFiberHomeomorphPathToSet_endpointAndPath, pairLoopToRelativePathSpaceMap_endpointAndPath]
  rfl

/-- Helper for Theorem 9.2.2: generalized-loop homotopies are exactly paths in the generalized
loop space. -/
private theorem genLoopHomotopic_iff_joined
    {N : Type*} {Y : Type*} [TopologicalSpace Y] {y : Y} {p q : Ω^ N Y y} :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let curriedHomotopy := H.toHomotopy.curry
    -- Curry the relative homotopy into a path through the generalized-loop space.
    refine ⟨Path.mk
      ⟨fun t ↦
          (⟨curriedHomotopy t, fun a ha ↦ (H.prop t a ha).trans (p.property a ha)⟩ :
            Ω^ N Y y),
        Continuous.subtype_mk curriedHomotopy.continuous ?_⟩
      ?_ ?_⟩
    · intro t a ha
      exact (H.prop t a ha).trans (p.property a ha)
    · ext a
      exact H.apply_zero a
    · ext a
      exact H.apply_one a
  · rintro ⟨γ⟩
    -- Uncurry a path of generalized loops into a relative homotopy.
    refine ⟨⟨⟨
      (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ γ.toContinuousMap).uncurry,
      ?_, ?_⟩, ?_⟩⟩
    · intro a
      change γ 0 a = p a
      exact congrArg (fun r : Ω^ N Y y ↦ r a) γ.source
    · intro a
      change γ 1 a = q a
      exact congrArg (fun r : Ω^ N Y y ↦ r a) γ.target
    · intro t a ha
      exact ((γ t).property a ha).trans (p.property a ha).symm

/-- Helper for Theorem 9.2.2: a homeomorphism preserves and reflects the path relation `Joined`.
-/
private theorem joined_iff_homeomorph
    {Y : Type*} {Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Y ≃ₜ Z) {a b : Y} :
    Joined (h a) (h b) ↔ Joined a b := by
  constructor
  · rintro ⟨γ⟩
    -- Pull the path back along the inverse homeomorphism.
    simpa using (show Joined (h.symm (h a)) (h.symm (h b)) from ⟨γ.map h.symm.continuous⟩)
  · rintro ⟨γ⟩
    -- Push the path forward along the homeomorphism.
    exact ⟨γ.map h.continuous⟩

/-- Helper for Theorem 9.2.2: a homeomorphism of generalized-loop spaces preserves and reflects
generalized-loop homotopies. -/
private theorem genLoopHomotopic_iff_of_homeomorph
    {M : Type*} {N : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] {y : Y} {z : Z}
    (h : Ω^ M Y y ≃ₜ Ω^ N Z z) {p q : Ω^ M Y y} :
    GenLoop.Homotopic (h p) (h q) ↔ GenLoop.Homotopic p q := by
  -- Translate homotopies to paths, use the homeomorphism, then translate back.
  rw [genLoopHomotopic_iff_joined, genLoopHomotopic_iff_joined, joined_iff_homeomorph h]

/-- Helper for Theorem 9.2.2: `π_N(Y, y)` is the path-component quotient of the generalized-loop
owner `Ω^ N Y y`. -/
private abbrev homotopyGroupEquivZerothHomotopyGenLoop
    {Y : Type u} [TopologicalSpace Y] (N : Type*) (y : Y) :
    HomotopyGroup N Y y ≃ ZerothHomotopy (Ω^ N Y y) :=
  Quotient.congr (Equiv.refl _) fun _ _ ↦ genLoopHomotopic_iff_joined

/-- Helper for Theorem 9.2.2: under `π_ 0 ≃ ZerothHomotopy`, the induced map on `π_ 0` agrees
with the map on path components. -/
private theorem pi0EquivZerothHomotopy_natural
    {Y : Type u} {Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : C(Y, Z)) (y : Y) :
    (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 Z (e y) ≃ ZerothHomotopy Z).toFun ∘
        homotopyGroupMap e 0 y =
      zerothHomotopyMap e ∘
        (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 Y y ≃ ZerothHomotopy Y).toFun := by
  -- Both sides send a represented `π_ 0` class to the path component of the image point under `e`.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  rfl

/-- Helper for Theorem 9.2.2: `Fin 1`-indexed generalized loops identify with the ordinary loop
space. -/
private def oneGenLoopHomeomorph (x : X) : Ω^ (Fin 1) X x ≃ₜ Ω X x where
  toFun p :=
    Path.mk ⟨fun t ↦ p (fun _ ↦ t), by fun_prop⟩
      (p.2 (fun _ ↦ 0) ⟨0, Or.inl rfl⟩)
      (p.2 (fun _ ↦ 1) ⟨0, Or.inr rfl⟩)
  invFun γ :=
    ⟨⟨fun t ↦ γ (t 0), by fun_prop⟩, fun t ht ↦ by
      rcases ht with ⟨i, hi | hi⟩
      · have hi0 : t 0 = 0 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = x
        calc
          γ (t 0) = γ 0 := by simpa using congrArg γ hi0
          _ = x := γ.source
      · have hi1 : t 0 = 1 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = x
        calc
          γ (t 0) = γ 1 := by simpa using congrArg γ hi1
          _ = x := γ.target⟩
  left_inv p := by
    -- Reduce the `Fin 1` cube to its unique coordinate.
    ext t
    have ht : t = fun _ : Fin 1 ↦ t 0 := by
      funext i
      fin_cases i
      rfl
    rw [ht]
    rfl
  right_inv γ := by
    -- The forward map simply evaluates the unique coordinate.
    ext t
    rfl
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t _ ↦ t, by fun_prop⟩).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t : I^(Fin 1) ↦ t 0, by fun_prop⟩).comp continuous_induced_dom

/-- Helper for Theorem 9.2.2: the inverse of `oneGenLoopHomeomorph` sends the constant loop to
the constant generalized loop. -/
@[simp] private theorem oneGenLoopHomeomorph_symm_refl (x : X) :
    (oneGenLoopHomeomorph x).symm (Path.refl x) = GenLoop.const := by
  -- Both representatives are constant at `x`.
  ext t
  rfl

/-- Helper for Theorem 9.2.2: a homeomorphism of spaces induces a homeomorphism on
generalized-loop spaces. -/
private def genLoopHomeomorph
    {M : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z) :
    Ω^ M Y y ≃ₜ Ω^ M Z z where
  toFun p :=
    ⟨⟨fun t ↦ h (p t), h.continuous.comp p.1.continuous⟩, fun t ht ↦ by
      simpa [hy] using congrArg h (p.2 t ht)⟩
  invFun p :=
    ⟨⟨fun t ↦ h.symm (p t), (h.symm.continuous).comp p.1.continuous⟩, fun t ht ↦ by
      have hp : p t = z := p.2 t ht
      calc
        h.symm (p t) = h.symm z := by rw [hp]
        _ = y := (h.symm_apply_eq).2 hy.symm⟩
  left_inv p := by
    -- The inverse homeomorphism cancels pointwise.
    ext t
    simp
  right_inv p := by
    -- The same pointwise cancellation proves the reverse direction.
    ext t
    simp
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact (ContinuousMap.continuous_postcomp ⟨h, h.continuous⟩).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_postcomp ⟨h.symm, h.symm.continuous⟩).comp
        continuous_subtype_val

/-- Helper for Theorem 9.2.2: `genLoopHomeomorph` respects generalized-loop homotopies. -/
private theorem genLoopHomeomorph_respects
    {M : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z)
    {p q : Ω^ M Y y} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (genLoopHomeomorph h hy p) (genLoopHomeomorph h hy q) := by
  -- Postcompose the representative homotopy by the homeomorphism.
  change (genLoopHomeomorph h hy p).1.HomotopicRel (genLoopHomeomorph h hy q).1 (Cube.boundary M)
  simpa [genLoopHomeomorph, GenLoop.Homotopic] using
    ContinuousMap.HomotopicRel.comp_continuousMap hpq ⟨h, h.continuous⟩

/-- Helper for Theorem 9.2.2: the inverse of `genLoopHomeomorph` also respects generalized-loop
homotopies. -/
private theorem genLoopHomeomorph_symm_respects
    {M : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z)
    {p q : Ω^ M Z z} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic
      ((genLoopHomeomorph h hy).symm p)
      ((genLoopHomeomorph h hy).symm q) := by
  -- Reduce to the forward compatibility for the inverse homeomorphism.
  have hsymm : h.symm z = y := by
    exact (h.symm_apply_eq).2 hy.symm
  simpa [genLoopHomeomorph] using
    genLoopHomeomorph_respects h.symm hsymm hpq

/-- Helper for Theorem 9.2.2: a homeomorphism transports homotopy groups by acting on
generalized-loop representatives. -/
private def homotopyGroupHomeomorphEquiv
    {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z)
    (n : ℕ) : π_ n Y y ≃ π_ n Z z :=
  let e : Ω^ (Fin n) Y y ≃ₜ Ω^ (Fin n) Z z := genLoopHomeomorph h hy
  { toFun := Quotient.map e (fun _ _ hpq ↦ genLoopHomeomorph_respects h hy hpq)
    invFun := Quotient.map e.symm (fun _ _ hpq ↦ genLoopHomeomorph_symm_respects h hy hpq)
    left_inv := by
      -- The homeomorphism inverse cancels on representatives before quotienting.
      intro p
      refine Quotient.inductionOn p ?_
      intro γ
      change Quotient.mk' (e.symm (e γ)) = Quotient.mk' γ
      congr
      ext t
      simp
    right_inv := by
      -- The same representative-level cancellation proves the reverse direction.
      intro p
      refine Quotient.inductionOn p ?_
      intro γ
      change Quotient.mk' (e (e.symm γ)) = Quotient.mk' γ
      congr
      ext t
      simp }

/-- Helper for Theorem 9.2.2: iterated loops on the loop space identify with the next
ordinary iterated loop space. -/
private def loopSpaceRepresentativeHomeomorph (n : ℕ) (x : X) :
    Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin (n + 1)) X x :=
  let e₁ : Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const :=
    genLoopHomeomorph (oneGenLoopHomeomorph x).symm (oneGenLoopHomeomorph_symm_refl x)
  let e₂ : Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) X x :=
    GenLoop.genLoopGenLoopEquiv x
  let e₃ : Ω^ (Fin n ⊕ Fin 1) X x ≃ₜ Ω^ (Fin (n + 1)) X x :=
    GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  (e₁.trans e₂).trans e₃

/-- Helper for Theorem 9.2.2: the standard loop-space shift induces an equivalence
`π_ n(Ω X, refl) ≃ π_(n + 1)(X, x)`. -/
private def loopSpaceHomotopyGroupEquivPiSucc (n : ℕ) (x : X) :
    π_ n (Ω X x) (Path.refl x) ≃ π_ (n + 1) X x :=
  Quotient.congr (loopSpaceRepresentativeHomeomorph n x) fun _ _ ↦
    (genLoopHomotopic_iff_of_homeomorph (loopSpaceRepresentativeHomeomorph n x)).symm

/-- Helper for Theorem 9.2.2: the loop-space shift sends a class to the class of its shifted
representative. -/
@[simp] private theorem loopSpaceHomotopyGroupEquivPiSucc_apply
    (n : ℕ) (x : X) (γ : Ω^ (Fin n) (Ω X x) (Path.refl x)) :
    loopSpaceHomotopyGroupEquivPiSucc n x ⟦γ⟧ =
      (⟦loopSpaceRepresentativeHomeomorph n x γ⟧ : π_ (n + 1) X x) :=
  rfl

/-- Helper for Theorem 9.2.2: the representative-level loop-space shift commutes with the
subtype inclusion. -/
private theorem loopSpaceRepresentativeHomeomorph_subtypeInclusion
    (A : Set X) (x : A) (n : ℕ)
    (γ : Ω^ (Fin n) (Ω A x) (Path.refl x)) :
    loopSpaceRepresentativeHomeomorph n x.1
        (genLoopMap (pairLoopSubspaceInclusionMap A x) γ) =
      genLoopMap (pairSubspaceInclusion A)
        (loopSpaceRepresentativeHomeomorph n x γ) := by
  -- Both sides evaluate by forgetting the subtype after the same iterated-loop reshuffling.
  ext t
  rfl

/-- Helper for Theorem 9.2.2: after one loop-space shift, the public map
`pairLoopSubspaceInclusionHomotopyGroupMap A x q` agrees with the ordinary inclusion-induced map
on `π_(q + 2)`. -/
private theorem pairLoopSubspaceInclusion_commutes_withSubtypeInclusionPiSucc
    (A : Set X) (x : A) (q : ℕ) :
    (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1).toFun ∘
        pairLoopSubspaceInclusionHomotopyGroupMap A x q =
      pairSubspaceInclusionHomotopyGroupMap A x (q + 2) ∘
        (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x).toFun := by
  -- Compare both induced maps on iterated-loop representatives before quotienting.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  simp [pairLoopSubspaceInclusionHomotopyGroupMap,
    pairSubspaceInclusionHomotopyGroupMap,
    loopSpaceRepresentativeHomeomorph_subtypeInclusion]

/-- Helper for Theorem 9.2.2: the tail identification `π₀(Ω -) ≃ π₁(-)` carries the loop-space
inclusion map to the ordinary degree-`1` inclusion-induced map. -/
private theorem pairLoopPiZero_commutes_withPairSubspaceInclusionPiOne
    (A : Set X) (x : A) :
    (loopSpaceHomotopyGroupEquivPiSucc 0 x.1).toFun ∘
        pairLoopSubspaceInclusionPiZeroMap A x =
      pairSubspaceInclusionHomotopyGroupMap A x 1 ∘
        (loopSpaceHomotopyGroupEquivPiSucc 0 x).toFun := by
  -- Compare both induced maps on ordinary loop representatives before passing to the quotient.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  change
    Quotient.mk'
      (loopSpaceRepresentativeHomeomorph 0 x.1
        (genLoopMap (pairLoopSubspaceInclusionMap A x) γ)) =
    Quotient.mk'
      (genLoopMap (pairSubspaceInclusion A)
        (loopSpaceRepresentativeHomeomorph 0 x γ))
  exact congrArg Quotient.mk' (loopSpaceRepresentativeHomeomorph_subtypeInclusion A x 0 γ)

/-- Helper for Theorem 9.2.2: the `S^0`-owner `Ho*[S^0, ΩA]` identifies with the tail model
`π_ 0 (ΩA, refl)`. -/
private noncomputable def pairSubspaceLoopSZeroEquivPiZero
    (A : Set X) (x : A) :
    Ho*[sZeroBasedSpace, Ωᵇ (underTopOfPoint A x)] ≃ pairSubspaceLoopPiZeroHomotopyGroup A x :=
  (sZeroBasedHomotopyClassesEquivZerothHomotopy (Ωᵇ (underTopOfPoint A x))).trans
    ((HomotopyGroup.pi0EquivZerothHomotopy :
      pairSubspaceLoopPiZeroHomotopyGroup A x ≃ ZerothHomotopy (Ω A x)).symm)

/-- Helper for Theorem 9.2.2: the `S^0`-owner `Ho*[S^0, ΩX]` identifies with the tail model
`π_ 0 (ΩX, refl)`. -/
private noncomputable def pairAmbientLoopSZeroEquivPiZero
    (A : Set X) (x : A) :
    Ho*[sZeroBasedSpace, Ωᵇ (underTopOfPoint X x.1)] ≃ pairAmbientLoopPiZeroHomotopyGroup A x :=
  (sZeroBasedHomotopyClassesEquivZerothHomotopy (Ωᵇ (underTopOfPoint X x.1))).trans
    ((HomotopyGroup.pi0EquivZerothHomotopy :
      pairAmbientLoopPiZeroHomotopyGroup A x ≃ ZerothHomotopy (Ω X x.1)).symm)

/-- Helper for Theorem 9.2.2: the Chapter 8 homotopy-fiber owner and the public path-space owner
have the same path components. -/
private noncomputable def pairFiberZerothHomotopyEquivRelativePiZero
    (A : Set X) (x : A) :
    ZerothHomotopy (HomotopyFiber (pairBasedInclusionMap A x)) ≃ pairRelativePiZeroHomotopyGroup A x :=
  (zerothHomotopyEquivOfHomotopyEquiv
      (pairFiberHomeomorphPathToSet A x).toHomotopyEquiv).trans
    ((HomotopyGroup.pi0EquivZerothHomotopy :
      pairRelativePiZeroHomotopyGroup A x ≃ ZerothHomotopy (PathToSet A x.1)).symm)

/-- Helper for Theorem 9.2.2: the `S^0`-owner `Ho*[S^0, F_i]` identifies with the public tail
model `π_ 0 P(X; *, A)`. -/
private noncomputable def pairRelativeSZeroEquivPiZero
    (A : Set X) (x : A) :
    Ho*[sZeroBasedSpace, homotopyFiber (pairBasedInclusionMap A x)] ≃
      pairRelativePiZeroHomotopyGroup A x :=
  (sZeroBasedHomotopyClassesEquivZerothHomotopy (homotopyFiber (pairBasedInclusionMap A x))).trans
    (pairFiberZerothHomotopyEquivRelativePiZero A x)

/-- Helper for Theorem 9.2.2: the explicit positive-degree map
`pairLoopToRelativeHomotopyGroupMap A x q` sends the unit class to the unit class. -/
@[simp] private theorem pairLoopToRelativeHomotopyGroupMap_one
    (A : Set X) (x : A) (q : ℕ) :
    pairLoopToRelativeHomotopyGroupMap A x q 1 = 1 := by
  -- Normalize the relative owner to the path-space model and use the standard `e_*` unit law.
  cases relativeHomotopyGroup_succ (q + 1) A x
  change homotopyGroupMapOverEq
      (pairLoopToRelativePathSpaceMap A x)
      (pairLoopToRelativePathSpaceMap_refl A x)
      q 1 = 1
  rw [← eStarMulHomOverEq_apply
    (pairLoopToRelativePathSpaceMap A x)
    (pairLoopToRelativePathSpaceMap_refl A x)
    q 1]
  exact (ContinuousMap.eStarMulHomOverEq
    (pairLoopToRelativePathSpaceMap A x)
    q
    (pairLoopToRelativePathSpaceMap_refl A x)).map_one

/-- Helper for Theorem 9.2.2: once the Chapter 8 group-tail owner is compared with the explicit
Chapter 9 pair maps, the three positive-degree exactness clauses assemble together. -/
private theorem pairMapsPositiveDegreeExact
    (A : Set X) (x : A) :
    (∀ q : ℕ,
      Function.MulExact
        (pairLoopSubspaceInclusionHomotopyGroupMap A x q)
        (pairLoopToRelativeHomotopyGroupMap A x q)) ∧
    (∀ q : ℕ,
      Function.MulExact
        (pairLoopToRelativeHomotopyGroupMap A x q)
        (pairHomotopyBoundaryMap A x q)) ∧
    (∀ q : ℕ,
      Function.MulExact
        (pairHomotopyBoundaryMap A x q)
        (pairSubspaceInclusionHomotopyGroupMap A x (q + 1))) := by
  -- Route correction: the suggested `onePointBasedSpace` transport is not viable here.
  -- `Ho*[onePointBasedSpace, Z]` is always a subsingleton by `onePointToSubsingleton`, so it
  -- cannot recover the nontrivial `π₀`-owners needed for the pair long exact sequence.
  -- TODO: the local `S^0` bridge `Ho*[S^0, W] ≃ ZerothHomotopy W.right` is now available above.
  -- The unit computation for the public relative map is now isolated in
  -- `pairLoopToRelativeHomotopyGroupMap_one`, and the tail-facing `S^0` comparison equivalences
  -- are packaged by `pairSubspaceLoopSZeroEquivPiZero`, `pairAmbientLoopSZeroEquivPiZero`, and
  -- `pairRelativeSZeroEquivPiZero`.
  -- TODO: the remaining work is the stage transport: package the stage-owner equivalences for
  -- indices `3*q + 5`, `3*q + 4`, and `3*q + 3`, then compare the transported Chapter 8 maps
  -- with the public pair maps `pairLoopToRelativeHomotopyGroupMap` and
  -- `pairHomotopyBoundaryMap`.
  -- Current blocker: `fiberSequenceGeneratedByPostcompose` currently wants the source owner and
  -- the pair inclusion to live in the same universe, so the concrete `sZeroBasedSpace` at
  -- universe `0` cannot yet drive the stage-local transports for arbitrary `u`; after that
  -- universe alignment, the remaining proof work is the recursive signed-loop normalization.
  sorry

/-- The pointed tail exactness
`π_1(A, x) ⟶ π_1(X, x) ⟶ π_1(X, A, x) ⟶ π₀(A) ⟶ π₀(X)`, written using the `π_ 0` loop-space
models for the two fundamental-group terms. -/
def pairHomotopyTailExact (A : Set X) (x : A) : Prop :=
  (∀ g : pairAmbientLoopPiZeroHomotopyGroup A x,
      pairLoopToRelativePiZeroMap A x g = pairRelativePiZeroBasepoint A x ↔
        ∃ a : pairSubspaceLoopPiZeroHomotopyGroup A x,
          pairLoopSubspaceInclusionPiZeroMap A x a = g) ∧
    (∀ r : pairRelativePiZeroHomotopyGroup A x,
      pairHomotopyBoundaryZeroMap A x r = ⟦x⟧ ↔
        ∃ g : pairAmbientLoopPiZeroHomotopyGroup A x,
          pairLoopToRelativePiZeroMap A x g = r) ∧
    ∀ a₀ : ZerothHomotopy A,
      zerothHomotopyInclusion A a₀ = ⟦(x : X)⟧ ↔
        ∃ r : pairRelativePiZeroHomotopyGroup A x,
          pairHomotopyBoundaryZeroMap A x r = a₀

/-- Helper for Theorem 9.2.2: the pointed tail exactness of the pair sequence follows from the
Chapter 8 pointed exactness theorem after rewriting the public `π₀` owners. -/
private theorem pairTailExact
    (A : Set X) (x : A) :
    pairHomotopyTailExact A x := by
  -- Route correction: the tail really does need the `S^0` owner, not `onePointBasedSpace`.
  -- The latter has only one based homotopy class, so it cannot encode the path components
  -- appearing in `π₀(A)` and `π₀(X)`.
  -- TODO: the `S^0`/`π₀` bridge and its naturality are now proved above, and the three tail
  -- owners are packaged by `pairSubspaceLoopSZeroEquivPiZero`,
  -- `pairAmbientLoopSZeroEquivPiZero`, and `pairRelativeSZeroEquivPiZero`.
  -- The remaining tail work is to transport Chapter 8 exactness at indices `2`, `1`, and `0`
  -- through that bridge and the explicit tail
  -- identifications `pairLoopPiZero_commutes_withPairSubspaceInclusionPiOne`,
  -- `pairSubspaceInclusionPiZero_commutes`, and `pairRelativePiZeroBasepoint_eq_default`.
  -- Current blocker: invoking `fiberSequenceGeneratedByPostcompose sZeroBasedSpace` against the
  -- pair inclusion exposes the same-universe restriction from Chapter 8, so the concrete
  -- universe-`0` `S^0` owner still needs a universe-polymorphic replacement before the tail
  -- transport lemmas comparing `ΩX → F_i` / `F_i → A` with
  -- `pairLoopToRelativePiZeroMap` / `pairHomotopyBoundaryZeroMap` can even be stated.
  sorry

/-- A source-facing specification of Theorem 9.2.2, keeping the canonical inclusion-induced and
boundary maps explicit and bundling the three group-valued exactness clauses with the pointed tail
`π_1(A, x) ⟶ π_1(X, x) ⟶ π_1(X, A, x) ⟶ π₀(A) ⟶ π₀(X)`. -/
def pairHomotopyLongExactSequenceSpec (A : Set X) (x : A) : Prop :=
  (∀ q : ℕ,
      Function.MulExact
        (pairLoopSubspaceInclusionHomotopyGroupMap A x q)
        (pairLoopToRelativeHomotopyGroupMap A x q)) ∧
    (∀ q : ℕ,
      Function.MulExact
        (pairLoopToRelativeHomotopyGroupMap A x q)
        (pairHomotopyBoundaryMap A x q)) ∧
    (∀ q : ℕ,
      Function.MulExact
        (pairHomotopyBoundaryMap A x q)
        (pairSubspaceInclusionHomotopyGroupMap A x (q + 1))) ∧
    pairHomotopyTailExact A x

/-- Theorem 9.2.2. The based inclusion `A ↪ X` determines the long exact sequence of the pair
`(X, A)`, recorded here by the three exactness clauses in positive degrees together with the
pointed tail `π_1(A, x) ⟶ π_1(X, x) ⟶ π_1(X, A, x) ⟶ π₀(A) ⟶ π₀(X)`. -/
theorem pairHomotopyLongExactSequence (A : Set X) (x : A) :
    pairHomotopyLongExactSequenceSpec A x := by
  rcases pairMapsPositiveDegreeExact A x with ⟨h₁, h₂, h₃⟩
  -- The main theorem is now a flat assembly of the positive-degree exactness package and tail.
  exact ⟨h₁, h₂, h₃, pairTailExact A x⟩

/-- Theorem 9.2.2 (1). Applying `π_0` to the fiber sequence of the based inclusion `A ↪ X` from
Construction 9.2.1 yields exactness of
`pairLoopSubspaceInclusionHomotopyGroupMap A x q` followed by
`pairLoopToRelativeHomotopyGroupMap A x q`; under the standard loop-space identifications this is
the exactness of `π_(q + 2)(A, x) ⟶ π_(q + 2)(X, x) ⟶ π_(q + 2)(X, A, x)`. -/
theorem pairHomotopyLongExactSequenceSubspaceToAmbient (A : Set X) (x : A) (q : ℕ) :
    Function.MulExact
      (pairLoopSubspaceInclusionHomotopyGroupMap A x q)
      (pairLoopToRelativeHomotopyGroupMap A x q) :=
  (pairHomotopyLongExactSequence A x).1 q

/-- Theorem 9.2.2 (2). Applying `π_0` to the same fiber sequence yields exactness of
`pairLoopToRelativeHomotopyGroupMap A x q` followed by `pairHomotopyBoundaryMap A x q`; under the
standard identifications this is the exactness of
`π_(q + 2)(X, x) ⟶ π_(q + 2)(X, A, x) ⟶ π_(q + 1)(A, x)`. -/
theorem pairHomotopyLongExactSequenceAmbientToRelative (A : Set X) (x : A) (q : ℕ) :
    Function.MulExact
      (pairLoopToRelativeHomotopyGroupMap A x q)
      (pairHomotopyBoundaryMap A x q) :=
  (pairHomotopyLongExactSequence A x).2.1 q

/-- Theorem 9.2.2 (3). Applying `π_0` to the same fiber sequence yields exactness of
`pairHomotopyBoundaryMap A x q` followed by
`pairSubspaceInclusionHomotopyGroupMap A x (q + 1)`; under the standard identifications this is
the exactness of `π_(q + 2)(X, A, x) ⟶ π_(q + 1)(A, x) ⟶ π_(q + 1)(X, x)`. -/
theorem pairHomotopyLongExactSequenceBoundaryToSubspace (A : Set X) (x : A) (q : ℕ) :
    Function.MulExact
      (pairHomotopyBoundaryMap A x q)
      (pairSubspaceInclusionHomotopyGroupMap A x (q + 1)) :=
  (pairHomotopyLongExactSequence A x).2.2.1 q

/-- Theorem 9.2.2 (4). The tail of the pair long exact sequence is the pointed exact sequence
`π_1(A, x) ⟶ π_1(X, x) ⟶ π_1(X, A, x) ⟶ π₀(A) ⟶ π₀(X)`, written using the canonical `π_ 0`
loop-space models for the fundamental-group terms and the map
`pairHomotopyBoundaryZeroMap A x`. -/
theorem pairHomotopyLongExactSequenceTail (A : Set X) (x : A) :
    pairHomotopyTailExact A x :=
  (pairHomotopyLongExactSequence A x).2.2.2

/-- The first exactness clause in the tail
`π_1(A, x) ⟶ π_1(X, x) ⟶ π_1(X, A, x)`. -/
theorem pairHomotopyLongExactSequenceTail_exact_subspace_to_ambient (A : Set X) (x : A) :
    ∀ g : pairAmbientLoopPiZeroHomotopyGroup A x,
      pairLoopToRelativePiZeroMap A x g = pairRelativePiZeroBasepoint A x ↔
        ∃ a : pairSubspaceLoopPiZeroHomotopyGroup A x,
          pairLoopSubspaceInclusionPiZeroMap A x a = g :=
  (pairHomotopyLongExactSequenceTail A x).1

/-- The second exactness clause in the tail
`π_1(X, x) ⟶ π_1(X, A, x) ⟶ π₀(A)`. -/
theorem pairHomotopyLongExactSequenceTail_exact_ambient_to_relative (A : Set X) (x : A) :
    ∀ r : pairRelativePiZeroHomotopyGroup A x,
      pairHomotopyBoundaryZeroMap A x r = ⟦x⟧ ↔
        ∃ g : pairAmbientLoopPiZeroHomotopyGroup A x,
          pairLoopToRelativePiZeroMap A x g = r :=
  (pairHomotopyLongExactSequenceTail A x).2.1

/-- The third exactness clause in the tail
`π_1(X, A, x) ⟶ π₀(A) ⟶ π₀(X)`. -/
theorem pairHomotopyLongExactSequenceTail_exact_boundary_to_piZero (A : Set X) (x : A) :
    ∀ a₀ : ZerothHomotopy A,
      zerothHomotopyInclusion A a₀ = ⟦(x : X)⟧ ↔
        ∃ r : pairRelativePiZeroHomotopyGroup A x,
          pairHomotopyBoundaryZeroMap A x r = a₀ :=
  (pairHomotopyLongExactSequenceTail A x).2.2
