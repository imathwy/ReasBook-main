import Mathlib.Data.PNat.Basic
import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Problem_9_7_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Problem_15_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.KPiOne

open CategoryTheory Limits
open scoped ContinuousMap Topology Topology.Homotopy
open scoped HomotopyClasses

universe u v w

-- Local declaration justification (notation): the Chapter 8-15 pointed-space API is written over
-- `Under (⊤_ TopCat)`, and this owner spelling avoids repeated universe mismatches in `Ho*`
-- quotient goals.
local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall: `lean_leansearch` surfaced `HomotopyGroup.Pi`; Chapter 15 precedent in this
-- repository uses `TopCat.CWComplex` for CW-complex structure and `≃ₕ` for homotopy equivalence.
-- No canonical `K(π,n)` owner was found in this environment, so the source is formalized via the
-- standard property characterizing pointed `K(π,n)` models.

/-- A pointed space `(X, x)` is a `K(π,n)` model if it is connected, admits a CW-complex
structure, has `π_ (n : ℕ) X x ≃* π`, and every other positive homotopy group is trivial. -/
class IsEilenbergMacLaneSpace (π : Type v) [Group π] (n : ℕ+) (X : TopCat.{u}) (x : X) : Prop
    extends ConnectedSpace X where
  cwComplex : Nonempty (TopCat.CWComplex X)
  homotopyGroupIso : Nonempty (π_ (n : ℕ) X x ≃* π)
  otherHomotopySubsingleton : ∀ m : ℕ+, m ≠ n → Subsingleton (π_ (m : ℕ) X x)

/-- A `K(π,n)` witness supplies both a CW-complex structure and the distinguished homotopy-group
identification in degree `n`. -/
theorem IsEilenbergMacLaneSpace.cwComplex_and_homotopyGroupIso
    {π : Type v} [Group π] {n : ℕ+} {X : TopCat.{u}} {x : X}
    (h : IsEilenbergMacLaneSpace π n X x) :
    Nonempty (TopCat.CWComplex X) ∧ Nonempty (π_ (n : ℕ) X x ≃* π) := by
  -- Unpack the two non-connectedness fields recorded in the structure.
  exact ⟨h.cwComplex, h.homotopyGroupIso⟩

/-- `IsEilenbergMacLaneSpace π n X x` is exactly the source-facing `K(π,n)` condition on the
pointed connected CW complex `(X, x)` for positive degree `n`. -/
theorem isEilenbergMacLaneSpace_iff {π : Type v} [Group π] {n : ℕ+} {X : TopCat.{u}} {x : X} :
    IsEilenbergMacLaneSpace π n X x ↔
      ConnectedSpace X ∧
        Nonempty (TopCat.CWComplex X) ∧
          Nonempty (π_ (n : ℕ) X x ≃* π) ∧
            ∀ m : ℕ+, m ≠ n → Subsingleton (π_ (m : ℕ) X x) := by
  constructor
  · intro h
    -- Read the source-facing owner field-by-field.
    exact ⟨h.toConnectedSpace, h.cwComplex, h.homotopyGroupIso, h.otherHomotopySubsingleton⟩
  · intro h
    rcases h with ⟨hconn, hcw, hiso, hother⟩
    -- Repackage the data into the `K(π,n)` owner.
    exact
      { toConnectedSpace := hconn
        cwComplex := hcw
        homotopyGroupIso := hiso
        otherHomotopySubsingleton := hother }

-- The generalized-loop, sphere-fiber, and basepoint-change owners are imported from Chapter 9 and
-- Problem 15.3.2.  Reuse those canonical declarations instead of redeclaring identical globals.

/-- Helper for Problem 15.3.6: a colimit of locally path connected spaces is locally path
connected. -/
theorem locPathConnectedSpaceOfIsColimit {J : Type*} [Category J] {F : J ⥤ TopCat}
    (c : Cocone F) (hc : IsColimit c) (hF : ∀ j, LocPathConnectedSpace (F.obj j)) :
    LocPathConnectedSpace c.pt := by
  let _ : ∀ j, LocPathConnectedSpace (F.obj j) := hF
  let desc : (Σ j, F.obj j) → c.pt := fun x ↦ c.ι.app x.1 x.2
  have hsurj : Function.Surjective desc := by
    intro x
    obtain ⟨j, y, rfl⟩ :=
      CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
        (F := F ⋙ forget TopCat) (t := (forget TopCat).mapCocone c)
        (isColimitOfPreserves (forget TopCat) hc) x
    exact ⟨⟨j, y⟩, rfl⟩
  have hquot : Topology.IsQuotientMap desc := by
    rw [Topology.isQuotientMap_iff]
    constructor
    · exact hsurj
    · intro U
      -- Openness on the sigma source is checked fiberwise via the colimit topology criterion.
      rw [isOpen_sigma_iff, TopCat.isOpen_iff_of_isColimit _ hc]
      refine forall_congr' fun j ↦ ?_
      change IsOpen ((fun x : F.obj j ↦ desc ⟨j, x⟩) ⁻¹' U) ↔ IsOpen ((c.ι.app j) ⁻¹' U)
      simp [desc]
  -- The colimit is a quotient of the sigma coproduct of the locally path connected stages.
  exact hquot.locPathConnectedSpace

/-- Helper for Problem 15.3.6: each disk `TopCat.disk n` is locally path connected. -/
theorem disk_locPathConnectedSpace (n : ℕ) : LocPathConnectedSpace (TopCat.disk n) := by
  -- The closed ball model of the disk is convex, hence locally path connected.
  let _ : LocPathConnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).locPathConnectedSpace
  -- The `ULift` wrapper used in `TopCat.disk` preserves the topology up to homeomorphism.
  simpa [TopCat.disk] using
    (Homeomorph.ulift.isOpenEmbedding.locPathConnectedSpace :
      LocPathConnectedSpace (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))

/-- Helper for Problem 15.3.6: attaching locally path connected cells preserves local path
connectedness. -/
theorem locPathConnectedSpaceOfAttachCells {α : Type*} {A B : α → TopCat}
    (g : ∀ a, A a ⟶ B a) {X₁ X₂ : TopCat} {f : X₁ ⟶ X₂}
    (c : HomotopicalAlgebra.AttachCells g f) (hX₁ : LocPathConnectedSpace X₁)
    (hB : ∀ a, LocPathConnectedSpace (B a)) : LocPathConnectedSpace X₂ := by
  let _ : LocPathConnectedSpace X₁ := hX₁
  let _ : ∀ a, LocPathConnectedSpace (B a) := hB
  let inlMap : X₁ ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) :=
    TopCat.ofHom ⟨Sum.inl, by continuity⟩
  let inrMap : c.cofan₂.pt ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) :=
    TopCat.ofHom ⟨Sum.inr, by continuity⟩
  let qLeft : c.cofan₁.pt ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) := c.g₁ ≫ inlMap
  let qRight : c.cofan₁.pt ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) := c.m ≫ inrMap
  let t : TopCat.of (X₁ ⊕ c.cofan₂.pt) ⟶ X₂ :=
    TopCat.ofHom
      { toFun := Sum.elim f c.g₂
        continuous_toFun := by
          continuity }
  have hcofork :
      CategoryTheory.Limits.IsColimit
        (Cofork.ofπ (f := qLeft) (g := qRight) t
          (by
            simpa [qLeft, qRight, t, inlMap, inrMap] using c.isPushout.w)) := by
    -- The coequalizer on the explicit sum coproduct restates the pushout universal property.
    refine CategoryTheory.Limits.Cofork.IsColimit.mk' _ ?_
    intro s
    let l : X₂ ⟶ s.pt :=
      c.isPushout.desc
        (inlMap ≫ s.π)
        (inrMap ≫ s.π)
        (by
          simpa using s.condition)
    refine ⟨l, ?_, ?_⟩
    · -- The descended map coequalizes the explicit sum map by the pushout equations.
      ext x
      cases x with
      | inl x =>
          exact ConcreteCategory.congr_hom
            (c.isPushout.inl_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)) x
      | inr x =>
          exact ConcreteCategory.congr_hom
            (c.isPushout.inr_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)) x
    · intro m hm
      apply c.isPushout.hom_ext
      · have hmInl : f ≫ m = inlMap ≫ s.π := by
          simpa [t, inlMap] using congrArg (fun k ↦ inlMap ≫ k) hm
        have hlInl : f ≫ l = inlMap ≫ s.π :=
          c.isPushout.inl_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)
        exact hmInl.trans hlInl.symm
      · have hmInr : c.g₂ ≫ m = inrMap ≫ s.π := by
          simpa [t, inrMap] using congrArg (fun k ↦ inrMap ≫ k) hm
        have hlInr : c.g₂ ≫ l = inrMap ≫ s.π :=
          c.isPushout.inr_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)
        exact hmInr.trans hlInr.symm
  have hcoprod₂ : LocPathConnectedSpace c.cofan₂.pt := by
    -- The cell coproduct is itself a colimit of the locally path connected cell spaces.
    exact locPathConnectedSpaceOfIsColimit c.cofan₂ c.isColimit₂ (fun i ↦ hB (c.π i.as))
  let _ : LocPathConnectedSpace (TopCat.of (X₁ ⊕ c.cofan₂.pt)) := by
    -- The pushout is a quotient of a disjoint union of locally path connected spaces.
    change LocPathConnectedSpace (X₁ ⊕ c.cofan₂.pt)
    infer_instance
  exact (TopCat.isQuotientMap_of_isColimit_cofork _ hcofork).locPathConnectedSpace

/-- Helper for Problem 15.3.6: every skeleton in an abstract CW complex is locally
path connected. -/
theorem cwStage_locPathConnectedSpace {Y : TopCat} (hY : TopCat.CWComplex Y) :
    ∀ n : ℕ, LocPathConnectedSpace (hY.F.obj n)
  | 0 => by
      let e : hY.F.obj 0 ≅ TopCat.of PEmpty :=
        hY.isoBot ≪≫ TopCat.initialIsoPEmpty
      have hEmpty : IsEmpty (hY.F.obj 0) := by
        refine ⟨fun x ↦ ?_⟩
        exact (e.hom x).elim
      -- The initial skeleton is empty, hence trivially locally path connected.
      let _ : LocPathConnectedSpace (hY.F.obj 0) := by
        rw [locPathConnectedSpace_iff_isOpen_pathComponentIn]
        intro x
        exact (hEmpty.false x).elim
      infer_instance
  | n + 1 => by
      have hn : ¬ IsMax n := not_isMax_iff.mpr ⟨n + 1, Nat.lt_succ_self n⟩
      -- The successor skeleton is obtained by attaching `n`-disks to the previous skeleton.
      simpa using
        locPathConnectedSpaceOfAttachCells
          (g := TopCat.RelativeCWComplex.basicCell n) (c := hY.attachCells n hn)
          (cwStage_locPathConnectedSpace hY n) (fun _ ↦ disk_locPathConnectedSpace n)

/-- Helper for Problem 15.3.6: an abstract CW-complex is locally path connected. -/
theorem locPathConnectedSpace_of_cwComplex {Y : TopCat} (hY : TopCat.CWComplex Y) :
    LocPathConnectedSpace Y := by
  -- Use the abstract CW colimit witness directly instead of the unavailable classical CW bridge.
  simpa using
    locPathConnectedSpaceOfIsColimit (c := Cocone.mk Y hY.incl) hY.isColimit
      (cwStage_locPathConnectedSpace hY)

/-- Helper for Problem 15.3.6: every positive-degree homotopy group below the distinguished
degree is trivial at the chosen basepoint of an Eilenberg-MacLane witness. -/
theorem subsingleton_pi_succ_le_of_isEilenbergMacLaneSpace
    {π : Type v} [Group π] (n q : ℕ) {X : BasedSpace}
    (hq : Nat.succ q ≤ n)
    (h : IsEilenbergMacLaneSpace π n.succPNat X.right (underTopBasepoint X)) :
    Subsingleton (π_ (Nat.succ q) X.right (underTopBasepoint X)) := by
  -- Any positive degree at most `n` is different from the unique nontrivial degree `n + 1`.
  have hneq : q.succPNat ≠ n.succPNat := by
    intro hEq
    have hEqNat : q.succ = n.succ :=
      congrArg (fun m : ℕ+ => (m : ℕ)) hEq
    exact (Nat.ne_of_lt (Nat.lt_succ_of_le hq)) hEqNat
  simpa using h.otherHomotopySubsingleton q.succPNat hneq

/-- Helper for Problem 15.3.6: a degree-one Eilenberg-MacLane witness is exactly a `K(π,1)`
witness. -/
theorem isKPiOne_of_isEilenbergMacLaneSpace_one
    {π : Type v} [Group π] {X : TopCat.{u}} {x : X}
    (h : IsEilenbergMacLaneSpace π 1 X x) :
    IsKPiOne π X x := by
  refine
    { toConnectedSpace := h.toConnectedSpace
      cwComplex := h.cwComplex
      pi1Iso := ?_
      higherHomotopySubsingleton := ?_ }
  · -- The distinguished degree is already `1`.
    simpa using h.homotopyGroupIso
  · intro n hn
    let m : ℕ+ := ⟨n, Nat.lt_trans Nat.zero_lt_one hn⟩
    have hm : m ≠ 1 := by
      -- The positive index `n` cannot equal `1` because we are in the `n > 1` branch.
      intro hEq
      exact (Nat.ne_of_gt hn) (congrArg (fun t : ℕ+ => (t : ℕ)) hEq)
    -- Reuse the vanishing of every homotopy group away from the distinguished degree.
    simpa [m] using h.otherHomotopySubsingleton m hm

/-- Helper for Problem 15.3.6: an Eilenberg-MacLane witness is path connected because it is both
connected and locally path connected. -/
theorem pathConnected_of_isEilenbergMacLaneSpace
    {π : Type v} [Group π] {n : ℕ+} {X : TopCat.{u}} {x : X}
    (h : IsEilenbergMacLaneSpace π n X x) :
    PathConnectedSpace X := by
  rcases h.cwComplex with ⟨hCW⟩
  let _ : ConnectedSpace X := h.toConnectedSpace
  let _ : LocPathConnectedSpace X := locPathConnectedSpace_of_cwComplex hCW
  -- The abstract CW witness supplies local path connectedness, so connectedness upgrades to path
  -- connectedness.
  exact PathConnectedSpace.of_locPathConnectedSpace

/-- Helper for Problem 15.3.6: every non-distinguished positive homotopy group is trivial at any
basepoint of an Eilenberg-MacLane witness. -/
theorem otherHomotopySubsingleton_atAnyBasepoint
    {π : Type v} [Group π] {n : ℕ+} {X : TopCat.{u}} {x₀ : X}
    (h : IsEilenbergMacLaneSpace π n X x₀) [PathConnectedSpace X] :
    ∀ x : X, ∀ m : ℕ+, m ≠ n → Subsingleton (π_ (m : ℕ) X x) := by
  -- TODO: bridge the abstract CW witness to the CGWH hypotheses required by the current
  -- basepoint-change API, then transport `h.otherHomotopySubsingleton m hm` along a path.
  sorry

/-- Helper for Problem 15.3.6: if the source homotopy group is already subsingleton, then the
induced map on that homotopy group is automatically injective. -/
theorem eStar_injective_of_subsingleton_domain
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : C(A, B)) (q : ℕ) (a : A) [Subsingleton (π_ q A a)] :
    Function.Injective (e.eStar q a) := by
  intro x y _hxy
  -- The source homotopy group already has only one element.
  exact Subsingleton.elim _ _

/-- Helper for Problem 15.3.6: if the target homotopy group is already subsingleton, then the
induced map on that homotopy group is automatically surjective. -/
theorem eStar_surjective_of_subsingleton_codomain
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : C(A, B)) (q : ℕ) (a : A) [Subsingleton (π_ q B (e a))] :
    Function.Surjective (e.eStar q a) := by
  intro b
  refine ⟨(⟦(GenLoop.const : Ω^ (Fin q) A a)⟧ : π_ q A a), ?_⟩
  -- Every target class agrees with the image of the constant representative.
  exact Subsingleton.elim _ _

/-- Helper for Problem 15.3.6: between path-connected spaces, every continuous map is already a
`0`-equivalence because both `π₀` groups are trivial. -/
theorem isNEquivalenceZero_of_pathConnected
    {Y Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : C(Y, Z)) [PathConnectedSpace Y] [PathConnectedSpace Z] :
    IsNEquivalence 0 e := by
  refine ⟨?_, ?_⟩
  · intro y q hq
    -- There are no negative homotopy groups below degree `0`.
    exact False.elim (Nat.not_lt_zero _ hq)
  · intro y q hq
    have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
    subst hq0
    intro a
    let b : π_ 0 Y y := (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := y)).symm ⟦y⟧
    refine ⟨b, ?_⟩
    -- Both source and target degree-`0` groups are subsingletons in the path-connected case.
    let _ : Subsingleton (π_ 0 Z (e y)) :=
      NConnectedSpace.pi0SubsingletonOfPathConnected (X := Z) (x := e y)
    exact Subsingleton.elim _ _

-- The stagewise `n`-equivalence assembly lemmas are owned by Theorem 10.5.1 and imported through
-- Problem 15.3.2; this file only consumes them.

/-- Helper for Problem 15.3.6: any element of `π_q(Y)` is represented by a concrete based sphere
map once a Hurewicz comparison in degree `q` is fixed. -/
theorem sphereRepresentative_of_piElement
    (q : ℕ) {Y : BasedSpace} (comparison : HurewiczComparison q Y)
    (a : π_ q Y.right (underTopBasepoint Y)) :
    ∃ f : basedSphere q ⟶ Y,
      comparison.ofSphereClass
        ((Quotient.mk (basedHomotopySetoid (basedSphere q) Y) f) :
          basedHomotopyClasses (basedSphere q) Y) = a := by
  rcases Quotient.exists_rep (comparison.toSphereClass a) with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  -- Replace the abstract class with a chosen representative and then evaluate the comparison.
  simpa using congrArg comparison.ofSphereClass hf

/-- Helper for Problem 15.3.6: any element of `π_ q(Y)` is represented by a concrete generalized
loop in the quotient model used by `π_ q`. -/
theorem genLoopRepresentative_of_piElement
    {q : ℕ} {Y : BasedSpace}
    (a : π_ q Y.right (underTopBasepoint Y)) :
    ∃ γ : Ω^ (Fin q) Y.right (underTopBasepoint Y),
      ((Quotient.mk' γ) : π_ q Y.right (underTopBasepoint Y)) = a := by
  -- Choose a quotient representative of the given homotopy-group class.
  rcases Quotient.exists_rep a with ⟨γ, rfl⟩
  exact ⟨γ, rfl⟩

/-- Helper for Problem 15.3.6: a homotopy relative to the chosen basepoint induces a homotopy of
generalized loops after postcomposition, still relative to the cube boundary. -/
theorem genLoopMap_homotopicRel_of_homotopyRel_singleton
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {f g : C(A, B)} (H : f.HomotopyRel g ({a} : Set A)) (m : ℕ)
    (γ : Ω^ (Fin m) A a) :
    (genLoopMap f γ).1.HomotopicRel (genLoopMap g γ).1 (Cube.boundary (Fin m)) := by
  -- Postcompose the singleton-relative homotopy with the generalized loop representative.
  refine ⟨{
    toHomotopy := H.toHomotopy.compContinuousMap γ.1
    prop' := ?_
  }⟩
  intro t x hx
  have hx' : γ x ∈ ({a} : Set A) := by
    simpa using γ.2 x hx
  simpa using H.prop t (γ x) hx'

/-- Helper for Problem 15.3.6: postcomposition with continuous maps composes on generalized loop
representatives. -/
private theorem genLoopMap_comp
    {A : Type u} {B : Type v} {C : Type max u v}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) {q : ℕ} {a : A} (γ : Ω^ (Fin q) A a) :
    genLoopMap g (genLoopMap f γ) = genLoopMap (g.comp f) γ := by
  -- Compare the two postcomposed loops pointwise.
  ext t
  rfl

/-- Helper for Problem 15.3.6: postcomposing a generalized loop and then transporting its target
basepoint along `hf` yields a generalized loop based at `b`. -/
private theorem genLoopMapOverEqLoop_boundary
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (q : ℕ)
    (γ : Ω^ (Fin q) A a) :
    ∀ t ∈ Cube.boundary (Fin q), (genLoopMap f γ).1 t = b := by
  intro t ht
  calc
    (genLoopMap f γ).1 t = f a := by
      simpa using congrArg f (γ.2 t ht)
    _ = b := hf

/-- Helper for Problem 15.3.6: the postcomposed generalized loop, regarded at the target
basepoint fixed by `hf`. -/
private def genLoopMapOverEqLoop
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) {q : ℕ}
    (γ : Ω^ (Fin q) A a) :
    Ω^ (Fin q) B b :=
  ⟨(genLoopMap f γ).1, genLoopMapOverEqLoop_boundary f hf q γ⟩

/-- Helper for Problem 15.3.6: the specialized homotopy-group map sends a representative to the
postcomposed loop viewed at the target basepoint chosen by `hf`. -/
private theorem homotopyGroupMapOverEq_mk
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (q : ℕ)
    (γ : Ω^ (Fin (q + 1)) A a) :
    homotopyGroupMapOverEq f hf q ⟦γ⟧ =
      (⟦genLoopMapOverEqLoop f hf γ⟧ : π_ (q + 1) B b) := by
  -- Reduce to the definitional case where the target basepoint is literally `f a`.
  cases hf
  simpa [homotopyGroupMapOverEq, genLoopMapOverEqLoop] using homotopyGroupMap_mk f q a γ

/-- Helper for Problem 15.3.6: the canonical comparison map sending a based map between pointed
`K(π, n + 1)` models to the induced endomorphism of the distinguished homotopy group `π`. -/
noncomputable def eilenbergMacLaneBasedMapToHom
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π) :
    (X ⟶ Y) → (π →* π) :=
  fun f ↦
    eY.toMonoidHom.comp
      ((f.right.hom.eStarMulHomOverEq n (fundamentalGroupFunctorMap_basepoint f)).comp
        eX.symm.toMonoidHom)

/-- Helper for Problem 15.3.6: if the classifier of a based map is `MonoidHom.id π`, then on the
distinguished homotopy group the induced transported map is exactly the comparison
`eY.symm.toMonoidHom.comp eX.toMonoidHom`. -/
theorem eStarMulHomOverEq_eq_of_classifier_id
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    (f : X ⟶ Y)
    (hf : eilenbergMacLaneBasedMapToHom n eX eY f = MonoidHom.id π) :
    f.right.hom.eStarMulHomOverEq n (fundamentalGroupFunctorMap_basepoint f) =
      eY.symm.toMonoidHom.comp eX.toMonoidHom := by
  -- Compare the two monoid homomorphisms after evaluating on an arbitrary source class.
  ext x
  apply eY.injective
  -- Evaluating the classifier identity on `eX x` rewrites the distinguished-degree map.
  simpa [eilenbergMacLaneBasedMapToHom, MonoidHom.comp_apply] using
    congrArg (fun h : π →* π ↦ h (eX x)) hf

/-- Helper for Problem 15.3.6: a based map classified by `MonoidHom.id π` is bijective on the
distinguished homotopy group at the chosen basepoints. -/
theorem eStarMulHomOverEq_bijective_of_classifier_id
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    (f : X ⟶ Y)
    (hf : eilenbergMacLaneBasedMapToHom n eX eY f = MonoidHom.id π) :
    Function.Bijective
      (f.right.hom.eStarMulHomOverEq n (fundamentalGroupFunctorMap_basepoint f)) := by
  -- Rewrite the induced map to the comparison built from the chosen `π_(n+1) ≃ π` witnesses.
  rw [eStarMulHomOverEq_eq_of_classifier_id n eX eY f hf]
  simpa using (eX.trans eY.symm).bijective

/-- Helper for Problem 15.3.6: a homotopy relative to a singleton gives the same transported map
on positive-degree homotopy groups after both endpoints are identified with one chosen basepoint.
-/
theorem homotopyGroupMapOverEq_eq_of_homotopyRel_singleton
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} {f g : C(A, B)}
    (H : f.HomotopyRel g ({a} : Set A)) (hf : f a = b) (hg : g a = b) (n : ℕ) :
    homotopyGroupMapOverEq f hf n = homotopyGroupMapOverEq g hg n := by
  -- Compare the two specialized maps pointwise on quotient representatives.
  funext x
  refine Quotient.inductionOn x ?_
  intro γ
  rw [homotopyGroupMapOverEq_mk f hf n γ, homotopyGroupMapOverEq_mk g hg n γ]
  -- The singleton-relative homotopy gives a boundary-relative homotopy of the loop representatives.
  exact Quotient.sound (genLoopMap_homotopicRel_of_homotopyRel_singleton H (n + 1) γ)

/-- Helper for Problem 15.3.6: changing only the proof of the target-basepoint equality does not
change `ContinuousMap.eStarMulHomOverEq`. -/
theorem eStarMulHomOverEq_proofIrrel
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (n : ℕ) (h₁ h₂ : f a = b) :
    f.eStarMulHomOverEq n h₁ = f.eStarMulHomOverEq n h₂ := by
  -- The endpoint witness is proposition-valued, so the defining transport is proof irrelevant.
  cases h₁
  cases h₂
  rfl

/-- Helper for Problem 15.3.6: applying `eStarMulHomOverEq` is the same as applying the
specialized positive-degree homotopy-group map with the same endpoint witness. -/
theorem eStarMulHomOverEq_apply
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (n : ℕ) (x : π_ (n + 1) A a) :
    f.eStarMulHomOverEq n hf x = homotopyGroupMapOverEq f hf n x := by
  -- Normalize the endpoint witness so both sides reduce to the same underlying map.
  cases hf
  rfl

/-- Helper for Problem 15.3.6: a classifier-id based map is already bijective on the normalized
distinguished homotopy-group comparison at the chosen basepoint. -/
theorem eStar_bijective_at_underTopBasepoint_of_classifier_id
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    (f : X ⟶ Y)
    (hf : eilenbergMacLaneBasedMapToHom n eX eY f = MonoidHom.id π) :
    Function.Bijective
      (f.right.hom.eStarMulHomOverEq n (fundamentalGroupFunctorMap_basepoint f)) := by
  -- The classifier identity already makes the normalized chosen-basepoint map bijective.
  exact eStarMulHomOverEq_bijective_of_classifier_id n eX eY f hf

/-- Helper for Problem 15.3.6: a homotopy relative to a singleton induces the same transported
positive-degree monoid hom after both endpoints are identified with one chosen basepoint. -/
theorem eStarMulHomOverEq_eq_of_homotopyRel_singleton
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} {f g : C(A, B)}
    (H : f.HomotopyRel g ({a} : Set A)) (hf : f a = b) (hg : g a = b) (n : ℕ) :
    f.eStarMulHomOverEq n hf = g.eStarMulHomOverEq n hg := by
  -- Reduce the monoid-hom equality to equality of the underlying transported maps.
  ext x
  -- Normalize both bundled maps to the representative-level transport map on `π_(n + 1)`.
  rw [eStarMulHomOverEq_apply f hf n x, eStarMulHomOverEq_apply g hg n x]
  -- The previously established singleton-relative homotopy invariance now closes the goal.
  exact congrFun (homotopyGroupMapOverEq_eq_of_homotopyRel_singleton H hf hg n) x

/-- Helper for Problem 15.3.6: composing the successor-degree transported monoid homs agrees
with transporting along the composite map. -/
theorem eStarMulHomOverEq_comp
    {A : Type u} {B : Type v} {C : Type max u v}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {a : A} {b : B} {c : C}
    (f : C(A, B)) (hf : f a = b) (g : C(B, C)) (hg : g b = c) (n : ℕ) :
    (g.eStarMulHomOverEq n hg).comp (f.eStarMulHomOverEq n hf) =
      (g.comp f).eStarMulHomOverEq n
        (by simpa [ContinuousMap.comp_apply, hf] using hg) := by
  -- Normalize the endpoint witnesses first so both sides act on the same loop representatives.
  cases hf
  cases hg
  ext x
  refine Quotient.inductionOn x ?_
  intro γ
  -- After unfolding the transported maps, both sides are induced by the same composite loop map.
  simpa [MonoidHom.comp_apply, ContinuousMap.eStarMulHomOverEq_rfl, homotopyGroupMap_mk] using
    congrArg (fun δ ↦ (⟦δ⟧ : π_ (n + 1) C ((g.comp f) a))) (genLoopMap_comp f g γ)

/-- Helper for Problem 15.3.6: based-homotopic representatives induce the same comparison
endomorphism on the distinguished homotopy group. -/
theorem eilenbergMacLaneBasedMapToHom_eq_of_basedHomotopyRel
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    {f g : X ⟶ Y}
    (hfg : basedHomotopyRel f g) :
    eilenbergMacLaneBasedMapToHom n eX eY f =
      eilenbergMacLaneBasedMapToHom n eX eY g := by
  obtain ⟨H⟩ := hfg
  -- Reduce equality of monoid homomorphisms to the transported map on `π_(n + 1)`.
  ext a
  -- The singleton-relative homotopy bridge applies at the chosen basepoint of `X`.
  simpa [eilenbergMacLaneBasedMapToHom, MonoidHom.comp_apply] using
    congrArg eY
      (congrArg
        (fun h :
          π_ (n + 1) X.right (underTopBasepoint X) →*
            π_ (n + 1) Y.right (underTopBasepoint Y) ↦ h (eX.symm a))
        (eStarMulHomOverEq_eq_of_homotopyRel_singleton H
          (fundamentalGroupFunctorMap_basepoint f) (fundamentalGroupFunctorMap_basepoint g) n))

/-- Helper for Problem 15.3.6: the comparison endomorphism depends only on the based homotopy
class of the representing map. -/
theorem eilenbergMacLaneBasedMapToHom_eq_of_basedHomotopy
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    {f g : X ⟶ Y}
    (hfg : (basedHomotopySetoid X Y).r f g) :
    eilenbergMacLaneBasedMapToHom n eX eY f =
      eilenbergMacLaneBasedMapToHom n eX eY g := by
  -- Induct through the equivalence closure generated by based homotopies.
  induction hfg with
  | rel _ _ h =>
      exact eilenbergMacLaneBasedMapToHom_eq_of_basedHomotopyRel n eX eY h
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Helper for Problem 15.3.6: the canonical comparison descends from representatives to based
homotopy classes. -/
noncomputable def eilenbergMacLaneBasedHomotopyClassesToHom
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π) :
    Ho*[X, Y] → (π →* π) :=
  Quotient.lift (eilenbergMacLaneBasedMapToHom n eX eY)
    (fun _ _ hfg ↦ eilenbergMacLaneBasedMapToHom_eq_of_basedHomotopy n eX eY hfg)

/-- Helper for Problem 15.3.6: the class of a representative based map is sent to its induced
endomorphism on the distinguished homotopy group. -/
noncomputable abbrev eilenbergMacLaneBasedHomotopyClassToHom
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    (f : X ⟶ Y) :
    π →* π :=
  eilenbergMacLaneBasedHomotopyClassesToHom n eX eY
    ((Quotient.mk (basedHomotopySetoid X Y) f) : Ho*[X, Y])

/-- Helper for Problem 15.3.6: the identity based map induces the identity endomorphism of `π`
under the canonical comparison. -/
theorem eilenbergMacLaneBasedMapToHom_id
    {π : Type v} [Group π] (n : ℕ)
    {X : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π) :
    eilenbergMacLaneBasedMapToHom n eX eX (𝟙 X) = MonoidHom.id π := by
  -- Once the identity basepoint equation is normalized, the induced map on homotopy groups is
  -- literally `id`.
  ext a
  have hId : (𝟙 X : X ⟶ X).right.hom (underTopBasepoint X) = underTopBasepoint X :=
    fundamentalGroupFunctorMap_basepoint (𝟙 X : X ⟶ X)
  revert hId
  intro hId
  cases hId
  change eX (((ContinuousMap.id X.right).eStar (n + 1) (underTopBasepoint X)) (eX.symm a)) = a
  simp [homotopyGroupMap_id]

/-- Helper for Problem 15.3.6: the canonical comparison sends composites of based maps to
composites of the resulting endomorphisms of `π`. -/
theorem eilenbergMacLaneBasedMapToHom_comp
    {π : Type v} [Group π] (n : ℕ)
    {X Y Z : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    (eZ : π_ (n + 1) Z.right (underTopBasepoint Z) ≃* π)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    eilenbergMacLaneBasedMapToHom n eX eZ (f ≫ g) =
      (eilenbergMacLaneBasedMapToHom n eY eZ g).comp
        (eilenbergMacLaneBasedMapToHom n eX eY f) := by
  -- Compare both composite homomorphisms pointwise on `π`.
  ext a
  have hf : f.right.hom (underTopBasepoint X) = underTopBasepoint Y :=
    fundamentalGroupFunctorMap_basepoint f
  have hg : g.right.hom (underTopBasepoint Y) = underTopBasepoint Z :=
    fundamentalGroupFunctorMap_basepoint g
  have hcomp : (f ≫ g).right.hom (underTopBasepoint X) = underTopBasepoint Z :=
    fundamentalGroupFunctorMap_basepoint (f ≫ g)
  have hcompEq :
      (f ≫ g).right.hom.eStarMulHomOverEq n hcomp =
        ((g.right.hom.eStarMulHomOverEq n hg).comp (f.right.hom.eStarMulHomOverEq n hf)) := by
    calc
      (f ≫ g).right.hom.eStarMulHomOverEq n hcomp
          = (g.right.hom.comp f.right.hom).eStarMulHomOverEq n
              (by simpa [ContinuousMap.comp_apply, hf] using hg) := by
                simpa using
                  (eStarMulHomOverEq_proofIrrel ((f ≫ g).right.hom) n
                    hcomp (by simpa [ContinuousMap.comp_apply, hf] using hg))
      _ = (g.right.hom.eStarMulHomOverEq n hg).comp (f.right.hom.eStarMulHomOverEq n hf) := by
            simpa using (eStarMulHomOverEq_comp f.right.hom hf g.right.hom hg n).symm
  simpa [eilenbergMacLaneBasedMapToHom, MonoidHom.comp_apply] using
    congrArg eZ
      (congrArg
        (fun h :
          π_ (n + 1) X.right (underTopBasepoint X) →*
            π_ (n + 1) Z.right (underTopBasepoint Z) ↦ h (eX.symm a))
        hcompEq)

/-- Helper for Problem 15.3.6: equality in the based-homotopy setoid forgets to an ordinary
homotopy of the underlying continuous maps. -/
theorem homotopic_of_basedHomotopySetoid
    {X Y : BasedSpace} {f g : X ⟶ Y}
    (hfg : (basedHomotopySetoid X Y).r f g) :
    f.right.hom.Homotopic g.right.hom := by
  -- Forget the basepoint condition at each generating step and then follow the equivalence
  -- closure.
  induction hfg with
  | rel _ _ h =>
      obtain ⟨H⟩ := h
      exact ⟨H.toHomotopy⟩
  | refl _ =>
      exact ContinuousMap.Homotopic.refl _
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Helper for Problem 15.3.6: equality of based homotopy classes implies an ordinary homotopy of
their chosen representatives. -/
theorem homotopic_of_basedHomotopyClass_eq
    {X Y : BasedSpace} {f g : X ⟶ Y}
    (hfg : ((Quotient.mk _ f) : Ho*[X, Y]) = ((Quotient.mk _ g) : Ho*[X, Y])) :
    f.right.hom.Homotopic g.right.hom := by
  -- Extract the generated based-homotopy relation from the quotient equality and forget the
  -- basepoint condition.
  have hsetoid : (basedHomotopySetoid X Y).r f g := Quotient.exact hfg
  rw [basedHomotopySetoid_iff] at hsetoid
  have hEquiv : Equivalence (fun a b : X ⟶ Y ↦ basedHomotopyRel a b) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨ContinuousMap.HomotopyRel.refl a.right.hom (basedBasepointSet X)⟩
    · intro a b hab
      exact hab.elim fun H ↦ ⟨H.symm⟩
    · intro a b c hab hbc
      exact hab.elim fun Hab ↦ hbc.elim fun Hbc ↦ ⟨Hab.trans Hbc⟩
  have hrel : basedHomotopyRel f g := (Equivalence.eqvGen_iff hEquiv).1 hsetoid
  obtain ⟨H⟩ := hrel
  exact ⟨H.toHomotopy⟩

/-- Helper for Problem 15.3.6: a based-class equality of self-maps on `underTopOfPoint Z z`
forgets to an ordinary homotopy of the underlying continuous maps. -/
theorem homotopic_of_underTopClass_eq
    {Z : TopCat.{max u v}} (z : Z)
    {f g : underTopOfPoint Z z ⟶ underTopOfPoint Z z}
    (hfg : ((Quotient.mk _ f) : Ho*[underTopOfPoint Z z, underTopOfPoint Z z]) =
      ((Quotient.mk _ g) : Ho*[underTopOfPoint Z z, underTopOfPoint Z z])) :
    f.right.hom.Homotopic g.right.hom := by
  let W : BasedSpace := underTopOfPoint Z z
  have hfgW : ((Quotient.mk _ f) : Ho*[W, W]) = ((Quotient.mk _ g) : Ho*[W, W]) := by
    simpa [W] using hfg
  -- This is exactly the generic quotient-forgetting statement specialized to the pointed space
  -- obtained from `Z` by choosing `z` as basepoint.
  simpa using
    (homotopic_of_basedHomotopyClass_eq
      (X := W) (Y := W) hfgW)

/-- Helper for Problem 15.3.6: the classifier endgame repeatedly reduces composite self-classes
to the composite of two identity endomorphisms of `π`. -/
private theorem monoidHom_id_comp_id
    {π : Type v} [Group π] :
    (MonoidHom.id π).comp (MonoidHom.id π) = MonoidHom.id π := by
  -- The identity endomorphism is neutral under composition.
  ext a
  rfl

/-- Helper for Problem 15.3.6: the canonical `π₁`/fundamental-group bridge commutes with
postcomposition on loop representatives. -/
private theorem genLoopEquivOfUnique_genLoopMap_eq_pathMap
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} (γ : Ω^ (Fin 1) A a) :
    genLoopEquivOfUnique (X := B) (x := f a) (Fin 1) (genLoopMap f γ) =
      (genLoopEquivOfUnique (X := A) (x := a) (Fin 1) γ).map f.continuous := by
  -- Both paths evaluate the unique cube coordinate and then postcompose by `f`.
  ext t
  rfl

/-- Helper for Problem 15.3.6: the degree-one transported map on homotopy groups is exactly the
induced map on fundamental groups after applying the canonical `π₁ ≃ FundamentalGroup` bridge. -/
private theorem piOneEStarMulHomOverEq_eq_fundamentalGroupMapOfEq
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (h : f a = b) :
    (HomotopyGroup.pi1MulEquivFundamentalGroup b).toMonoidHom.comp (f.eStarMulHomOverEq 0 h) =
      (FundamentalGroup.mapOfEq f h).comp (HomotopyGroup.pi1MulEquivFundamentalGroup a).toMonoidHom := by
  -- Normalize the endpoint witness first so the induced map is computed at the literal target
  -- basepoint `f a`.
  cases h
  ext x
  refine Quotient.inductionOn x ?_
  intro γ
  -- After unfolding the quotient representatives, both sides apply `f` to the same loop.
  change
    Path.Homotopic.Quotient.mk
      (genLoopEquivOfUnique (X := B) (x := f a) (Fin 1) (genLoopMap f γ)) =
    FundamentalGroup.mapOfEq f rfl (Path.Homotopic.Quotient.mk
      (genLoopEquivOfUnique (X := A) (x := a) (Fin 1) γ))
  rw [FundamentalGroup.mapOfEq_apply]
  exact congrArg Path.Homotopic.Quotient.mk
    (genLoopEquivOfUnique_genLoopMap_eq_pathMap f γ)

/-- Helper for Problem 15.3.6: on the zero branch, the based-map classifier is the conjugate of
the induced fundamental-group map by the chosen `FundamentalGroup ≃* π` identifications coming
from the canonical `π₁` bridge. -/
theorem eilenbergMacLaneBasedMapToHom_zero_eq_fundamentalGroupClassifier
    {π : Type v} [Group π]
    {X Y : BasedSpace}
    (eX : π_ 1 X.right (underTopBasepoint X) ≃* π)
    (eY : π_ 1 Y.right (underTopBasepoint Y) ≃* π)
    (f : X ⟶ Y) :
    eilenbergMacLaneBasedMapToHom 0 eX eY f =
      (((HomotopyGroup.pi1MulEquivFundamentalGroup (underTopBasepoint Y)).symm.trans eY).toMonoidHom).comp
        ((FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)).comp
          (((HomotopyGroup.pi1MulEquivFundamentalGroup
              (underTopBasepoint X)).symm.trans eX).symm.toMonoidHom)) := by
  have hfg := piOneEStarMulHomOverEq_eq_fundamentalGroupMapOfEq f.right.hom
    (fundamentalGroupFunctorMap_basepoint f)
  -- Route correction: isolate the `π₁`/fundamental-group normalization once, so the degree-one
  -- branch can work entirely on the fundamental-group classifier surface.
  ext a
  simpa [eilenbergMacLaneBasedMapToHom, MonoidHom.comp_apply] using
    congrArg
      (fun h :
        π_ 1 X.right (underTopBasepoint X) →*
          FundamentalGroup Y.right (underTopBasepoint Y) ↦
        ((HomotopyGroup.pi1MulEquivFundamentalGroup (underTopBasepoint Y)).symm.trans eY)
          (h (eX.symm a))) hfg

-- Helper for Problem 15.3.6: a based map between pointed `K(π,n + 1)` models whose classifier
-- is `MonoidHom.id π` should be a weak equivalence of the underlying continuous maps.
-- Route correction: the main theorem only needs one classifier-id representative upgraded to a
-- weak equivalence, so the remaining work should package this structural step directly.
/-- Helper for Problem 15.3.6: a classifier-id based map controls the two-stage `π_*` data in
every degree once the distinguished-degree comparison is transported to all basepoints. -/
-- TODO: the remaining local blocker is owner-level Chapter 9 basepoint transport for absolute
-- homotopy groups, together with its naturality for `eStar`. With those in hand, one transports
-- the away-from-`n + 1` vanishing and the distinguished-degree bijection from
-- `underTopBasepoint X` to arbitrary basepoints and then applies the Chapter 10 weak-equivalence
-- assembler.
theorem hasPiInjectiveSurjectiveSuccAll_of_classifier_id
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    (hX : IsEilenbergMacLaneSpace π n.succPNat X.right (underTopBasepoint X))
    (hY : IsEilenbergMacLaneSpace π n.succPNat Y.right (underTopBasepoint Y))
    (f : X ⟶ Y)
    (hf : eilenbergMacLaneBasedMapToHom n eX eY f = MonoidHom.id π) :
    ∀ m : ℕ, HasPiInjectiveSurjectiveSucc m f.right.hom := by
  let _ : PathConnectedSpace X.right := pathConnected_of_isEilenbergMacLaneSpace hX
  let _ : PathConnectedSpace Y.right := pathConnected_of_isEilenbergMacLaneSpace hY
  have hOtherX := otherHomotopySubsingleton_atAnyBasepoint hX
  have hOtherY := otherHomotopySubsingleton_atAnyBasepoint hY
  have hDistinguishedBase :
      Function.Bijective
        (f.right.hom.eStarMulHomOverEq n (fundamentalGroupFunctorMap_basepoint f)) :=
    eStar_bijective_at_underTopBasepoint_of_classifier_id n eX eY f hf
  have hDistinguished :
      ∀ x : X.right, Function.Bijective (f.right.hom.eStar (n + 1) x) := by
    intro x
    -- Route correction: the chosen-basepoint bijection is now closed above. The only remaining
    -- blocker is the owner-level path-conjugation lemma transporting that bijection from
    -- `underTopBasepoint X` to the arbitrary basepoint `x`.
    -- TODO: choose `β : Path (underTopBasepoint X) x`, prove the normal form rewriting
    -- `f.right.hom.eStar (n + 1) x` as a conjugate of the chosen-basepoint map, and then
    -- transport `hDistinguishedBase` across the resulting source and target equivalences.
    sorry
  intro m
  refine ⟨?_, ?_⟩
  · intro x
    by_cases hmSucc : m = n + 1
    · -- At the distinguished degree, injectivity is exactly the remaining arbitrary-basepoint
      -- bijection blocker isolated above.
      subst hmSucc
      exact (hDistinguished x).1
    · cases m with
      | zero =>
          -- Away from the distinguished positive degree, path connectedness makes `π₀` trivial.
          let _ : Subsingleton (π_ 0 X.right x) :=
            NConnectedSpace.pi0SubsingletonOfPathConnected (X := X.right) (x := x)
          simpa using eStar_injective_of_subsingleton_domain f.right.hom 0 x
      | succ k =>
          -- In every other positive degree, the source homotopy group vanishes at `x`.
          let _ : Subsingleton (π_ (k + 1) X.right x) := by
            simpa using hOtherX x k.succPNat (by simpa using hmSucc)
          simpa using eStar_injective_of_subsingleton_domain f.right.hom (k + 1) x
  · intro x
    by_cases hm : m = n
    · -- Surjectivity in the unique nontrivial successor degree is the other half of the same
      -- distinguished-degree bijection blocker.
      subst hm
      exact (hDistinguished x).2
    · -- Every other successor degree has subsingleton target, so surjectivity is automatic.
      let _ : Subsingleton (π_ (m + 1) Y.right (f.right.hom x)) := by
        simpa using hOtherY (f.right.hom x) m.succPNat (by simpa using hm)
      simpa using eStar_surjective_of_subsingleton_codomain f.right.hom (m + 1) x

theorem isWeakEquivalence_of_classifier_id
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    (hX : IsEilenbergMacLaneSpace π n.succPNat X.right (underTopBasepoint X))
    (hY : IsEilenbergMacLaneSpace π n.succPNat Y.right (underTopBasepoint Y))
    (f : X ⟶ Y)
    (hf : eilenbergMacLaneBasedMapToHom n eX eY f = MonoidHom.id π) :
    IsWeakEquivalence f.right.hom := by
  let _ : PathConnectedSpace X.right := pathConnected_of_isEilenbergMacLaneSpace hX
  let _ : PathConnectedSpace Y.right := pathConnected_of_isEilenbergMacLaneSpace hY
  have h0 : IsNEquivalence 0 f.right.hom :=
    isNEquivalenceZero_of_pathConnected f.right.hom
  have hSteps : ∀ m : ℕ, HasPiInjectiveSurjectiveSucc m f.right.hom :=
    hasPiInjectiveSurjectiveSuccAll_of_classifier_id n eX eY hX hY f hf
  -- Assemble the path-connected `π₀` control and the stagewise `π_*` package into a weak
  -- equivalence.
  exact
    isWeakEquivalenceOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccAll h0 hSteps

/-- Helper for Problem 15.3.6: an abstract-CW weak equivalence of spaces should upgrade to an
actual homotopy equivalence with the same forward map. -/
-- Route correction: this isolates the real Whitehead support gap instead of reopening the old
-- branchwise uniqueness frontier.
-- TODO: bridge the abstract witness `TopCat.CWComplex` to the Whitehead theorem behind
-- `exists_homotopyEquiv_of_isWeakEquivalence`, or prove the direct abstract-CW model-category
-- upgrade on `TopCat`.
theorem topCatHomotopyEquiv_of_isWeakEquivalence_onAbstractCW
    {Y Z : TopCat.{w}} (e : C(Y, Z))
    (hCWY : Nonempty (TopCat.CWComplex Y))
    (hCWZ : Nonempty (TopCat.CWComplex Z))
    [IsWeakEquivalence e] :
    ∃ h : Y ≃ₕ Z, h.toFun = e := sorry

/-- Helper for Problem 15.3.6: the degree-one branch is reduced to finding a based map between
pointed `K(π,1)` models whose induced map on fundamental groups is the identity on `π`. -/
-- TODO: realize `MonoidHom.id π` on the fundamental-group surface for pointed `K(π,1)` models.
theorem kPiOneIdClassifierExists
    {π : Type v} [Group π]
    {X Y : BasedSpace}
    (φX : FundamentalGroup X.right (underTopBasepoint X) ≃* π)
    (φY : FundamentalGroup Y.right (underTopBasepoint Y) ≃* π)
    (hX : IsKPiOne π X.right (underTopBasepoint X))
    (hY : IsKPiOne π Y.right (underTopBasepoint Y)) :
    ∃ f : X ⟶ Y,
      φY.toMonoidHom.comp
        ((FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)).comp
          φX.symm.toMonoidHom) = MonoidHom.id π := sorry

/-- Helper for Problem 15.3.6: the successor branch is reduced to realizing the identity
classifier on the existing `GenLoop`/`eStarMulHomOverEq` surface. -/
-- TODO: stay on the normalized generalized-loop surface and realize `MonoidHom.id π`.
theorem genLoopIdClassifierExists
    {π : Type v} [Group π] (k : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (k + 2) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (k + 2) Y.right (underTopBasepoint Y) ≃* π)
    (hX : IsEilenbergMacLaneSpace π (Nat.succ k).succPNat X.right (underTopBasepoint X))
    (hY : IsEilenbergMacLaneSpace π (Nat.succ k).succPNat Y.right (underTopBasepoint Y)) :
    ∃ c : Ho*[X, Y],
      eilenbergMacLaneBasedHomotopyClassesToHom (Nat.succ k) eX eY c = MonoidHom.id π := sorry

/-- Helper for Problem 15.3.6: any two pointed `K(π,1)` models admit a based homotopy class whose
degree-one classifier is `MonoidHom.id π`. -/
-- Route correction: the degree-one branch only needs the identity classifier, not full
-- classification by arbitrary endomorphisms.
theorem existsBasedClassOfIdClassifierOne
    {π : Type v} [Group π]
    {X Y : BasedSpace}
    (eX : π_ 1 X.right (underTopBasepoint X) ≃* π)
    (eY : π_ 1 Y.right (underTopBasepoint Y) ≃* π)
    (hX : IsEilenbergMacLaneSpace π 1 X.right (underTopBasepoint X))
    (hY : IsEilenbergMacLaneSpace π 1 Y.right (underTopBasepoint Y)) :
    ∃ c : Ho*[X, Y], eilenbergMacLaneBasedHomotopyClassesToHom 0 eX eY c = MonoidHom.id π := by
  let hX1 : IsKPiOne π X.right (underTopBasepoint X) :=
    isKPiOne_of_isEilenbergMacLaneSpace_one hX
  let hY1 : IsKPiOne π Y.right (underTopBasepoint Y) :=
    isKPiOne_of_isEilenbergMacLaneSpace_one hY
  let φX : FundamentalGroup X.right (underTopBasepoint X) ≃* π :=
    (HomotopyGroup.pi1MulEquivFundamentalGroup (underTopBasepoint X)).symm.trans eX
  let φY : FundamentalGroup Y.right (underTopBasepoint Y) ≃* π :=
    (HomotopyGroup.pi1MulEquivFundamentalGroup (underTopBasepoint Y)).symm.trans eY
  -- The real degree-one work now lives in the fundamental-group core lemma.
  rcases kPiOneIdClassifierExists φX φY hX1 hY1 with ⟨f, hf⟩
  refine ⟨((Quotient.mk (basedHomotopySetoid X Y) f) : Ho*[X, Y]), ?_⟩
  -- Rewrite the quotient-level classifier to its representing map and then apply the adapter.
  calc
    eilenbergMacLaneBasedHomotopyClassesToHom 0 eX eY
        ((Quotient.mk (basedHomotopySetoid X Y) f) : Ho*[X, Y]) =
      eilenbergMacLaneBasedMapToHom 0 eX eY f := by
        rfl
    _ =
      φY.toMonoidHom.comp
        ((FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)).comp
          φX.symm.toMonoidHom) := by
            simpa [φX, φY] using
              eilenbergMacLaneBasedMapToHom_zero_eq_fundamentalGroupClassifier eX eY f
    _ = MonoidHom.id π := hf

/-- Helper for Problem 15.3.6: any two pointed `K(π, k + 2)` models admit a based homotopy class
whose distinguished-degree classifier is `MonoidHom.id π`. -/
-- TODO: stay on the `GenLoop`/`eStarMulHomOverEq` surface, realize the distinguished generator by
-- `genLoopRepresentative_of_piElement`, and extend it across higher cells using the low-degree
-- vanishing package from the Eilenberg-MacLane hypotheses.
theorem existsBasedClassOfIdClassifierSucc
    {π : Type v} [Group π] (k : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (k + 2) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (k + 2) Y.right (underTopBasepoint Y) ≃* π)
    (hX : IsEilenbergMacLaneSpace π (Nat.succ k).succPNat X.right (underTopBasepoint X))
    (hY : IsEilenbergMacLaneSpace π (Nat.succ k).succPNat Y.right (underTopBasepoint Y)) :
    ∃ c : Ho*[X, Y],
      eilenbergMacLaneBasedHomotopyClassesToHom (Nat.succ k) eX eY c = MonoidHom.id π := by
  -- The successor branch now delegates to the normalized generalized-loop core theorem.
  exact genLoopIdClassifierExists k eX eY hX hY

/-- Helper for Problem 15.3.6: between pointed `K(π, n + 1)` models there exists a based
homotopy class whose classifier is `MonoidHom.id π`. -/
theorem existsBasedClassOfIdClassifier
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    (hX : IsEilenbergMacLaneSpace π n.succPNat X.right (underTopBasepoint X))
    (hY : IsEilenbergMacLaneSpace π n.succPNat Y.right (underTopBasepoint Y)) :
    ∃ c : Ho*[X, Y], eilenbergMacLaneBasedHomotopyClassesToHom n eX eY c = MonoidHom.id π := by
  -- Dispatch to the degree-one or successor-degree identity-classifier realization.
  cases n with
  | zero =>
      exact existsBasedClassOfIdClassifierOne eX eY hX hY
  | succ k =>
      exact existsBasedClassOfIdClassifierSucc k eX eY hX hY

/-- Helper for Problem 15.3.6: an identity-classifier homotopy class has a representing based map
with the same classifier. -/
theorem existsBasedMapOfIdClassifier
    {π : Type v} [Group π] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* π)
    (hXY : ∃ c : Ho*[X, Y], eilenbergMacLaneBasedHomotopyClassesToHom n eX eY c = MonoidHom.id π) :
    ∃ f : X ⟶ Y, eilenbergMacLaneBasedMapToHom n eX eY f = MonoidHom.id π := by
  rcases hXY with ⟨c, hc⟩
  rcases Quotient.exists_rep c with ⟨f, rfl⟩
  -- Unfold the quotient-level classifier on the chosen representative.
  exact ⟨f, by simpa [eilenbergMacLaneBasedHomotopyClassesToHom] using hc⟩

/-- Problem 15.3.6: if `X` is a connected CW complex with exactly one nonzero homotopy group
`π_ (n : ℕ) X x ≃* π`, then any chosen pointed `K(π,n)` model is homotopy equivalent to `X`. -/
theorem homotopyEquivOfIsEilenbergMacLaneSpace
    (π : Type v) [Group π] (n : ℕ+) {X Y : TopCat.{max u v}} (x : X) (y : Y)
    (hY : IsEilenbergMacLaneSpace π n Y y) (hX : IsEilenbergMacLaneSpace π n X x) :
    Nonempty (Y ≃ₕ X) := by
  let Y₀ : BasedSpace := underTopOfPoint Y y
  let X₀ : BasedSpace := underTopOfPoint X x
  let k : ℕ := n.natPred
  -- Normalize both `K(π,n)` witnesses to the `k + 1` indexing used by the classifier theorem.
  have hY₀ : IsEilenbergMacLaneSpace π k.succPNat Y₀.right (underTopBasepoint Y₀) := by
    simpa [Y₀, k] using hY
  have hX₀ : IsEilenbergMacLaneSpace π k.succPNat X₀.right (underTopBasepoint X₀) := by
    simpa [X₀, k] using hX
  rcases hY₀.homotopyGroupIso with ⟨eYSucc⟩
  rcases hX₀.homotopyGroupIso with ⟨eXSucc⟩
  have eY : π_ (k + 1) Y₀.right (underTopBasepoint Y₀) ≃* π := by
    -- Reindex the distinguished degree once and then keep the normalized surface throughout.
    simpa [Y₀] using eYSucc
  have eX : π_ (k + 1) X₀.right (underTopBasepoint X₀) ≃* π := by
    -- The same normalization is used for `X`.
    simpa [X₀] using eXSucc
  rcases
      existsBasedMapOfIdClassifier (π := π) k eY eX
        (existsBasedClassOfIdClassifier (π := π) k eY eX hY₀ hX₀) with
    ⟨f, hf⟩
  let fYX := f.right.hom
  have hWeak : IsWeakEquivalence fYX := by
    -- Route correction: upgrade the single classifier-id representative directly to a weak
    -- equivalence instead of building an explicit inverse by classifying two composites.
    simpa [fYX] using isWeakEquivalence_of_classifier_id k eY eX hY₀ hX₀ f hf
  let _ : IsWeakEquivalence fYX := hWeak
  rcases
      topCatHomotopyEquiv_of_isWeakEquivalence_onAbstractCW fYX hY.cwComplex hX.cwComplex
    with ⟨e, _⟩
  -- The abstract-CW Whitehead bridge finishes once the single representative map is known to be
  -- a weak equivalence.
  exact ⟨e⟩
