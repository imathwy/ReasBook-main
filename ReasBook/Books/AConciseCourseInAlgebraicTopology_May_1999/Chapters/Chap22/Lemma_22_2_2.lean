import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Books.AConciseCourseInAlgebraicTopology_May_1999.PointedExact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.OnePointBasedSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_6_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.BasedHomotopyClasses

open CategoryTheory Limits
open BasedHomotopyClasses
open scoped HomotopyClasses unitInterval

noncomputable section

universe u v

variable {ι : Type v}

/-- Helper for Lemma 22.2.2: the coproduct of an empty family in `TopCat` is the initial object. -/
def emptyCofanIsColimit (X : ULift PEmpty → TopCat.{u}) :
    IsColimit (Cofan.mk (f := X) (⊥_ TopCat.{u}) (fun i ↦ PEmpty.elim i.down)) := by
  -- The empty coproduct is characterized by the initial map out of `⊥_ TopCat`.
  refine
    { desc := fun s ↦ initial.to s.pt
      fac := by
        intro s j
        rcases j with ⟨i⟩
        cases i with
        | up i =>
            cases i
      uniq := by
        intro s m hm
        exact initialIsInitial.hom_ext _ _ }

/-- Helper for Lemma 22.2.2: the coproduct of a singleton family in `TopCat` is the object
itself. -/
def unitCofanIsColimit (X : TopCat.{u}) :
    IsColimit (Cofan.mk (f := fun _ : ULift Unit ↦ X) X (fun _ : ULift Unit ↦ 𝟙 X)) := by
  -- A cocone over a singleton diagram is determined by its unique leg.
  refine
    { desc := fun s ↦ s.ι.app ⟨ULift.up ()⟩
      fac := by
        intro s j
        rcases j with ⟨j⟩
        cases j with
        | up j =>
            cases j
            simp
      uniq := by
        intro s m hm
        simpa using hm ⟨ULift.up ()⟩ }

/-- Helper for Lemma 22.2.2: the boundary of the `0`-disk is empty. -/
theorem diskBoundaryZeroIsEmpty : IsEmpty (TopCat.diskBoundary 0) := by
  -- In `Fin 0`, every vector is `0`, so the equation `dist x 0 = 1` is impossible.
  refine ⟨fun x ↦ ?_⟩
  rcases x with ⟨x⟩
  rcases x with ⟨x, hx⟩
  have hx0 : x = 0 := Subsingleton.elim _ _
  have h01 : (0 : ℝ) = 1 := by
    simp [Metric.sphere, hx0] at hx
  exact zero_ne_one h01

/-- Helper for Lemma 22.2.2: the `0`-disk has a unique point. -/
abbrev diskZeroUnique : Unique (TopCat.disk 0) := by
  -- The closed unit ball in `ℝ^0` contains only the origin.
  refine
    { default := ⟨⟨0, by simp [Metric.mem_closedBall]⟩⟩
      uniq := ?_ }
  intro x
  rcases x with ⟨x⟩
  rcases x with ⟨x, hx⟩
  have hx0 : x = 0 := Subsingleton.elim _ _
  subst hx0
  simp

/-- Helper for Lemma 22.2.2: the boundary of the `0`-disk identifies with the initial object of
`TopCat`. -/
def diskBoundaryZeroIsoInitial : TopCat.diskBoundary 0 ≅ ⊥_ TopCat := by
  -- The geometric boundary is empty, so we bridge it to the categorical initial object.
  letI : IsEmpty (TopCat.diskBoundary 0) := diskBoundaryZeroIsEmpty
  exact
    TopCat.isoOfHomeo (Homeomorph.empty (X := TopCat.diskBoundary 0) (Y := PEmpty)) ≪≫
      TopCat.initialIsoPEmpty.symm

/-- Helper for Lemma 22.2.2: the `0`-disk identifies with the one-point space. -/
def diskZeroIsoTerminal : TopCat.disk 0 ≅ onePointBasedSpace.right := by
  -- The geometric disk has one point, so it matches the underlying topological space of
  -- `onePointBasedSpace`.
  letI : Unique (TopCat.disk 0) := diskZeroUnique
  simpa [onePointBasedSpace] using
    (TopCat.isoOfHomeo (Homeomorph.homeomorphOfUnique (TopCat.disk 0) PUnit))

/-- Helper for Lemma 22.2.2: the one-point CW filtration starts from the empty space and then
stays constant at the one-point space. -/
def onePointStageObj : ℕ → TopCat.{u}
  | 0 => ⊥_ TopCat
  | _ + 1 => onePointBasedSpace.right

/-- Helper for Lemma 22.2.2: the first stage map is the initial map, and every later stage map is
the identity on the one-point space. -/
def onePointStageMap (n : ℕ) : onePointStageObj n ⟶ onePointStageObj (n + 1) :=
  match n with
  | 0 => initial.to _
  | _ + 1 => 𝟙 _

/-- Helper for Lemma 22.2.2: the staged diagram for the one-point CW structure. -/
def onePointStageFunctor : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence onePointStageMap

/-- Helper for Lemma 22.2.2: each successor map in the staged diagram is the prescribed stage
map. -/
theorem onePointStageFunctor_map_succ (n : ℕ) :
    onePointStageFunctor.map (homOfLE (Nat.le_add_right n 1)) = onePointStageMap n := by
  -- `Functor.ofSequence` computes the `n → n + 1` morphisms definitionally.
  simp [onePointStageFunctor]

/-- Helper for Lemma 22.2.2: every map inside the constant tail of the staged diagram is the
identity on the one-point space. -/
theorem onePointStageFunctor_map_fromOne (n : ℕ) :
    onePointStageFunctor.map (homOfLE (show 1 ≤ n + 1 by simp)) = 𝟙 onePointBasedSpace.right := by
  -- The tail is built entirely from identity successor maps, so every composite there is an
  -- identity as well.
  induction n with
  | zero =>
      simp [onePointStageFunctor, onePointStageObj, onePointBasedSpace]
  | succ n ih =>
      rw [← homOfLE_comp (show 1 ≤ n + 1 by simp) (show n + 1 ≤ n + 2 by simp)]
      rw [Functor.map_comp, ih]
      simpa [onePointStageFunctor_map_succ, onePointStageMap]

/-- Helper for Lemma 22.2.2: the evident stagewise maps from the one-point filtration to its
colimit candidate. -/
def onePointStageCoconeMap : ∀ n : ℕ, onePointStageObj n ⟶ onePointBasedSpace.right
  | 0 => initial.to _
  | _ + 1 => 𝟙 _

/-- Helper for Lemma 22.2.2: the stagewise cocone maps satisfy the successor compatibility needed
by `NatTrans.ofSequence`. -/
theorem onePointStageCoconeMap_naturality (n : ℕ) :
    onePointStageFunctor.map (homOfLE (Nat.le_add_right n 1)) ≫ onePointStageCoconeMap (n + 1) =
      onePointStageCoconeMap n ≫
        ((Functor.const ℕ).obj onePointBasedSpace.right).map
          (homOfLE (Nat.le_add_right n 1)) := by
  -- Normalize the successor map and then split into the initial stage and the constant tail.
  cases n with
  | zero =>
      rw [onePointStageFunctor_map_succ]
      simp only [onePointStageCoconeMap, onePointStageMap, onePointStageObj, Under.mk_right,
        Nat.reduceAdd, Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map,
        Category.comp_id]
      exact Category.comp_id _
  | succ n =>
      rw [onePointStageFunctor_map_succ]
      simp only [onePointStageCoconeMap, onePointStageMap, onePointStageObj, Under.mk_right,
        Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map, Category.comp_id]
      exact Category.id_comp _

/-- Helper for Lemma 22.2.2: the evident cocone from the staged diagram to the one-point space. -/
def onePointStageCocone : Cocone onePointStageFunctor :=
  Cocone.mk _ (NatTrans.ofSequence onePointStageCoconeMap onePointStageCoconeMap_naturality)

/-- Helper for Lemma 22.2.2: every cocone over the one-point stage diagram is determined by its
stage-`1` leg. -/
def onePointStageCoconeDesc (s : Cocone onePointStageFunctor) :
    onePointStageCocone.pt ⟶ s.pt :=
  s.ι.app 1

/-- Helper for Lemma 22.2.2: the stage-`1` leg induces the canonical factorization through the
one-point cocone. -/
theorem onePointStageCoconeFac (s : Cocone onePointStageFunctor) (j : ℕ) :
    onePointStageCocone.ι.app j ≫ onePointStageCoconeDesc s = s.ι.app j := by
  cases j with
  | zero =>
      -- The stage-`0` leg is forced by naturality along the initial successor map.
      have hs := s.ι.naturality (homOfLE (show 0 ≤ 1 by simp))
      simpa [onePointStageCocone, onePointStageCoconeDesc, onePointStageCoconeMap,
        onePointStageFunctor_map_succ, onePointStageMap] using hs
  | succ n =>
      -- Every later stage is identified with stage `1` through the constant tail.
      have hs := s.ι.naturality (homOfLE (show 1 ≤ n + 1 by simp))
      have htail : s.ι.app (n + 1) = s.ι.app 1 := by
        simpa [onePointStageFunctor_map_fromOne n] using hs
      simpa [onePointStageCocone, onePointStageCoconeDesc, onePointStageCoconeMap] using
        htail.symm

/-- Helper for Lemma 22.2.2: the stage-`1` factorization is the unique map out of the one-point
cocone. -/
theorem onePointStageCoconeUniq (s : Cocone onePointStageFunctor)
    (m : onePointStageCocone.pt ⟶ s.pt)
    (hm : ∀ j : ℕ, onePointStageCocone.ι.app j ≫ m = s.ι.app j) :
    m = onePointStageCoconeDesc s := by
  -- Stage `1` already sees the identity leg of the stabilized tail.
  simpa [onePointStageCocone, onePointStageCoconeDesc, onePointStageCoconeMap] using hm 1

/-- Helper for Lemma 22.2.2: the evident cocone from the staged diagram is a colimit cocone. -/
def onePointStageCoconeIsColimit : IsColimit onePointStageCocone :=
  { desc := onePointStageCoconeDesc
    fac := onePointStageCoconeFac
    uniq := onePointStageCoconeUniq }

/-- Helper for Lemma 22.2.2: the basic `0`-cell inclusion carries the canonical one-cell
attachment structure. -/
def basicCellZeroAttachCells :
    HomotopicalAlgebra.AttachCells.{u} (TopCat.RelativeCWComplex.basicCell 0)
      (TopCat.RelativeCWComplex.basicCell 0 ()) := by
  -- A single `0`-cell attachment is the tautological pushout square of the basic cell map.
  refine
    { ι := ULift Unit
      π := fun _ ↦ ()
      cofan₁ := Cofan.mk (TopCat.diskBoundary 0) (fun _ : ULift Unit ↦ 𝟙 _)
      cofan₂ := Cofan.mk (TopCat.disk 0) (fun _ : ULift Unit ↦ 𝟙 _)
      isColimit₁ := unitCofanIsColimit _
      isColimit₂ := unitCofanIsColimit _
      m := TopCat.RelativeCWComplex.basicCell 0 ()
      g₁ := 𝟙 _
      g₂ := 𝟙 _
      isPushout := by
        simpa using (IsPushout.of_id_fst (f := TopCat.RelativeCWComplex.basicCell 0 ())) }

/-- Helper for Lemma 22.2.2: the `0`-cell inclusion becomes the actual stage-`0` map after
identifying the source with `⊥_ TopCat` and the target with the one-point space. -/
theorem basicCellZeroStageMap_comm :
    diskBoundaryZeroIsoInitial.hom ≫ onePointStageMap 0 =
      TopCat.RelativeCWComplex.basicCell 0 () ≫ diskZeroIsoTerminal.hom := by
  -- Both sides are maps out of the empty boundary of the `0`-disk, so pointwise equality is
  -- vacuous.
  ext x
  exact (diskBoundaryZeroIsEmpty.false x).elim

/-- Helper for Lemma 22.2.2: the stage-`0` map is isomorphic to the basic `0`-cell inclusion. -/
def basicCellZeroStageMapArrowIso :
    Arrow.mk (TopCat.RelativeCWComplex.basicCell 0 ()) ≅ Arrow.mk (onePointStageMap 0) :=
  Arrow.isoMk diskBoundaryZeroIsoInitial diskZeroIsoTerminal basicCellZeroStageMap_comm

/-- Helper for Lemma 22.2.2: the canonical `0`-cell attachment transports to the actual stage-`0`
map of the one-point filtration. -/
def basicCellZeroAttachCellsOnStageZero :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell 0) (onePointStageMap 0) :=
  HomotopicalAlgebra.AttachCells.ofArrowIso
    basicCellZeroAttachCells
    basicCellZeroStageMapArrowIso

/-- Helper for Lemma 22.2.2: the empty attachment square is the identity pushout over the initial
object. -/
theorem emptyBasicCellAttachCells_isPushout (X : TopCat.{u}) :
    IsPushout (initial.to X) (𝟙 (⊥_ TopCat.{u})) (𝟙 X) (initial.to X) := by
  -- Attaching no cells leaves the ambient object unchanged.
  simpa using (IsPushout.of_id_snd (f := initial.to X))

/-- Helper for Lemma 22.2.2: attaching no `n`-cells gives the identity morphism. -/
def emptyBasicCellAttachCells (n : ℕ) (X : TopCat.{u}) :
    HomotopicalAlgebra.AttachCells.{u} (TopCat.RelativeCWComplex.basicCell n) (𝟙 X) :=
  { ι := ULift.{u} PEmpty
    π := fun i ↦ PEmpty.elim i.down
    cofan₁ := Cofan.mk (f := fun _ : ULift.{u} PEmpty ↦ TopCat.diskBoundary n) (⊥_ TopCat.{u})
      (fun i ↦ PEmpty.elim i.down)
    cofan₂ := Cofan.mk (f := fun _ : ULift.{u} PEmpty ↦ TopCat.disk n) (⊥_ TopCat.{u})
      (fun i ↦ PEmpty.elim i.down)
    isColimit₁ := emptyCofanIsColimit (fun _ : ULift.{u} PEmpty ↦ TopCat.diskBoundary n)
    isColimit₂ := emptyCofanIsColimit (fun _ : ULift.{u} PEmpty ↦ TopCat.disk n)
    m := 𝟙 (⊥_ TopCat.{u})
    hm := fun i ↦ PEmpty.elim i.down
    g₁ := initial.to X
    g₂ := initial.to X
    isPushout := emptyBasicCellAttachCells_isPushout X }

/-- Lemma 22.2.2: theorem `onePointTopCatCWComplex` gives the one-point space an abstract
`TopCat.CWComplex` structure with one `0`-cell and no higher cells. -/
theorem onePointTopCatCWComplex : Nonempty (TopCat.CWComplex onePointBasedSpace.right) := by
  -- Route correction: stay in the abstract sequential CW API, since the classical one-point
  -- witness does not directly transport to `TopCat.CWComplex`.
  refine
    ⟨{ F := onePointStageFunctor
       isoBot := Iso.refl _
       incl := onePointStageCocone.ι
       isColimit := onePointStageCoconeIsColimit
       attachCells := ?_ }⟩
  intro j hj
  cases j with
  | zero =>
      -- The first step adds the unique `0`-cell.
      simpa [onePointStageFunctor_map_succ] using basicCellZeroAttachCellsOnStageZero
  | succ n =>
      -- Every later step is the identity, i.e. attaching no higher-dimensional cells.
      simpa [onePointStageFunctor_map_succ, onePointStageMap] using
        (emptyBasicCellAttachCells (n + 1) onePointBasedSpace.right)

/-- The one-point based space is a based CW complex. -/
theorem onePointBasedSpace_isBasedCWComplex :
    IsBasedCWComplex onePointBasedSpace := by
  -- The abstract one-point CW witness constructed above gives the required based CW structure.
  exact onePointTopCatCWComplex

/-- The one-point based CW complex used for cofibration exactness statements. -/
abbrev onePointBasedCWComplex : BasedCWComplex :=
  ⟨onePointBasedSpace, onePointBasedSpace_isBasedCWComplex⟩

/-- The canonical collapse of a based CW complex to the one-point based CW complex. -/
abbrev collapseToOnePointOnBasedCWComplex (X : BasedCWComplex) :
    X ⟶ onePointBasedCWComplex :=
  CategoryTheory.ObjectProperty.homMk (collapseToOnePoint X.1)

/-- The canonical based map from the one-point based CW complex to a based CW complex. -/
abbrev onePointBasedCWComplexTo (X : BasedCWComplex) :
    onePointBasedCWComplex ⟶ X :=
  CategoryTheory.ObjectProperty.homMk (constantBasedMap onePointBasedSpace X.1)

/-- The coproduct of a family of based CW complexes, bundled once its ambient coproduct is known
to be a based CW complex. -/
abbrev basedCWComplexCoproduct (X : ι → BasedCWComplex)
    [HasCoproduct fun i ↦ (X i).1] (hX : IsBasedCWComplex (∐ fun i ↦ (X i).1)) :
    BasedCWComplex :=
  ⟨∐ fun i ↦ (X i).1, hX⟩

/-- The `i`th coproduct leg as a morphism of based CW complexes. -/
abbrev basedCWComplexCoproductι (X : ι → BasedCWComplex)
    [HasCoproduct fun i ↦ (X i).1] (hX : IsBasedCWComplex (∐ fun i ↦ (X i).1)) (i : ι) :
    X i ⟶ basedCWComplexCoproduct X hX :=
  CategoryTheory.ObjectProperty.homMk (Sigma.ι (fun i ↦ (X i).obj) i)

/-- Helper for Lemma 22.2.2: the path space of a based space becomes a based space by choosing the
constant basepoint path. -/
abbrev basedPathSpace (Z : BasedSpace) : BasedSpace :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (ContinuousMap.const I (underTopBasepoint Z))))

/-- Helper for Lemma 22.2.2: the chosen basepoint of `basedPathSpace Z` is the constant path at
the basepoint of `Z`. -/
@[simp] theorem underTopBasepoint_basedPathSpace (Z : BasedSpace) :
    underTopBasepoint (basedPathSpace Z) = ContinuousMap.const I (underTopBasepoint Z) :=
  rfl

/-- Helper for Lemma 22.2.2: evaluating a based path preserves the chosen basepoints. -/
theorem basedPathSpaceEvalAt_w (Z : BasedSpace) (t : I) :
    (basedPathSpace Z).hom ≫ TopCat.ofHom (pathSpaceEvalAt t Z.right) = Z.hom := by
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  have hx' : x = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x) := by
    exact (congrArg (fun f ↦ f x) TopCat.terminalIsoPUnit.hom_inv_id).symm
  have hu : x = TopCat.terminalIsoPUnit.inv PUnit.unit := by
    calc
      x = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x) := hx'
      _ = TopCat.terminalIsoPUnit.inv PUnit.unit := by rw [hx]
  -- Evaluate the terminal-domain maps at the unique point.
  calc
    ((basedPathSpace Z).hom ≫ TopCat.ofHom (pathSpaceEvalAt t Z.right)) x
        = ((basedPathSpace Z).hom ≫ TopCat.ofHom (pathSpaceEvalAt t Z.right))
            (TopCat.terminalIsoPUnit.inv PUnit.unit) := by rw [hu]
    _ = underTopBasepoint Z := rfl
    _ = Z.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = Z.hom x := by rw [hu]

/-- Helper for Lemma 22.2.2: evaluation at a fixed time is a based map out of the based path
space. -/
def basedPathSpaceEvalAt (Z : BasedSpace) (t : I) : basedPathSpace Z ⟶ Z :=
  Under.homMk
    (TopCat.ofHom (pathSpaceEvalAt t Z.right))
    (basedPathSpaceEvalAt_w Z t)

/-- Helper for Lemma 22.2.2: a based homotopy determines a based map into the based path space. -/
theorem basedPathSpaceMapOfHomotopy_w
    {A Z : BasedSpace} {f g : A ⟶ Z}
    (H : f.right.hom HRel[A] g.right.hom) :
    A.hom ≫ TopCat.ofHom H.toHomotopy.toPathSpaceMap = (basedPathSpace Z).hom := by
  ext x t
  change (A.hom ≫ TopCat.ofHom H.toHomotopy.toPathSpaceMap) x t =
    (basedPathSpaceEvalAt Z t).right.hom ((basedPathSpace Z).hom x)
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  have hx' : x = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x) := by
    exact (congrArg (fun k ↦ k x) TopCat.terminalIsoPUnit.hom_inv_id).symm
  have hu : x = TopCat.terminalIsoPUnit.inv PUnit.unit := by
    calc
      x = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x) := hx'
      _ = TopCat.terminalIsoPUnit.inv PUnit.unit := by rw [hx]
  have hfbase : f.right.hom (underTopBasepoint A) = underTopBasepoint Z := by
    have hw :=
      congrArg
        (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
        (Under.w f)
    simpa [underTopBasepoint] using hw
  -- The relative condition makes the chosen basepoint trace the constant basepoint path.
  calc
    (A.hom ≫ TopCat.ofHom H.toHomotopy.toPathSpaceMap) x t
        = (A.hom ≫ TopCat.ofHom H.toHomotopy.toPathSpaceMap)
            (TopCat.terminalIsoPUnit.inv PUnit.unit) t := by rw [hu]
    _ = underTopBasepoint Z := by
      have hrel := H.prop' t (underTopBasepoint A) (by simp [basedBasepointSet])
      calc
        H.toHomotopy.toPathSpaceMap (underTopBasepoint A) t
            = H.toHomotopy (t, underTopBasepoint A) := by
          rfl
        _ = f.right.hom (underTopBasepoint A) := by simpa using hrel
        _ = underTopBasepoint Z := hfbase
    _ = (basedPathSpaceEvalAt Z t).right.hom
          ((basedPathSpace Z).hom (TopCat.terminalIsoPUnit.inv PUnit.unit)) := by
            rfl
    _ = (basedPathSpaceEvalAt Z t).right.hom ((basedPathSpace Z).hom x) := by rw [hu]

/-- Helper for Lemma 22.2.2: package a based homotopy as a based map into the based path space. -/
def basedPathSpaceMapOfHomotopy
    {A Z : BasedSpace} {f g : A ⟶ Z}
    (H : f.right.hom HRel[A] g.right.hom) :
    A ⟶ basedPathSpace Z :=
  Under.homMk
    (TopCat.ofHom H.toHomotopy.toPathSpaceMap)
    (basedPathSpaceMapOfHomotopy_w H)

/-- Helper for Lemma 22.2.2: evaluating the path-space map of a based homotopy at `0` recovers
its initial map. -/
theorem basedPathSpaceMapOfHomotopy_evalAt_zero
    {A Z : BasedSpace} {f g : A ⟶ Z}
    (H : f.right.hom HRel[A] g.right.hom) :
    basedPathSpaceMapOfHomotopy H ≫ basedPathSpaceEvalAt Z 0 = f := by
  -- Evaluate the stored path family at time `0` and simplify to the initial endpoint.
  ext a
  simp [basedPathSpaceMapOfHomotopy, basedPathSpaceEvalAt, Under.comp_right, pathSpaceEvalAt]

/-- Helper for Lemma 22.2.2: evaluating the path-space map of a based homotopy at `1` recovers
its terminal map. -/
theorem basedPathSpaceMapOfHomotopy_evalAt_one
    {A Z : BasedSpace} {f g : A ⟶ Z}
    (H : f.right.hom HRel[A] g.right.hom) :
    basedPathSpaceMapOfHomotopy H ≫ basedPathSpaceEvalAt Z 1 = g := by
  -- Evaluate the stored path family at time `1` and simplify to the terminal endpoint.
  ext a
  simp [basedPathSpaceMapOfHomotopy, basedPathSpaceEvalAt, Under.comp_right, pathSpaceEvalAt]

namespace BasedCWComplexHomotopyClasses

/-- The pointed set of based homotopy classes `[(X : BasedSpace), Z]` for a based CW complex `X`. -/
abbrev obj (X : BasedCWComplex) (Z : BasedSpace) : Pointed :=
  Ho*[X.1, Z]

/-- A morphism of based CW complexes induces a pointed map on based homotopy classes by
precomposition. -/
abbrev map
    (Z : BasedSpace) {X Y : BasedCWComplex} (f : X ⟶ Y) :
    obj Y Z ⟶ obj X Z :=
  BasedHomotopyClasses.precompose f.hom

/-- The product pointed set of the family `i ↦ [X i, Z]` on based CW complexes. -/
def product
    (Z : BasedSpace) (X : ι → BasedCWComplex) : Pointed :=
  Pointed.of (fun i ↦ (obj (X i) Z).point)

/-- The wedge-to-product comparison sends a class on a based-CW wedge to its restrictions to the
summands. -/
def wedgeToProductFun
    (Z : BasedSpace) (X : ι → BasedCWComplex)
    [HasCoproduct fun i ↦ (X i).1] (hX : IsBasedCWComplex (∐ fun i ↦ (X i).1)) :
    obj (basedCWComplexCoproduct X hX) Z → ∀ i, obj (X i) Z :=
  fun h i ↦ map Z (basedCWComplexCoproductι X hX i) h

/-- The wedge-to-product comparison preserves the distinguished point. -/
theorem wedgeToProductFun_point
    (Z : BasedSpace) (X : ι → BasedCWComplex)
    [HasCoproduct fun i ↦ (X i).1] (hX : IsBasedCWComplex (∐ fun i ↦ (X i).1)) :
    wedgeToProductFun Z X hX (obj (basedCWComplexCoproduct X hX) Z).point =
      (product Z X).point := by
  -- Evaluate the distinguished point componentwise and use point preservation of precomposition.
  funext i
  simpa [wedgeToProductFun, map, BasedHomotopyClasses.precompose] using
    BasedHomotopyClasses.precomposeFun_point (basedCWComplexCoproductι X hX i).hom

/-- The pointed comparison map from homotopy classes on a based-CW wedge to the product of the
homotopy classes on the summands. -/
def wedgeToProduct
    (Z : BasedSpace) (X : ι → BasedCWComplex)
    [HasCoproduct fun i ↦ (X i).1] (hX : IsBasedCWComplex (∐ fun i ↦ (X i).1)) :
    obj (basedCWComplexCoproduct X hX) Z ⟶ product Z X where
  toFun := wedgeToProductFun Z X hX
  map_point := wedgeToProductFun_point Z X hX

/-- First clause of Lemma 22.2.2. For any based space `Z`, the functor `X ↦ [X, Z]` on based CW
complexes is homotopy invariant: based-homotopic maps induce the same map on based homotopy
classes. -/
theorem map_eq_of_basedHomotopy
    (Z : BasedSpace) {X Y : BasedCWComplex} {f g : X ⟶ Y}
    (hfg : basedHomotopyRel f.hom g.hom) :
    map Z f = map Z g := by
  -- The ambient Chapter 22 functor already identifies based-homotopic maps.
  simpa [map, onBasedCWComplexes] using
    BasedHomotopyClasses.map_eq_of_basedHomotopy Z hfg

/-- Helper for Lemma 22.2.2: equality in `Ho*[X, Z]` can be represented by an actual based
homotopy between representatives because `basedHomotopyRel` is already an equivalence relation. -/
theorem basedHomotopyRel_of_eq
    {X Z : BasedSpace} {f g : X ⟶ Z}
    (hfg :
      (Quotient.mk (basedHomotopySetoid X Z) f : Ho*[X, Z]) =
        Quotient.mk (basedHomotopySetoid X Z) g) :
    basedHomotopyRel f g := by
  -- Reduce quotient equality to the underlying relation and collapse the `EqvGen` closure.
  have hsetoid : (basedHomotopySetoid X Z).r f g := Quotient.exact hfg
  rw [basedHomotopySetoid_iff] at hsetoid
  have hEquiv : Equivalence (fun a b : X ⟶ Z ↦ basedHomotopyRel a b) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨ContinuousMap.HomotopyRel.refl a.right.hom (basedBasepointSet X)⟩
    · intro a b hab
      exact hab.elim fun H ↦ ⟨H.symm⟩
    · intro a b c hab hbc
      exact hab.elim fun Hab ↦ hbc.elim fun Hbc ↦ ⟨Hab.trans Hbc⟩
  exact (Equivalence.eqvGen_iff hEquiv).1 hsetoid

/-- Helper for Lemma 22.2.2: any based map out of `onePointBasedSpace` is uniquely determined by
the basepoint condition. -/
theorem onePointToSubsingleton (Z : BasedSpace) :
    Subsingleton (onePointBasedSpace ⟶ Z) := by
  constructor
  intro f g
  -- The domain has one point, and both maps send it to the distinguished basepoint of `Z`.
  ext x
  cases x
  have hfbase : underTopBasepoint Z = f.right.hom PUnit.unit := by
    have hwf := congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      (congrArg ConcreteCategory.hom f.w)
    simpa [onePointBasedSpace] using hwf
  have hgbase : underTopBasepoint Z = g.right.hom PUnit.unit := by
    have hwg := congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      (congrArg ConcreteCategory.hom g.w)
    simpa [onePointBasedSpace] using hwg
  calc
    f.right.hom PUnit.unit = underTopBasepoint Z := hfbase.symm
    _ = g.right.hom PUnit.unit := hgbase

/-- Helper for Lemma 22.2.2: any homotopy class on `Y` restricts trivially along the cofibration
leg after precomposing with the quotient map. -/
theorem map_comp_eq_point
    (Z : BasedSpace) {A X Y : BasedCWComplex}
    (i : A ⟶ X) (q : X ⟶ Y)
    (hpushout :
      IsPushout i.hom (collapseToOnePoint A.1) q.hom (onePointBasedCWComplexTo Y).hom)
    (a : obj Y Z) :
    map Z i (map Z q a) = (obj A Z).point := by
  -- The pushout square identifies `i ≫ q` with the collapse-to-point composite.
  have hcomp :
      i.hom ≫ q.hom =
        collapseToOnePoint A.1 ≫ constantBasedMap onePointBasedSpace Y.1 := by
    simpa using hpushout.w
  have hpre :
      BasedHomotopyClasses.precomposeFun i.hom
        (BasedHomotopyClasses.precomposeFun q.hom a) =
      BasedHomotopyClasses.precomposeFun (i.hom ≫ q.hom) a := by
    simpa using congrArg (fun f ↦ f a) (BasedHomotopyClasses.precompose_comp i.hom q.hom).symm
  -- Rewrite the composite precomposition along the commutative square.
  change BasedHomotopyClasses.precomposeFun i.hom
      (BasedHomotopyClasses.precomposeFun q.hom a) = _
  rw [hpre, hcomp]
  have hpre' :
      BasedHomotopyClasses.precomposeFun (collapseToOnePoint A.1)
        (BasedHomotopyClasses.precomposeFun (constantBasedMap onePointBasedSpace Y.1) a) =
      BasedHomotopyClasses.precomposeFun
        (collapseToOnePoint A.1 ≫ constantBasedMap onePointBasedSpace Y.1) a := by
    simpa using congrArg (fun f ↦ f a)
      (BasedHomotopyClasses.precompose_comp (collapseToOnePoint A.1)
        (constantBasedMap onePointBasedSpace Y.1)).symm
  rw [← hpre']
  have hsub : Subsingleton (Ho*[onePointBasedSpace, Z]) := by
    change Subsingleton (Quotient (basedHomotopySetoid onePointBasedSpace Z))
    let _ : Subsingleton (onePointBasedSpace ⟶ Z) := onePointToSubsingleton Z
    infer_instance
  have hone :
      BasedHomotopyClasses.precomposeFun (constantBasedMap onePointBasedSpace Y.1) a =
        (Ho*[onePointBasedSpace, Z]).point :=
    Subsingleton.elim _ _
  rw [hone]
  exact BasedHomotopyClasses.precomposeFun_point (collapseToOnePoint A.1)

/-- Helper for Lemma 22.2.2: the wedge comparison on based homotopy classes is surjective. -/
theorem wedgeToProduct_surjective
    (Z : BasedSpace) (X : ι → BasedCWComplex)
    [HasCoproduct fun i ↦ (X i).1] (hX : IsBasedCWComplex (∐ fun i ↦ (X i).1)) :
    Function.Surjective (wedgeToProduct Z X hX) := by
  classical
  intro u
  -- Choose representatives of the component classes and descend them through the coproduct.
  choose f hf using fun i : ι ↦ Quotient.exists_rep (u i)
  refine ⟨Quotient.mk _ (Sigma.desc f), ?_⟩
  funext i
  change Quotient.map (fun g : (basedCWComplexCoproduct X hX).1 ⟶ Z ↦
      (basedCWComplexCoproductι X hX i).hom ≫ g)
      (fun a b h ↦ BasedHomotopyClasses.precomposeWellDefined
        (basedCWComplexCoproductι X hX i).hom h)
      (Quotient.mk (basedHomotopySetoid (basedCWComplexCoproduct X hX).1 Z) (Sigma.desc f)) = u i
  rw [Quotient.map_mk, ← hf i]
  congr
  simpa using Sigma.ι_desc f i

/-- Helper for Lemma 22.2.2: a class on `X` whose restriction to `A` is nullhomotopic descends
across the cofiber pushout once the ambient based-cofibration and ambient pushout interfaces are
available. -/
theorem exists_desc_of_nullRestriction
    (Z : BasedSpace) {A X Y : BasedCWComplex}
    (i : A ⟶ X) (q : X ⟶ Y)
    (hi : IsBasedCofibration i.hom)
    (hpushout :
      IsPushout i.hom (collapseToOnePoint A.1) q.hom (onePointBasedCWComplexTo Y).hom)
    {f : X.1 ⟶ Z}
    (hnull :
      (Quotient.mk (basedHomotopySetoid A.1 Z) (i.hom ≫ f) : Ho*[A.1, Z]) =
        (Ho*[A.1, Z]).point) :
    ∃ g : Y.1 ⟶ Z, basedHomotopyRel (q.hom ≫ g) f := by
  -- Turn the null restriction into a concrete based homotopy on `A`.
  have hnullRel : basedHomotopyRel (i.hom ≫ f) (constantBasedMap A.1 Z) := by
    apply basedHomotopyRel_of_eq
    simpa [basedHomotopyClasses_point_eq] using hnull
  obtain ⟨Hnull⟩ := hnullRel
  -- Extend that nullhomotopy across the cofibration so the endpoint is literally constant on `A`.
  obtain ⟨G, F, hF⟩ := hi.exists_homotopy_extension f (constantBasedMap A.1 Z) Hnull
  let iMap : A.1 ⟶ X.1 := i.hom
  let collapseMap : A.1 ⟶ onePointBasedSpace := collapseToOnePoint A.1
  let constMap : onePointBasedSpace ⟶ Z := constantBasedMap onePointBasedSpace Z
  let iFun := iMap.right.hom
  have hcollapse :
      i.hom ≫ G =
        collapseToOnePoint A.1 ≫ constantBasedMap onePointBasedSpace Z := by
    -- Evaluating the extension at time `1` makes the restriction visibly constant.
    ext a
    calc
      (i.hom ≫ G).right.hom a = G.right.hom (iFun a) := rfl
      _ = F (1, iFun a) := by
        exact (F.map_one_left (iFun a)).symm
      _ = Hnull (1, a) := hF (1, a)
      _ = (constantBasedMap A.1 Z).right.hom a := by
        exact Hnull.map_one_left a
      _ = (collapseMap ≫ constMap).right.hom a := by
        rfl
  -- Descend the strict endpoint map across the ambient pushout square.
  let g : Y.1 ⟶ Z :=
    hpushout.desc G (constantBasedMap onePointBasedSpace Z) hcollapse
  have hqg : q.hom ≫ g = G := by
    dsimp [g]
    exact hpushout.inl_desc G (constantBasedMap onePointBasedSpace Z) hcollapse
  have hqg_hom : (q.hom ≫ g).right.hom = G.right.hom := by
    exact congrArg (fun k ↦ k.right.hom) hqg
  refine ⟨g, ?_⟩
  -- The descended representative is endpoint-homotopic to the original map `f`.
  exact ⟨(F.cast rfl hqg_hom.symm).symm⟩

/-- Helper for Lemma 22.2.2: a based homotopy on each summand of a based-CW wedge glues to a
based homotopy on the coproduct. -/
theorem basedHomotopyRel_of_componentwiseOnCoproduct
    (Z : BasedSpace) (X : ι → BasedCWComplex)
    [HasCoproduct fun i ↦ (X i).1] (hX : IsBasedCWComplex (∐ fun i ↦ (X i).1))
    {f g : (basedCWComplexCoproduct X hX).1 ⟶ Z}
    (hfg : ∀ i,
      basedHomotopyRel ((basedCWComplexCoproductι X hX i).hom ≫ f)
        ((basedCWComplexCoproductι X hX i).hom ≫ g)) :
    basedHomotopyRel f g := by
  classical
  let H :
      ∀ i,
        ((basedCWComplexCoproductι X hX i).hom ≫ f).right.hom HRel[(X i).1]
          ((basedCWComplexCoproductι X hX i).hom ≫ g).right.hom :=
    fun i ↦ (hfg i).some
  let dMap : ∀ i, (X i).1 ⟶ basedPathSpace Z :=
    fun i ↦ basedPathSpaceMapOfHomotopy (H i)
  let D : (basedCWComplexCoproduct X hX).1 ⟶ basedPathSpace Z :=
    Sigma.desc dMap
  have hD₀Map : D ≫ basedPathSpaceEvalAt Z 0 = f := by
    -- Compare both maps after restricting to every coproduct summand.
    apply Sigma.hom_ext
    intro i
    calc
      (basedCWComplexCoproductι X hX i).hom ≫ D ≫ basedPathSpaceEvalAt Z 0
          = dMap i ≫ basedPathSpaceEvalAt Z 0 := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ basedPathSpaceEvalAt Z 0) (Sigma.ι_desc dMap i)
      _ = (basedCWComplexCoproductι X hX i).hom ≫ f := by
            simpa [dMap, H] using basedPathSpaceMapOfHomotopy_evalAt_zero (H i)
  have hD₁Map : D ≫ basedPathSpaceEvalAt Z 1 = g := by
    -- The same descent argument identifies the terminal endpoint with `g`.
    apply Sigma.hom_ext
    intro i
    calc
      (basedCWComplexCoproductι X hX i).hom ≫ D ≫ basedPathSpaceEvalAt Z 1
          = dMap i ≫ basedPathSpaceEvalAt Z 1 := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ basedPathSpaceEvalAt Z 1) (Sigma.ι_desc dMap i)
      _ = (basedCWComplexCoproductι X hX i).hom ≫ g := by
            simpa [dMap, H] using basedPathSpaceMapOfHomotopy_evalAt_one (H i)
  have hD₀Right :
      (basedPathSpaceEvalAt Z 0).right.hom.comp D.right.hom = f.right.hom := by
    simpa [Under.comp_right] using congrArg (fun k ↦ k.right.hom) hD₀Map
  have hD₁Right :
      (basedPathSpaceEvalAt Z 1).right.hom.comp D.right.hom = g.right.hom := by
    simpa [Under.comp_right] using congrArg (fun k ↦ k.right.hom) hD₁Map
  have hD₀Eval :
      ∀ a : (basedCWComplexCoproduct X hX).1.right,
        (basedPathSpaceEvalAt Z 0).right.hom (D.right.hom a) = f.right.hom a := by
    intro a
    simpa [basedPathSpaceEvalAt, pathSpaceEvalAtZero, pathSpaceEvalAt] using
      ContinuousMap.congr_fun hD₀Right a
  have hD₁Eval :
      ∀ a : (basedCWComplexCoproduct X hX).1.right,
        (basedPathSpaceEvalAt Z 1).right.hom (D.right.hom a) = g.right.hom a := by
    intro a
    simpa [basedPathSpaceEvalAt, pathSpaceEvalAt] using
      ContinuousMap.congr_fun hD₁Right a
  have hDrel :
      ∀ a : (basedCWComplexCoproduct X hX).1.right,
        a ∈ basedBasepointSet (basedCWComplexCoproduct X hX).1 →
          D.right.hom a = ContinuousMap.const I (f.right.hom a) := by
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    have hDb :
        D.right.hom (underTopBasepoint (basedCWComplexCoproduct X hX).1) =
          underTopBasepoint (basedPathSpace Z) := by
      have hw :=
        congrArg
          (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
          (Under.w D)
      simpa [underTopBasepoint] using hw
    have hfb :
        f.right.hom (underTopBasepoint (basedCWComplexCoproduct X hX).1) =
          underTopBasepoint Z := by
      have hw :=
        congrArg
          (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
          (Under.w f)
      simpa [underTopBasepoint] using hw
    apply ContinuousMap.ext
    intro t
    change (basedPathSpaceEvalAt Z t).right.hom
        (D.right.hom (underTopBasepoint (basedCWComplexCoproduct X hX).1)) =
      (ContinuousMap.const I (f.right.hom (underTopBasepoint (basedCWComplexCoproduct X hX).1))) t
    simpa [basedPathSpaceEvalAt, pathSpaceEvalAt, underTopBasepoint_basedPathSpace, hfb] using
      congrArg (fun γ ↦ (basedPathSpaceEvalAt Z t).right.hom γ) hDb
  -- Route correction: descend branchwise path families through the wedge coproduct, then rebuild
  -- the global based homotopy from the descended path family.
  exact ⟨basedHomotopyRelOfPathFamily D.right.hom
    (fun a ↦ by
      simpa [basedPathSpaceEvalAt, pathSpaceEvalAtZero, pathSpaceEvalAt] using hD₀Eval a)
    (fun a ↦ by
      simpa [basedPathSpaceEvalAt, pathSpaceEvalAt] using hD₁Eval a)
    hDrel⟩

/-- Helper for Lemma 22.2.2: the wedge-to-product comparison is injective on based homotopy
classes. -/
theorem wedgeToProduct_injective
    (Z : BasedSpace) (X : ι → BasedCWComplex)
    [HasCoproduct fun i ↦ (X i).1] (hX : IsBasedCWComplex (∐ fun i ↦ (X i).1)) :
    Function.Injective (wedgeToProduct Z X hX) := by
  intro a b hab
  refine Quotient.inductionOn₂ a b ?_ hab
  intro f g hfg
  have hcomp :
      ∀ i,
        basedHomotopyRel ((basedCWComplexCoproductι X hX i).hom ≫ f)
          ((basedCWComplexCoproductι X hX i).hom ≫ g) := by
    intro i
    -- Equality of product components is equality of the represented branch classes.
    apply basedHomotopyRel_of_eq
    simpa [wedgeToProduct, wedgeToProductFun, map, BasedHomotopyClasses.precompose,
      BasedHomotopyClasses.precomposeFun] using congrFun hfg i
  have hfgRel : basedHomotopyRel f g :=
    basedHomotopyRel_of_componentwiseOnCoproduct Z X hX hcomp
  -- Return from representative-level homotopy to equality in the quotient of based homotopy
  -- classes.
  apply Quotient.sound
  change (basedHomotopySetoid (basedCWComplexCoproduct X hX).1 Z).r f g
  rw [basedHomotopySetoid_iff]
  exact Relation.EqvGen.rel _ _ hfgRel

/-- Second clause of Lemma 22.2.2. For any based space `Z`, the functor `X ↦ [X, Z]` sends a
cofibration sequence of based CW complexes to an exact sequence of pointed sets. Here the
cofiber sequence is expressed in `BasedSpace` by a based cofibration `i` together with a
pushout square collapsing `A` to the one-point based CW complex, with quotient map `q : X ⟶ Y`.
-/
theorem cofibrationExact
    (Z : BasedSpace) {A X Y : BasedCWComplex}
    (i : A ⟶ X) (q : X ⟶ Y)
    (hi : IsBasedCofibration i.hom)
    (hpushout :
      IsPushout i.hom (collapseToOnePoint A.1) q.hom (onePointBasedCWComplexTo Y).hom) :
    PointedExact
      (map Z q)
      (map Z i) := by
  intro b
  constructor
  · refine Quotient.inductionOn b ?_
    intro f hf
    -- A null restriction on a representative descends across the cofiber pushout.
    rcases exists_desc_of_nullRestriction Z i q hi hpushout
        (f := f)
        (by
          simpa [map, BasedHomotopyClasses.precompose, BasedHomotopyClasses.precomposeFun] using
            hf) with ⟨g, hg⟩
    refine ⟨Quotient.mk _ g, ?_⟩
    have hsetoid : (basedHomotopySetoid X.1 Z).r (q.hom ≫ g) f := by
      rw [basedHomotopySetoid_iff]
      exact Relation.EqvGen.rel _ _ hg
    simpa [map, BasedHomotopyClasses.precompose, BasedHomotopyClasses.precomposeFun] using
      (Quotient.sound hsetoid :
        (Quotient.mk (basedHomotopySetoid X.1 Z) (q.hom ≫ g) : Ho*[X.1, Z]) =
          Quotient.mk (basedHomotopySetoid X.1 Z) f)
  · rintro ⟨a, rfl⟩
    -- Every class coming from `Y` restricts trivially along the cofibration leg.
    exact map_comp_eq_point Z i q hpushout a

/-- Elementwise form of Lemma 22.2.2 (2): exactness at `[X, Z]` means that a class restricts to
the basepoint on `A` exactly when it comes from a class on `Y`. -/
theorem cofibrationExact_iff
    (Z : BasedSpace) {A X Y : BasedCWComplex}
    (i : A ⟶ X) (q : X ⟶ Y)
    (hi : IsBasedCofibration i.hom)
    (hpushout :
      IsPushout i.hom (collapseToOnePoint A.1) q.hom (onePointBasedCWComplexTo Y).hom)
    (b : obj X Z) :
    map Z i b = (obj A Z).point ↔
      ∃ a : obj Y Z, map Z q a = b := by
  simpa [PointedExact] using
    (cofibrationExact Z i q hi hpushout) b

/-- Third clause of Lemma 22.2.2. For any based space `Z`, the functor `X ↦ [X, Z]` sends wedges
of based CW complexes to products of pointed sets: the restriction map from `[∐ X, Z]` to the
product of the `[X i, Z]` is bijective. -/
theorem wedgeToProduct_bijective
    (Z : BasedSpace) (X : ι → BasedCWComplex)
    [HasCoproduct fun i ↦ (X i).1] (hX : IsBasedCWComplex (∐ fun i ↦ (X i).1)) :
    Function.Bijective (wedgeToProduct Z X hX) := by
  constructor
  · -- Injectivity is the representative-level gluing argument through the descended path family.
    exact wedgeToProduct_injective Z X hX
  · -- Surjectivity comes from descending chosen representatives through `Sigma.desc`.
    exact wedgeToProduct_surjective Z X hX

end BasedCWComplexHomotopyClasses
