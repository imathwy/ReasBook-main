import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_6_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CWApproximation
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_5_1.StageAPI

open CategoryTheory Limits
open scoped TopCat Topology

noncomputable section

universe u

/-- Helper for Theorem 10.5.1: theorem-local stagewise approximation data packages a sequential
diagram of spaces, its abstract cell-attachment data, and a compatible cocone to the target. -/
structure StagewiseApproximationData (X : TopCat.{u}) where
  /-- The staged diagram `F₀ ⟶ F₁ ⟶ F₂ ⟶ ⋯` used to approximate `X`. -/
  F : ℕ ⥤ TopCat.{u}
  /-- The stage-zero object is initial, so the staged diagram starts from the empty CW stage. -/
  isoBot : F.obj 0 ≅ ⊥_ TopCat.{u}
  /-- Each successor map is an abstract `n`-cell attachment. -/
  attachCells :
    ∀ n : ℕ,
      HomotopicalAlgebra.AttachCells.{u}
        (TopCat.RelativeCWComplex.basicCell n)
        (F.map (homOfLE (Nat.le_add_right n 1)))
  /-- The staged maps to `X` that will descend to the final comparison map. -/
  stageToTarget : ∀ n : ℕ, F.obj n ⟶ X
  /-- The staged maps form a cocone over the sequential diagram. -/
  stageToTarget_naturality :
    ∀ n : ℕ,
      F.map (homOfLE (Nat.le_add_right n 1)) ≫ stageToTarget (n + 1) =
        stageToTarget n ≫
          ((Functor.const ℕ).obj X).map (homOfLE (Nat.le_add_right n 1))
  /-- The descended colimit map already has the required `0`-equivalence input. -/
  zeroEquivalence :
    IsNEquivalence 0
      ((Limits.colimit.desc F
          (Cocone.mk X (NatTrans.ofSequence stageToTarget stageToTarget_naturality))).hom)
  /-- The descended colimit map already has the degreewise Chapter 9 `π_*` control. -/
  piControl :
    ∀ n : ℕ,
      HasPiInjectiveSurjectiveSucc n
        ((Limits.colimit.desc F
            (Cocone.mk X (NatTrans.ofSequence stageToTarget stageToTarget_naturality))).hom)

/-- Helper for Theorem 10.5.1: a HELP-controlled version of the stagewise interface keeps the
same staged CW skeleton but stores the Chapter 9 lifting condition directly in each degree. -/
structure StagewiseHelpApproximationData (X : TopCat.{u}) where
  /-- The staged diagram `F₀ ⟶ F₁ ⟶ F₂ ⟶ ⋯` used to approximate `X`. -/
  F : ℕ ⥤ TopCat.{u}
  /-- The stage-zero object is initial, so the staged diagram starts from the empty CW stage. -/
  isoBot : F.obj 0 ≅ ⊥_ TopCat.{u}
  /-- Each successor map is an abstract `n`-cell attachment. -/
  attachCells :
    ∀ n : ℕ,
      HomotopicalAlgebra.AttachCells.{u}
        (TopCat.RelativeCWComplex.basicCell n)
        (F.map (homOfLE (Nat.le_add_right n 1)))
  /-- The staged maps to `X` that will descend to the final comparison map. -/
  stageToTarget : ∀ n : ℕ, F.obj n ⟶ X
  /-- The staged maps form a cocone over the sequential diagram. -/
  stageToTarget_naturality :
    ∀ n : ℕ,
      F.map (homOfLE (Nat.le_add_right n 1)) ≫ stageToTarget (n + 1) =
        stageToTarget n ≫
          ((Functor.const ℕ).obj X).map (homOfLE (Nat.le_add_right n 1))
  /-- The descended colimit map already has the required `0`-equivalence input. -/
  zeroEquivalence :
    IsNEquivalence 0
      ((Limits.colimit.desc F
          (Cocone.mk X (NatTrans.ofSequence stageToTarget stageToTarget_naturality))).hom)
  /-- The descended colimit map already has the degreewise HELP condition. -/
  helpControl :
    ∀ n : ℕ,
      HasSphereConeHelp n
        ((Limits.colimit.desc F
            (Cocone.mk X (NatTrans.ofSequence stageToTarget stageToTarget_naturality))).hom)

namespace StagewiseHelpApproximationData

variable {X : TopCat.{u}}

/-- Helper for Theorem 10.5.1: the cocone from the HELP-controlled staged approximation diagram
to the target. -/
def stageCocone (data : StagewiseHelpApproximationData X) : Cocone data.F :=
  Cocone.mk _ (NatTrans.ofSequence data.stageToTarget data.stageToTarget_naturality)

/-- Helper for Theorem 10.5.1: the source `Γ X` obtained as the colimit of the HELP-controlled
stage diagram. -/
abbrev colimitSpace (data : StagewiseHelpApproximationData X) : TopCat.{u} :=
  Limits.colimit data.F

/-- Helper for Theorem 10.5.1: the descended comparison map from the HELP-controlled colimit to
`X`. -/
abbrev colimitMap (data : StagewiseHelpApproximationData X) : data.colimitSpace ⟶ X :=
  Limits.colimit.desc data.F data.stageCocone

/-- Helper for Theorem 10.5.1: each HELP-controlled stage map factors through the descended
colimit map. -/
theorem stageInclusion_comp_colimitMap (data : StagewiseHelpApproximationData X) (n : ℕ) :
    Limits.colimit.ι data.F n ≫ data.colimitMap = data.stageToTarget n := by
  -- The HELP-controlled cocone descends through the colimit exactly as in the `π_*` interface.
  simpa [colimitMap, stageCocone] using Limits.colimit.ι_desc data.stageCocone n

/-- Helper for Theorem 10.5.1: the descended HELP-controlled colimit map keeps the stored
`0`-equivalence input. -/
theorem colimitMap_isNEquivalenceZero (data : StagewiseHelpApproximationData X) :
    IsNEquivalence 0 data.colimitMap.hom := by
  -- This is exactly the degree-zero control stored in the HELP-controlled interface.
  simpa [colimitMap, stageCocone] using data.zeroEquivalence

/-- Helper for Theorem 10.5.1: the descended HELP-controlled colimit map keeps the stored
all-degree HELP control. -/
theorem colimitMap_hasSphereConeHelpAll (data : StagewiseHelpApproximationData X) :
    ∀ n : ℕ, HasSphereConeHelp n data.colimitMap.hom := by
  intro n
  -- The HELP-controlled interface already stores the required lifting property in each degree.
  simpa [colimitMap, stageCocone] using data.helpControl n

/-- Helper for Theorem 10.5.1: HELP-controlled stagewise data converts directly to the existing
`π_*`-controlled interface by using Lemma 9.6.6 in each degree. -/
def toStagewiseApproximationData (data : StagewiseHelpApproximationData X) :
    StagewiseApproximationData X :=
  { F := data.F
    isoBot := data.isoBot
    attachCells := data.attachCells
    stageToTarget := data.stageToTarget
    stageToTarget_naturality := data.stageToTarget_naturality
    zeroEquivalence := data.zeroEquivalence
    piControl := fun n ↦
      -- Convert the stored HELP witness once at the interface boundary.
      (data.helpControl n).hasPiInjectiveSurjectiveSucc }

end StagewiseHelpApproximationData

/-- Helper for Theorem 10.5.1: once the HELP-controlled stage constructors are in place, they
assemble into the bridge interface used to recover `StagewiseApproximationData`. -/
theorem existsStagewiseHelpApproximationData (X : TopCat.{u}) :
    Nonempty (StagewiseHelpApproximationData X) := by
  -- Route correction: the remaining source-faithful work is to construct the HELP-controlled
  -- skeleton itself, not to re-prove the final Chapter 9 conversion inside the main wrapper.
  -- TODO: package the stage-`0` empty-to-points attachment, the connecting `1`-cell stage, and
  -- the higher successor `HasSphereConeHelp` attachments into one `StagewiseHelpApproximationData`.
  sorry

namespace StagewiseApproximationData

variable {X : TopCat.{u}}

/-- Helper for Theorem 10.5.1: the cocone from the staged approximation diagram to the target. -/
def stageCocone (data : StagewiseApproximationData X) : Cocone data.F :=
  Cocone.mk _ (NatTrans.ofSequence data.stageToTarget data.stageToTarget_naturality)

/-- Helper for Theorem 10.5.1: the source `Γ X` obtained as the colimit of the stagewise diagram.
-/
abbrev colimitSpace (data : StagewiseApproximationData X) : TopCat.{u} :=
  Limits.colimit data.F

/-- Helper for Theorem 10.5.1: the comparison map from the stagewise colimit to `X`. -/
abbrev colimitMap (data : StagewiseApproximationData X) : data.colimitSpace ⟶ X :=
  Limits.colimit.desc data.F data.stageCocone

/-- Helper for Theorem 10.5.1: each stage map factors through the descended colimit map. -/
theorem stageInclusion_comp_colimitMap (data : StagewiseApproximationData X) (n : ℕ) :
    Limits.colimit.ι data.F n ≫ data.colimitMap = data.stageToTarget n := by
  -- The colimit descends the stage cocone by construction.
  simpa [colimitMap, stageCocone] using Limits.colimit.ι_desc data.stageCocone n

/-- Helper for Theorem 10.5.1: the stagewise colimit carries the abstract CW-complex structure
coming from the recorded attachment data. -/
noncomputable def colimitCwComplex (data : StagewiseApproximationData X) :
    TopCat.CWComplex data.colimitSpace :=
  -- Route correction: build the abstract CW owner directly from the staged diagram instead of
  -- routing through the stalled singular-realization bridge.
  { F := data.F
    isoBot := data.isoBot
    incl := Limits.colimit.cocone data.F |>.ι
    isColimit := Limits.colimit.isColimit data.F
    attachCells := by
      intro n hn
      -- Each successor stage already records the required basic-cell attachment.
      simpa using data.attachCells n }

/-- Helper for Theorem 10.5.1: the descended colimit map keeps the stored `0`-equivalence input.
-/
theorem colimitMap_isNEquivalenceZero (data : StagewiseApproximationData X) :
    IsNEquivalence 0 data.colimitMap.hom := by
  -- This is exactly the degree-zero control stored in the stagewise interface.
  simpa [colimitMap, stageCocone] using data.zeroEquivalence

/-- Helper for Theorem 10.5.1: the descended colimit map keeps the stored all-degree Chapter 9
`π_*` control. -/
theorem colimitMap_hasPiInjectiveSurjectiveSuccAll (data : StagewiseApproximationData X) :
    ∀ n : ℕ, HasPiInjectiveSurjectiveSucc n data.colimitMap.hom := by
  intro n
  -- This is exactly the degreewise `π_*` control stored in the stagewise interface.
  simpa [colimitMap, stageCocone] using data.piControl n

end StagewiseApproximationData

/-- Helper for Theorem 10.5.1: every space should admit the source-faithful stagewise
approximation data needed for the final CW witness. -/
theorem existsStagewiseApproximationData (X : TopCat.{u}) :
    Nonempty (StagewiseApproximationData X) :=
by
  -- Route correction: keep the existential frontier on the HELP-controlled skeleton layer and
  -- reuse the one-time Chapter 9 conversion only at this interface boundary.
  rcases existsStagewiseHelpApproximationData X with ⟨data⟩
  -- The adapter preserves all staged CW fields and converts only the degreewise control field.
  exact ⟨data.toStagewiseApproximationData⟩
