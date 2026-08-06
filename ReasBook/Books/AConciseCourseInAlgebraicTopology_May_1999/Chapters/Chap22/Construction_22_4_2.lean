import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_6_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Construction_10_6_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Problem_22_6_1

open CategoryTheory
open scoped Topology Topology.Homotopy

noncomputable section

universe u

-- Semantic recall: Chapter 10 already owns the canonical repository abbreviation
-- `basedSpaceAtPoint`, while local Chapter 8/22 precedent fixes `IsBasedFibration`,
-- `homotopyFiber`, and `IsAdditiveEilenbergMacLaneSpace` as the source-facing owners for the
-- Postnikov-stage fibration and its Eilenberg-MacLane fibers.

variable {X : Type u} [TopologicalSpace X]

/-- The `n`th Postnikov stage of `P`, regarded as a based space via the image of `x : X`. -/
abbrev postnikovStageBased (P : PostnikovSystem X) (n : ℕ) (x : X) : BasedSpace :=
  basedSpaceAtPoint (P.stage n) (P.toStage n x)

/-- The stage bonding map preserves the chosen basepoints coming from `x : X`. -/
theorem postnikovBondingMap_w (P : PostnikovSystem X) (n : ℕ) (x : X) :
    (postnikovStageBased P (n + 1) x).hom ≫ TopCat.ofHom (P.bonding n) =
      (postnikovStageBased P n x).hom := by
  ext u
  change (P.bonding n) (P.toStage (n + 1) x) = P.toStage n x
  simpa using congrArg (fun f : C(X, P.stage n) ↦ f x) (P.bonding_comp_toStage n)

/-- The bonding map `X_(n+1) ⟶ X_n` of a Postnikov system, viewed as a based map using the
basepoint image of `x : X`. -/
def postnikovBondingMap (P : PostnikovSystem X) (n : ℕ) (x : X) :
    postnikovStageBased P (n + 1) x ⟶ postnikovStageBased P n x :=
  Under.homMk
    (TopCat.ofHom (P.bonding n))
    (postnikovBondingMap_w P n x)

/-- A bridge bundle packaging the explicit stage data from Construction 22.4.2.

The main public theorem `postnikov_stage_has_fibration_and_k_invariant` exposes the source-facing
existence statement directly; this structure is the thin reusable owner for consumers that want the
data as one object after choosing such a witness. -/
structure PostnikovStageConstruction (P : PostnikovSystem X) (x : X) (n : ℕ)
    [AddCommGroup (Additive (π_ (n + 1) X x))] where
  /-- A chosen based `K(π_(n+1)(X,x), n+2)` model receiving the stage `k`-invariant. -/
  kInvariantTarget : BasedSpace
  /-- The target of the `k`-invariant realizes `K(π_(n+1)(X,x), n+2)`. -/
  kInvariantTarget_isKPi :
    IsAdditiveEilenbergMacLaneSpace (Additive (π_ (n + 1) X x)) (n + 1) kInvariantTarget
  /-- The stage `k`-invariant from `X_n` into a chosen `K(π_(n+1)(X,x), n+2)` model. -/
  kInvariant : postnikovStageBased P n x ⟶ kInvariantTarget
  /-- The bonding map `X_(n+1) ⟶ X_n` is a based fibration at the chosen basepoint. -/
  bonding_isBasedFibration : IsBasedFibration (postnikovBondingMap P n x)
  /-- The actual fiber of the stage fibration realizes `K(π_(n+1)(X,x), n+1)`. -/
  fiber_isKPi :
    IsAdditiveEilenbergMacLaneSpace
      (Additive (π_ (n + 1) X x)) n
      (actualFiber (postnikovBondingMap P n x))
  /-- The next stage is modeled by the homotopy fiber of the chosen `k`-invariant. -/
  comparisonToHomotopyFiber :
    postnikovStageBased P (n + 1) x ⟶ homotopyFiber kInvariant
  /-- The comparison with the homotopy fiber is a based homotopy equivalence. -/
  comparisonToHomotopyFiber_isBasedHomotopyEquivalence :
    IsCofiberHomotopyEquivalence comparisonToHomotopyFiber

namespace PostnikovStageConstruction

variable {P : PostnikovSystem X} {x : X} {n : ℕ}
variable [AddCommGroup (Additive (π_ (n + 1) X x))]

/-- A packaged Postnikov-stage construction lets typeclass search recover that the stage bonding
map is a based fibration. -/
instance instIsBasedFibration
    (stage : PostnikovStageConstruction P x n) :
    IsBasedFibration (postnikovBondingMap P n x) :=
  stage.bonding_isBasedFibration

/-- The comparison map carried by a packaged Postnikov-stage construction is a based homotopy
equivalence. -/
instance instIsCofiberHomotopyEquivalence
    (stage : PostnikovStageConstruction P x n) :
    IsCofiberHomotopyEquivalence stage.comparisonToHomotopyFiber :=
  stage.comparisonToHomotopyFiber_isBasedHomotopyEquivalence

end PostnikovStageConstruction

/-- Construction 22.4.2: for a Postnikov system `P` on a simple space `X`, each bonding map
`X_(n+1) ⟶ X_n` at a chosen basepoint `x : X` can be equipped with explicit stage-construction
data: it is a based fibration, its actual fiber is a `K(π_(n+1)(X,x), n+1)`, and the stage is
modeled by the homotopy fiber of a chosen `k`-invariant
`X_n ⟶ K(π_(n+1)(X,x), n+2)`. On the Lean surface, the simple-space input is reflected by the
commutative additive structure on `π_(n+1)(X,x)` needed to speak about these
Eilenberg-MacLane spaces. -/
theorem postnikov_stage_has_fibration_and_k_invariant
    (P : PostnikovSystem X) (x : X) (n : ℕ)
    [AddCommGroup (Additive (π_ (n + 1) X x))] :
    ∃ (kInvariantTarget : BasedSpace)
      (kInvariant : postnikovStageBased P n x ⟶ kInvariantTarget)
      (comparisonToHomotopyFiber :
        postnikovStageBased P (n + 1) x ⟶ homotopyFiber kInvariant),
      IsAdditiveEilenbergMacLaneSpace
          (Additive (π_ (n + 1) X x)) (n + 1) kInvariantTarget ∧
        IsBasedFibration (postnikovBondingMap P n x) ∧
        IsAdditiveEilenbergMacLaneSpace
          (Additive (π_ (n + 1) X x)) n
          (actualFiber (postnikovBondingMap P n x)) ∧
        IsCofiberHomotopyEquivalence comparisonToHomotopyFiber := sorry

/-- Any packaged `PostnikovStageConstruction` yields the explicit source-facing stage data from
Construction 22.4.2. -/
theorem PostnikovStageConstruction.exists_stage_data
    {P : PostnikovSystem X} {x : X} {n : ℕ}
    [AddCommGroup (Additive (π_ (n + 1) X x))]
    (stage : PostnikovStageConstruction P x n) :
    ∃ (kInvariantTarget : BasedSpace)
      (kInvariant : postnikovStageBased P n x ⟶ kInvariantTarget)
      (comparisonToHomotopyFiber :
        postnikovStageBased P (n + 1) x ⟶ homotopyFiber kInvariant),
      IsAdditiveEilenbergMacLaneSpace
          (Additive (π_ (n + 1) X x)) (n + 1) kInvariantTarget ∧
        IsBasedFibration (postnikovBondingMap P n x) ∧
        IsAdditiveEilenbergMacLaneSpace
          (Additive (π_ (n + 1) X x)) n
          (actualFiber (postnikovBondingMap P n x)) ∧
        IsCofiberHomotopyEquivalence comparisonToHomotopyFiber :=
  ⟨stage.kInvariantTarget, stage.kInvariant, stage.comparisonToHomotopyFiber,
    stage.kInvariantTarget_isKPi, stage.bonding_isBasedFibration, stage.fiber_isKPi,
    stage.comparisonToHomotopyFiber_isBasedHomotopyEquivalence⟩
