import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Adjunction_8_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_5_3.Skeleton

open CategoryTheory
open Topology
open scoped TopCat Topology Topology.Homotopy unitInterval

noncomputable section

universe u v

private instance sphereLocallyCompactSpace (n : ℕ) : LocallyCompactSpace (𝕊 n) :=
  (Homeomorph.locallyCompactSpace_iff
      (Homeomorph.ulift : 𝕊 n ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).2
    inferInstance

private instance basedSphereLocallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (basedSphere n).right := by
  change LocallyCompactSpace (𝕊 n)
  infer_instance

section

variable {Y : Type u} [TopologicalSpace Y]

/- The coefficient bridge is a source-facing view from the Chapter 9 fiber owner to the Chapter 14
based-sphere-class owner. We keep only the forward map on path components used by Chapter 18 and
build it from an actual path-in-mapping-space to based homotopy, so this file introduces no new
quotient-lift equivalence data. -/

private abbrev sphereBasepointFiberToUnderBasedMapSpace
    (n : ℕ) (y₀ : Y) :
    C(sphereBasepointFiber n y₀,
      underBasedMapSpace (basedSphere n) (underTopOfPoint Y y₀)) where
  toFun := sphereBasepointFiberBasedMapSpaceHomeomorph n y₀
  continuous_toFun := (sphereBasepointFiberBasedMapSpaceHomeomorph n y₀).continuous_toFun

private def underBasedMapSpaceToBasedMap
    {X Y : Under (⊤_ TopCat.{u})} (f : underBasedMapSpace X Y) :
    X ⟶ Y :=
  Under.homMk (TopCat.ofHom f.1) (by
    ext x
    have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
      cases h : TopCat.terminalIsoPUnit.hom x
      rfl
    have hx' :
        X.hom x = X.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
      simp
    calc
      (X.hom ≫ TopCat.ofHom f.1) x = f.1 (X.hom x) := rfl
      _ = f.1 (X.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x))) := by
        rw [hx']
      _ = f.1 (X.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)) := by rw [hx]
      _ = underTopBasepoint Y := f.2
      _ = Y.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
      _ = Y.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by rw [hx]
      _ = Y.hom x := by simp)

private theorem basedHomotopyClass_eq_of_joined
    {X Y : Under (⊤_ TopCat.{u})} [LocallyCompactSpace X.right]
    {f g : underBasedMapSpace X Y} (hfg : Joined f g) :
    (Quotient.mk (basedHomotopySetoid X Y) (underBasedMapSpaceToBasedMap f) :
      basedHomotopyClasses X Y) =
      Quotient.mk (basedHomotopySetoid X Y) (underBasedMapSpaceToBasedMap g) := by
  apply Quotient.sound
  change Relation.EqvGen
      (fun a b : X ⟶ Y ↦ basedHomotopyRel a b)
      (underBasedMapSpaceToBasedMap f) (underBasedMapSpaceToBasedMap g)
  let p := hfg.somePath
  let r : C(I, C(X.right, Y.right)) := {
    toFun := fun t ↦ (p.toContinuousMap t).1
    continuous_toFun := continuous_subtype_val.comp p.toContinuousMap.continuous
  }
  exact Relation.EqvGen.rel _ _
    (show basedHomotopyRel (underBasedMapSpaceToBasedMap f) (underBasedMapSpaceToBasedMap g) from
      ⟨{
        toHomotopy := {
          toContinuousMap := r.uncurry
          map_zero_left := by
            intro x
            change (r 0) x = f.1 x
            exact congrArg (fun h : underBasedMapSpace X Y ↦ h.1 x) p.source
          map_one_left := by
            intro x
            change (r 1) x = g.1 x
            exact congrArg (fun h : underBasedMapSpace X Y ↦ h.1 x) p.target
        }
        prop' := by
          intro t x hx
          have hx' : x = underTopBasepoint X := by simpa using hx
          subst hx'
          change r t (underTopBasepoint X) = f.1 (underTopBasepoint X)
          rw [f.2]
          exact (p.toContinuousMap t).2
      }⟩)

private def zerothHomotopyUnderBasedMapSpaceToBasedHomotopyClasses
    {X Y : Under (⊤_ TopCat.{u})} [LocallyCompactSpace X.right] :
    ZerothHomotopy (underBasedMapSpace X Y) → basedHomotopyClasses X Y :=
  Quotient.lift
    (fun f : underBasedMapSpace X Y ↦
      (Quotient.mk (basedHomotopySetoid X Y) (underBasedMapSpaceToBasedMap f) :
        basedHomotopyClasses X Y))
    (fun _ _ hfg ↦ basedHomotopyClass_eq_of_joined hfg)

/-- The path-component class of the Chapter 9 sphere-evaluation fiber over `y₀`, viewed as a based
homotopy class `Ho*[basedSphere n, underTopOfPoint Y y₀]` via the canonical based-mapping-space
owner. -/
@[expose] abbrev sphereBasepointFiberZerothToBasedHomotopyClasses
    (n : ℕ) (y₀ : Y) :
    ZerothHomotopy (sphereBasepointFiber n y₀) →
      basedHomotopyClasses (basedSphere n) (underTopOfPoint Y y₀) :=
  fun η ↦
    zerothHomotopyUnderBasedMapSpaceToBasedHomotopyClasses
      (zerothHomotopyMap (sphereBasepointFiberToUnderBasedMapSpace n y₀) η)

/-- Composing the canonical sphere-fiber-to-based-sphere-class map with a chosen
`HurewiczComparison n (underTopOfPoint Y y₀)` gives the coefficient map from the Chapter 9
sphere-evaluation fiber owner to the canonical homotopy group `π_ n(Y, y₀)`. -/
@[expose] abbrev sphereBasepointFiberZerothToHomotopyGroup
    (n : ℕ) (y₀ : Y)
    (comparison : HurewiczComparison n (underTopOfPoint Y y₀)) :
    ZerothHomotopy (sphereBasepointFiber n y₀) → π_ n Y y₀ :=
  comparison ∘ sphereBasepointFiberZerothToBasedHomotopyClasses n y₀

end

section

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable [CWComplex (Set.univ : Set X)]
variable (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
variable [Topology.RelCWComplex (Set.univ : Set X) (A : Set X)]
variable {Y : Type v} [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace Y]

/-- The canonical obstruction cochain from Construction 18.5.2, rewritten through the Chapter 9
sphere-fiber-to-based-sphere-class bridge and a chosen Hurewicz comparison so that its values lie
in `π_ n(Y, y₀)`. -/
@[expose] abbrev relativeSkeletonObstructionHomotopyGroupCochain
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    (comparison : HurewiczComparison n (underTopOfPoint Y y₀))
    (f : C(relativePairSkeleton A n, Y)) :
    Topology.RelCWComplex.cell (Set.univ : Set X) (n + 1) →
      π_ n Y y₀ :=
  fun j ↦ sphereBasepointFiberZerothToHomotopyGroup n y₀ comparison
    (obstructionCochain (Set.univ : Set X) n y₀ f j)

/-- The canonical additive-valued obstruction cochain used for relative cellular cohomology with
coefficients in `Additive (π_ n(Y, y₀))`, relative to a chosen Hurewicz comparison on
`underTopOfPoint Y y₀`. -/
@[expose] abbrev relativeSkeletonObstructionAdditiveCochain
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    (comparison : HurewiczComparison n (underTopOfPoint Y y₀))
    [CommGroup (π_ n Y y₀)]
    (f : C(relativePairSkeleton A n, Y)) :
    Topology.RelCWComplex.cell (Set.univ : Set X) (n + 1) →
      Additive (π_ n Y y₀) :=
  fun j ↦ Additive.ofMul (relativeSkeletonObstructionHomotopyGroupCochain A n y₀ comparison f j)

end
