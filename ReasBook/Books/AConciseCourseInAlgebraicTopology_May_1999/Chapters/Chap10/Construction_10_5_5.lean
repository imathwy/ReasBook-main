import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Construction_10_6_4

open CategoryTheory
open scoped TopCat Topology Topology.Homotopy unitInterval

noncomputable section

universe u

-- Semantic recall via `lean_leansearch`: no public local owner surfaced for the specific
-- CW-approximation stage transition or for the equivalence between based sphere homotopy classes
-- and `π_ n`. The current chapter already exposes `reducedCylinder X = X ∧ I₊`, so this item
-- records the source step using explicit reduced-cylinder homotopy data, which is the canonical
-- way to witness equality of the corresponding `π_ n`-classes.

/-- Construction 10.5.5. For a current stage map `f_n : X_n ⟶ X`, a
`CWApproximationNextStage n X_n X x_n x f_n` packages one fixed next stage `X_(n+1)` together
with an inclusion `i_n : X_n ⟶ X_(n+1)`, an extension map `f_(n+1) : X_(n+1) ⟶ X`, and the
property that every reduced-cylinder homotopy in `X` between composites `a ≫ f_n` and `b ≫ f_n`
lifts to a reduced-cylinder attachment in that same next stage. -/
structure CWApproximationNextStage
    (n : ℕ) (X_n X : TopCat.{u}) (x_n : X_n) (x : X)
    (f_n : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X x) where
  /-- The next stage `X_(n+1)` in the CW approximation. -/
  X_next : TopCat.{u}
  /-- The chosen basepoint of the next stage `X_(n+1)`. -/
  x_next : X_next
  /-- The inclusion `i_n : X_n ⟶ X_(n+1)` of the current stage into the next stage. -/
  inclusion : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X_next x_next
  /-- The extension map `f_(n+1) : X_(n+1) ⟶ X`. -/
  toTarget : basedSpaceAtPoint X_next x_next ⟶ basedSpaceAtPoint X x
  /-- The stage map `f_n` factors through the inclusion into the next stage. -/
  fac : inclusion ≫ toTarget = f_n
  /-- Every reduced-cylinder homotopy in `X` between composites `a ≫ f_n` and `b ≫ f_n` lifts to
  a reduced-cylinder homotopy in the fixed next stage `X_(n+1)`. -/
  lift (a b : basedSphere n ⟶ basedSpaceAtPoint X_n x_n)
      (K : reducedCylinder (basedSphere n) ⟶ basedSpaceAtPoint X x)
      (hK₀ : ∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy K (s, 0) = (a ≫ f_n).right.hom s)
      (hK₁ : ∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy K (s, 1) = (b ≫ f_n).right.hom s) :
      ∃ H :
        reducedCylinder (basedSphere n) ⟶ basedSpaceAtPoint X_next x_next,
        (∀ s : (basedSphere n).right,
          reducedCylinderToBasedHomotopy H (s, 0) = (a ≫ inclusion).right.hom s) ∧
        (∀ s : (basedSphere n).right,
          reducedCylinderToBasedHomotopy H (s, 1) = (b ≫ inclusion).right.hom s) ∧
        H ≫ toTarget = K

/-- A `CWApproximationNextStage` canonically coerces to its underlying next-stage based space. -/
instance CWApproximationNextStage.instCoeToBasedSpace
    {n : ℕ} {X_n X : TopCat.{u}} {x_n : X_n} {x : X}
    {f_n : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X x} :
    CoeTC (CWApproximationNextStage n X_n X x_n x f_n) (BasedSpace.{u}) where
  coe X_nextStage := basedSpaceAtPoint X_nextStage.X_next X_nextStage.x_next

/-- The chosen basepoint of the next stage is `x_next`. -/
theorem CWApproximationNextStage.underTopBasepoint_coe
    {n : ℕ} {X_n X : TopCat.{u}} {x_n : X_n} {x : X}
    {f_n : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X x}
    (X_nextStage : CWApproximationNextStage n X_n X x_n x f_n) :
    underTopBasepoint (X_nextStage : BasedSpace.{u}) = X_nextStage.x_next :=
  rfl

/-- The stage map factors through the chosen inclusion into the fixed next stage. -/
@[simp] theorem CWApproximationNextStage.inclusion_comp_toTarget
    {n : ℕ} {X_n X : TopCat.{u}} {x_n : X_n} {x : X}
    {f_n : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X x}
    (X_nextStage : CWApproximationNextStage n X_n X x_n x f_n) :
    X_nextStage.inclusion ≫ X_nextStage.toTarget = f_n := by
  exact X_nextStage.fac

/-- A `CWApproximationNextStage` supplies the lifted reduced-cylinder attachment in its fixed next
stage for any pair of maps whose composites with `f_n` are homotopic in `X`. -/
theorem CWApproximationNextStage.lift_spec
    {n : ℕ} {X_n X : TopCat.{u}} {x_n : X_n} {x : X}
    {f_n : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X x}
    (X_nextStage : CWApproximationNextStage n X_n X x_n x f_n)
    (a b : basedSphere n ⟶ basedSpaceAtPoint X_n x_n)
    (K : reducedCylinder (basedSphere n) ⟶ basedSpaceAtPoint X x)
    (hK₀ : ∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy K (s, 0) = (a ≫ f_n).right.hom s)
    (hK₁ : ∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy K (s, 1) = (b ≫ f_n).right.hom s) :
    ∃ H :
      reducedCylinder (basedSphere n) ⟶ X_nextStage,
      (∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy H (s, 0) = (a ≫ X_nextStage.inclusion).right.hom s) ∧
      (∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy H (s, 1) = (b ≫ X_nextStage.inclusion).right.hom s) ∧
      H ≫ X_nextStage.toTarget = K := sorry
