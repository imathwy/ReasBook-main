import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Module.ZMod
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_5_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_4_1

open CategoryTheory
open scoped DirectSum SteenrodAlgebra

noncomputable section

-- Semantic recall via `lean_leansearch` surfaced only unrelated general cohomology APIs. The
-- current repository already fixes the total mod-`2` cohomology owner in Chapter 22 and the
-- Steenrod algebra owner in Definition 25.4.1, so this file records the source-facing Steenrod
-- action data on `H^*(X; ZMod 2)` directly over those canonical owners.

/-- Pullback on the total graded mod-`2` cohomology direct sum `H^*(X; ZMod 2)`. -/
def modTwoCohomologyStarPullback (H2 : ModTwoCohomologyTheory) {X Y : TopCat} (f : X ⟶ Y) :
    modTwoCohomologyStar H2 Y →+ modTwoCohomologyStar H2 X :=
  DirectSum.map fun n ↦ ConcreteCategory.hom ((H2.cohomology n).map f.op)

/-- `modTwoCohomologyStarPullback` acts degreewise on the homogeneous summands of the total
mod-`2` cohomology direct sum. -/
theorem modTwoCohomologyStarPullback_lof
    (H2 : ModTwoCohomologyTheory) {X Y : TopCat} (f : X ⟶ Y) (q : ℕ)
    (x : modTwoCohomologyGroup H2 q Y) :
    modTwoCohomologyStarPullback H2 f
        (DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n Y) q x) =
      DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) q (((H2.cohomology q).map f.op) x) :=
  sorry

/-- The action of the Steenrod generator `Sq^i` on the total mod-`2` cohomology direct sum,
obtained by applying the degreewise operation `Sq.sq i q X` on each homogeneous summand and
re-inserting the result in degree `q + i`. -/
def modTwoCohomologyStarSqAction
    (H2 : ModTwoCohomologyTheory)
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (i : ℕ) (X : TopCat) :
    modTwoCohomologyStar H2 X →+ modTwoCohomologyStar H2 X :=
  DirectSum.toAddMonoid fun q ↦
    (DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) (q + i)).toAddMonoidHom.comp
      (ConcreteCategory.hom (Sq.sq i q X))

/-- `modTwoCohomologyStarSqAction` restricts on a homogeneous degree-`q` summand to the Steenrod
operation `Sq^i : H^q(X; ZMod 2) → H^(q + i)(X; ZMod 2)`. -/
theorem modTwoCohomologyStarSqAction_lof
    (H2 : ModTwoCohomologyTheory)
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (i q : ℕ) (X : TopCat) (x : modTwoCohomologyGroup H2 q X) :
    modTwoCohomologyStarSqAction H2 Sq i X
        (DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) q x) =
      DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) (q + i) (Sq.sq i q X x) :=
  sorry

/-- `modTwoCohomologyStarSqAction` commutes with pullback along maps of spaces. -/
theorem modTwoCohomologyStarSqAction_natural
    (H2 : ModTwoCohomologyTheory)
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    {X Y : TopCat} (f : X ⟶ Y) (i : ℕ) (x : modTwoCohomologyStar H2 Y) :
    modTwoCohomologyStarPullback H2 f (modTwoCohomologyStarSqAction H2 Sq i Y x) =
      modTwoCohomologyStarSqAction H2 Sq i X (modTwoCohomologyStarPullback H2 f x) :=
  sorry

/-- The action hom attached to a `ModTwoSteenrodAlgebra`-module structure on
`modTwoCohomologyStar H2 X`. -/
def modTwoCohomologyStarSteenrodAction
    (H2 : ModTwoCohomologyTheory) (X : TopCat)
    (module : Module ModTwoSteenrodAlgebra (modTwoCohomologyStar H2 X)) :
    ModTwoSteenrodAlgebra →+* AddMonoid.End (modTwoCohomologyStar H2 X) :=
  @Module.toAddMonoidEnd ModTwoSteenrodAlgebra (modTwoCohomologyStar H2 X)
    inferInstance inferInstance module

/-- A chosen Steenrod action on the total mod-`2` cohomology direct sum `H^*(X; ZMod 2)`,
recorded by the actual `ModTwoSteenrodAlgebra`-module structure on each `modTwoCohomologyStar H2 X`
together with the degreewise `Sq^i` formulas and pullback naturality used later in Chapter 25. -/
structure ModTwoCohomologySteenrodAction
    (H2 : ModTwoCohomologyTheory)
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso) where
  /-- The scalar action of `ModTwoSteenrodAlgebra` on `modTwoCohomologyStar H2 X`. -/
  module : ∀ X : TopCat, Module ModTwoSteenrodAlgebra (modTwoCohomologyStar H2 X)
  /-- On total cohomology, the generator `Sq^i ∈ ModTwoSteenrodAlgebra` acts by the
  corresponding degreewise Steenrod square. -/
  generator_smul :
    ∀ (X : TopCat) (i q : ℕ) (x : modTwoCohomologyGroup H2 q X),
      modTwoCohomologyStarSteenrodAction H2 X (module X) (Sq^i)
          (DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) q x) =
        (DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) (q + i) (Sq.sq i q X x) :
          modTwoCohomologyStar H2 X)
  /-- Pullback along a map of spaces is `ModTwoSteenrodAlgebra`-linear for the chosen action. -/
  naturality :
    ∀ {X Y : TopCat} (f : X ⟶ Y) (a : ModTwoSteenrodAlgebra)
      (x : modTwoCohomologyStar H2 Y),
      modTwoCohomologyStarPullback H2 f
          (modTwoCohomologyStarSteenrodAction H2 Y (module Y) a x) =
        modTwoCohomologyStarSteenrodAction H2 X (module X) a
          (modTwoCohomologyStarPullback H2 f x)

section

variable (H2 : ModTwoCohomologyTheory)
variable {suspension : TopCat ⥤ TopCat}
variable {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
variable (Sq : SteenrodSquareFamily H2 suspension suspensionIso)

/-- Lemma 25.4.2. The total mod-`2` cohomology of spaces carries a natural action of the
Steenrod algebra: there exists a simultaneous `ModTwoSteenrodAlgebra`-module structure on every
`H^*(X; ZMod 2)` whose generators act by the Steenrod squares and whose pullback maps are
linear.  The action is the conclusion here, rather than an input whose fields merely restate the
lemma. -/
theorem exists_modTwoCohomologySteenrodAction :
    Nonempty (ModTwoCohomologySteenrodAction H2 Sq) := by
  sorry

/-- A chosen natural Steenrod action supplies the module instance on a particular space. -/
instance modTwoCohomologyStarModule
    (action : ModTwoCohomologySteenrodAction H2 Sq) (X : TopCat) :
    Module ModTwoSteenrodAlgebra (modTwoCohomologyStar H2 X) :=
  action.module X

/-- Restricting scalars along `ZMod 2 → ModTwoSteenrodAlgebra` gives the underlying
`ZMod 2`-module on `modTwoCohomologyStar H2 X` for a chosen Steenrod action. -/
instance modTwoCohomologyStarBaseModule
    (action : ModTwoCohomologySteenrodAction H2 Sq) (X : TopCat) :
    Module (ZMod 2) (modTwoCohomologyStar H2 X) := by
  -- Local instance justification (proof-local temporary data): restricting scalars must use the
  -- chosen `ModTwoSteenrodAlgebra`-module structure supplied by `action` on
  -- `modTwoCohomologyStar H2 X`.
  letI := action.module X
  exact Module.compHom (modTwoCohomologyStar H2 X) (algebraMap (ZMod 2) ModTwoSteenrodAlgebra)

namespace ModTwoCohomologySteenrodAction

variable {H2}
variable {Sq : SteenrodSquareFamily H2 suspension suspensionIso}

/-- The explicit action hom of `ModTwoSteenrodAlgebra` on `modTwoCohomologyStar H2 X`
carried by a chosen Steenrod action. -/
abbrev actionHom
    (action : ModTwoCohomologySteenrodAction H2 Sq) (X : TopCat) :
    ModTwoSteenrodAlgebra →+* AddMonoid.End (modTwoCohomologyStar H2 X) :=
  modTwoCohomologyStarSteenrodAction H2 X (action.module X)

/-- The underlying `ZMod 2`-module on `modTwoCohomologyStar H2 X` obtained by restricting
scalars along `ZMod 2 → ModTwoSteenrodAlgebra` for the chosen Steenrod action. -/
abbrev baseModule
    (action : ModTwoCohomologySteenrodAction H2 Sq) (X : TopCat) :
    Module (ZMod 2) (modTwoCohomologyStar H2 X) :=
  modTwoCohomologyStarBaseModule H2 Sq action X

/-- The Steenrod generator `Sq^i ∈ ModTwoSteenrodAlgebra` acts on homogeneous classes in
`modTwoCohomologyStar H2 X` by the corresponding degreewise Steenrod square. -/
theorem smul_generator_eq_sq
    (action : ModTwoCohomologySteenrodAction H2 Sq)
    (X : TopCat) (i q : ℕ) (x : modTwoCohomologyGroup H2 q X) :
    action.actionHom X (Sq^i)
        (DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) q x) =
      (DirectSum.lof ℤ ℕ (fun n ↦ modTwoCohomologyGroup H2 n X) (q + i) (Sq.sq i q X x) :
        modTwoCohomologyStar H2 X) :=
  action.generator_smul X i q x

/-- Pullback along a map of spaces is `ModTwoSteenrodAlgebra`-linear for the chosen action on
`modTwoCohomologyStar H2`. -/
theorem pullback_smul
    (action : ModTwoCohomologySteenrodAction H2 Sq)
    {X Y : TopCat} (f : X ⟶ Y) (a : ModTwoSteenrodAlgebra)
    (x : modTwoCohomologyStar H2 Y) :
    modTwoCohomologyStarPullback H2 f (action.actionHom Y a x) =
      action.actionHom X a (modTwoCohomologyStarPullback H2 f x) := by
  simpa using action.naturality f a x

end ModTwoCohomologySteenrodAction

end
