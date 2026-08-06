import Mathlib.Algebra.Exact
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_4_1

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

universe w

-- This file reuses Chapter 14's canonical `ReducedSuspensionCofiberSetup` owner for the chosen
-- reduced suspension and cofiber data on `nondegeneratelyBasedSpace`.

local notation "NBasedSpace" => nondegeneratelyBasedSpace

/-- Contravariant exactness for cofibrations in a `ℤ`-graded family of functors on
nondegenerately based spaces, relative to a chosen Chapter 14 reduced suspension/cofiber setup. -/
class ReducedCohomologyCofibrationExact
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat) : Prop where
  /-- For a cofibration `i : A ⟶ X`, the sequence
  `E q (cofiber i) ⟶ E q X ⟶ E q A ⟶ E (q + 1) (cofiber i)` is exact in the usual
  contravariant abelian-group sense. -/
  exactness :
    ∀ q {A X : NBasedSpace} (i : A ⟶ X) [Cofibration i],
      ∃ δ :
          (E q).obj (Opposite.op A) ⟶
            (E (q + 1)).obj (Opposite.op (setup.cofiber.obj (Arrow.mk i))),
        Function.Exact ((E q).map (setup.cofiberMap i).op) ((E q).map i.op) ∧
          Function.Exact ((E q).map i.op) δ

/-- Suspension isomorphisms for a `ℤ`-graded family of contravariant functors on
nondegenerately based spaces. -/
class ReducedCohomologySuspension
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat) : Prop where
  /-- Each degree `q` admits a natural suspension isomorphism
  `(E q).obj (Opposite.op (suspension.obj X)) ≅ (E (q - 1)).obj (Opposite.op X)`. -/
  suspensionIso : ∀ q, Nonempty (setup.suspension.op ⋙ E q ≅ E (q - 1))

/-- Definition 19.2.1: relative to a chosen reduced suspension endofunctor and cofiber
construction on nondegenerately based spaces, formalized here as the full subcategory of
cofibrant objects in `BasedSpace`, a reduced cohomology theory is a `ℤ`-graded family of
contravariant functors `NBasedSpaceᵒᵖ ⥤ AddCommGrpCat` satisfying cofibration exactness,
suspension, wedge additivity as products, and weak-equivalence invariance. -/
class ReducedCohomologyTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat) : Prop
    extends ReducedCohomologyCofibrationExact setup E,
      ReducedCohomologySuspension setup E where
  /-- Each degree functor sends wedges indexed by a discrete type to products. -/
  preservesWedgeProducts :
    ∀ q {ι : Type w}, PreservesLimitsOfShape (Discrete ι) (E q)
  /-- A weak equivalence of based spaces induces an isomorphism in every degree after applying
  the contravariant functor `E q`. -/
  map_isIso :
    ∀ q {X Y : NBasedSpace} (f : X ⟶ Y) [WeakEquivalence f], IsIso ((E q).map f.op)

/-- A `π`-normalized reduced cohomology theory on nondegenerately based spaces is a reduced
cohomology theory whose value at a chosen initial object `pt` modeling the one-point based space
has degree-zero coefficient group `π` and vanishes away from degree `0`. -/
class NormalizedReducedCohomologyTheory
    (π : Type) [AddCommGroup π]
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (pt : NBasedSpace)
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0}) : Prop
    extends ReducedCohomologyTheory setup E where
  /-- The degree-zero value at `pt` is isomorphic to the coefficient group `π`. -/
  zeroIso : Nonempty (((E 0).obj (Opposite.op pt)) ≅ AddCommGrpCat.of π)
  /-- The value at `pt` vanishes away from degree `0`. -/
  isZero_cohomology : ∀ q : ℤ, q ≠ 0 → IsZero ((E q).obj (Opposite.op pt))

/-- A reduced cohomology theory on nondegenerately based spaces, bundled as a graded family of
functors together with the `ReducedCohomologyTheory` predicate from Definition 19.2.1. -/
abbrev ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup) :=
  { E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0} //
      ReducedCohomologyTheory.{0, w, 0} setup E }

/-- The bundled reduced cohomology theories determined by a chosen Chapter 14 reduced
suspension/cofiber setup. -/
abbrev ReducedSuspensionCofiberSetup.reducedCohomologyTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup) :=
  ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces setup

/-- The underlying graded functor of a bundled reduced cohomology theory. -/
abbrev ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces.cohomology
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (E : ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0} :=
  E.1

/-- A bundled reduced cohomology theory carries the Definition 19.2.1 axioms on its underlying
graded functor. -/
instance reducedCohomologyTheoryOnNondegeneratelyBasedSpacesToReducedCohomologyTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (E : ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    ReducedCohomologyTheory.{0, w, 0} setup E.1 :=
  E.2

/-- A bundled reduced cohomology theory is determined by its underlying graded functor together
with the Definition 19.2.1 axioms. -/
theorem ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces.spec
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (E : ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    ReducedCohomologyTheory.{0, w, 0} setup E.1 :=
  E.2

/-- A `π`-normalized reduced cohomology theory on nondegenerately based spaces, bundled as a
reduced cohomology theory together with the coefficient normalization at a chosen initial object
`pt`. -/
abbrev NormalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpaces
    (π : Type) [AddCommGroup π]
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (pt : NBasedSpace)
    (setup : ReducedSuspensionCofiberSetup) :=
  { E : ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces setup //
      NormalizedReducedCohomologyTheory.{w, 0} π pt setup E.1 }

/-- The `π`-normalized bundled reduced cohomology theories determined by a chosen Chapter 14
reduced suspension/cofiber setup. -/
abbrev ReducedSuspensionCofiberSetup.normalizedReducedCohomologyTheory
    (π : Type) [AddCommGroup π]
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (pt : NBasedSpace) :=
  NormalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpaces π pt setup

/-- The underlying graded functor of a `π`-normalized bundled reduced cohomology theory. -/
abbrev NormalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpaces.cohomology
    (π : Type) [AddCommGroup π]
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {pt : NBasedSpace}
    {setup : ReducedSuspensionCofiberSetup}
    (E : NormalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpaces π pt setup) :
    ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0} :=
  E.1.1

/-- A `π`-normalized bundled reduced cohomology theory carries the Definition 19.2.1
normalization axioms on its underlying graded functor. -/
instance
    normalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpacesToNormalizedReducedCohomologyTheory
    (π : Type) [AddCommGroup π]
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {pt : NBasedSpace}
    {setup : ReducedSuspensionCofiberSetup}
    (E : NormalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpaces π pt setup) :
    NormalizedReducedCohomologyTheory.{w, 0} π pt setup E.1.1 :=
  E.2

/-- A `π`-normalized bundled reduced cohomology theory is determined by its underlying reduced
theory together with the coefficient normalization at `pt`. -/
theorem NormalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpaces.spec
    (π : Type) [AddCommGroup π]
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {pt : NBasedSpace}
    {setup : ReducedSuspensionCofiberSetup}
    (E : NormalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpaces π pt setup) :
    NormalizedReducedCohomologyTheory.{w, 0} π pt setup E.1.1 :=
  E.2

/-- A reduced cohomology theory satisfies the cofibration exactness axiom. -/
instance reducedCohomologyTheoryToReducedCohomologyCofibrationExact
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat}
    [h : ReducedCohomologyTheory setup E] :
    ReducedCohomologyCofibrationExact setup E :=
  h.toReducedCohomologyCofibrationExact

/-- A reduced cohomology theory satisfies the suspension axiom. -/
instance reducedCohomologyTheoryToReducedCohomologySuspension
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat}
    [h : ReducedCohomologyTheory setup E] :
    ReducedCohomologySuspension setup E :=
  h.toReducedCohomologySuspension

/-- A normalized reduced cohomology theory is determined by the coefficient normalization at
`pt`, together with its underlying reduced-theory field. -/
theorem NormalizedReducedCohomologyTheory.spec
    (π : Type) [AddCommGroup π]
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {pt : NBasedSpace}
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0}}
    [h : NormalizedReducedCohomologyTheory π pt setup E] :
    Nonempty (((E 0).obj (Opposite.op pt)) ≅ AddCommGrpCat.of π) ∧
      ∀ q : ℤ, q ≠ 0 → IsZero ((E q).obj (Opposite.op pt)) := by
  constructor
  · exact h.zeroIso
  · exact h.isZero_cohomology

namespace NormalizedReducedCohomologyTheory

/-- The degree-zero value at `pt` is isomorphic to the coefficient group `π`. -/
theorem zeroIso_nonempty
    (π : Type) [AddCommGroup π]
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {pt : NBasedSpace}
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0}}
    [h : NormalizedReducedCohomologyTheory π pt setup E] :
    Nonempty ((E 0).obj (Opposite.op pt) ≅ AddCommGrpCat.of π) :=
  h.zeroIso

/-- The value of a normalized reduced cohomology theory at `pt` vanishes away from degree `0`. -/
theorem isZero_cohomology_ne_zero
    (π : Type) [AddCommGroup π]
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {pt : NBasedSpace}
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0}}
    [h : NormalizedReducedCohomologyTheory π pt setup E]
    {q : ℤ} (hq : q ≠ 0) :
    IsZero ((E q).obj (Opposite.op pt)) :=
  h.isZero_cohomology q hq

end NormalizedReducedCohomologyTheory

/-- A reduced cohomology theory carries the exactness and suspension companion owners, while its
wedge-additivity and weak-equivalence data remain available as fields. -/
theorem ReducedCohomologyTheory.spec
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat}
    [h : ReducedCohomologyTheory setup E] :
    ReducedCohomologyCofibrationExact setup E ∧
      ReducedCohomologySuspension setup E := by
  constructor
  · infer_instance
  · infer_instance

namespace ReducedCohomologySuspension

/-- The suspension axiom provides a natural isomorphism in degree `q`. -/
theorem suspensionIso_nonempty
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat}
    [h : ReducedCohomologySuspension setup E]
    (q : ℤ) :
    Nonempty (setup.suspension.op ⋙ E q ≅ E (q - 1)) := by
  exact h.suspensionIso q

/-- The suspension axiom determines a chosen natural suspension isomorphism in degree `q`. -/
noncomputable abbrev suspensionNatIso
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat}
    [h : ReducedCohomologySuspension setup E]
    (q : ℤ) :
    setup.suspension.op ⋙ E q ≅ E (q - 1) :=
  Classical.choice (h.suspensionIso q)

/-- Applying the chosen suspension isomorphism at `X` yields the degree-shift isomorphism
`(E q)(ΣX) ≅ (E (q - 1))(X)`. -/
noncomputable abbrev suspensionIsoApp
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat}
    [ReducedCohomologySuspension setup E]
    (q : ℤ) (X : NBasedSpace) :
    (E q).obj (Opposite.op (setup.suspension.obj X)) ≅
      (E (q - 1)).obj (Opposite.op X) :=
  (suspensionNatIso q).app (Opposite.op X)

/-- Applying the suspension axiom at a fixed nondegenerately based space yields the degree-shift
isomorphism `(E q)(ΣX) ≅ (E (q - 1))(X)`. -/
theorem suspensionIsoApp_nonempty
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat}
    [h : ReducedCohomologySuspension setup E]
    (q : ℤ) (X : NBasedSpace) :
    Nonempty ((E q).obj (Opposite.op (setup.suspension.obj X)) ≅
      (E (q - 1)).obj (Opposite.op X)) := by
  exact ⟨suspensionIsoApp q X⟩

end ReducedCohomologySuspension

namespace ReducedCohomologyTheory

/-- A reduced cohomology theory determines a chosen natural suspension isomorphism in degree
`q`. -/
noncomputable abbrev suspensionNatIso
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat}
    [ReducedCohomologyTheory setup E]
    (q : ℤ) :
    setup.suspension.op ⋙ E q ≅ E (q - 1) :=
  ReducedCohomologySuspension.suspensionNatIso q

/-- Applying the chosen suspension isomorphism at `X` gives `(E q)(ΣX) ≅ (E (q - 1))(X)`. -/
noncomputable abbrev suspensionIsoApp
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat}
    [ReducedCohomologyTheory setup E]
    (q : ℤ) (X : NBasedSpace) :
    (E q).obj (Opposite.op (setup.suspension.obj X)) ≅
      (E (q - 1)).obj (Opposite.op X) :=
  ReducedCohomologySuspension.suspensionIsoApp q X

end ReducedCohomologyTheory
