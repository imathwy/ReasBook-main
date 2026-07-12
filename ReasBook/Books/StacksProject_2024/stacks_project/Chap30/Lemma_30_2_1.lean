import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.Lemma_18_14_2
import StacksProject_2024.Chap20.«20_11_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- The source-facing cover here is the standard affine-basic-open family, while the Čech
-- cohomology owner itself is the canonical Chapter 20 declaration
-- `RingedSpace.moduleCechCohomology`.

open AlgebraicGeometry.RingedSpace

variable {X : Scheme.{u}}

/-- The standard affine-basic-open cover of an affine open `U` cut out by a finite family of
sections `f`. This is the cover family fed to the Čech-cohomology owner. -/
abbrev standardAffineOpenCover
    (U : X.affineOpens) {n : ℕ} (f : Fin n → Γ(X, U)) :
    ULift.{u, 0} (Fin n) → X.Opens :=
  fun i ↦ X.affineBasicOpen (f i.down)

@[simp] theorem standardAffineOpenCover_apply
    (U : X.affineOpens) {n : ℕ} (f : Fin n → Γ(X, U))
    (i : ULift.{u, 0} (Fin n)) :
    standardAffineOpenCover U f i = X.affineBasicOpen (f i.down) :=
  rfl

/-- A finite family of sections of an affine open is a standard affine-basic-open cover exactly
when those sections generate the unit ideal. -/
def IsStandardAffineOpenCover
    (U : X.affineOpens) {n : ℕ} (f : Fin n → Γ(X, U)) : Prop :=
  Ideal.span (Set.range f) = ⊤

@[simp] theorem isStandardAffineOpenCover_iff
    (U : X.affineOpens) {n : ℕ} (f : Fin n → Γ(X, U)) :
    IsStandardAffineOpenCover U f ↔ Ideal.span (Set.range f) = ⊤ :=
  Iff.rfl

/-- Core/canonical positive-degree form of Lemma 30.2.1: for a standard affine-basic-open cover,
the Čech cohomology of a quasi-coherent module vanishes in every successor degree. -/
theorem moduleCechCohomology_isZero_of_standardAffineOpenCover_succ
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : X.affineOpens) {n : ℕ} (f : Fin n → Γ(X, U))
    (hf : IsStandardAffineOpenCover U f) (p : ℕ) :
    IsZero (moduleCechCohomology (standardAffineOpenCover U f) ℱ (p + 1)) := by
  sorry

/-- Lemma 30.2.1: let `X` be a scheme, let `ℱ` be a quasi-coherent `\mathcal O_X`-module, and
let `U = ⋃ᵢ D(fᵢ)` be a standard open covering of an affine open of `X`, encoded by an affine open
`U : X.affineOpens` and a finite family `f : Fin n → Γ(X, U)` generating the unit ideal. Then the
positive-degree Čech cohomology of `ℱ` on that standard affine-basic-open cover vanishes. -/
@[stacks 01X9]
theorem moduleCechCohomology_isZero_of_standardAffineOpenCover
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : X.affineOpens) {n : ℕ} (f : Fin n → Γ(X, U))
    (hf : IsStandardAffineOpenCover U f)
    (p : ℕ) (hp : 0 < p) :
    IsZero (moduleCechCohomology (standardAffineOpenCover U f) ℱ p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  simpa [Nat.succ_eq_add_one, Nat.add_comm] using
    moduleCechCohomology_isZero_of_standardAffineOpenCover_succ ℱ U f hf q

end AlgebraicGeometry.Scheme
