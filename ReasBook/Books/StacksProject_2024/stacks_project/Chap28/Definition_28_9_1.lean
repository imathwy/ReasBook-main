import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import StacksProject_2024.stacks_project.Chap10.Definition_10_110_7
import StacksProject_2024.stacks_project.Chap28.Definition_28_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the scheme stalk API and local-Noetherian infrastructure, while local
-- Chapter 28 precedent packages affine-open local properties via `HasRingPropertyLocally`.
-- The source phrase “the ring `O_X(U)` is Noetherian and regular” is therefore recorded through
-- `IsRegularRing (Γ(X, U))`, whose owner already includes Noetherianity.

variable (X : Scheme.{u})

/-- Definition 28.9.1: a scheme `X` is regular, or nonsingular, if every point of `X` admits an
affine open neighborhood whose ring of sections is regular (hence Noetherian). -/
@[stacks 01V7]
abbrev Regular (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsRegularRing A)

/-- On a regular scheme, every point lies in an affine open neighborhood with regular coordinate
ring. -/
theorem exists_affineOpen_regularRing (X : Scheme.{u}) [Regular X] (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsRegularRing (Γ(X, (U : X.Opens))) := by
  exact HasRingPropertyLocally.exists_affineOpen X (fun A : CommRingCat.{u} ↦ IsRegularRing A) x

/-- Unfold `Regular` into the affine-open neighborhood condition on points. -/
theorem regular_iff (X : Scheme.{u}) :
    Regular X ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsRegularRing (Γ(X, (U : X.Opens))) := by
  exact hasRingPropertyLocally_iff X (fun A : CommRingCat.{u} ↦ IsRegularRing A)

/-- A regular scheme is locally Noetherian. -/
noncomputable instance instIsLocallyNoetherianOfRegular [Regular X] : IsLocallyNoetherian X := by
  let hX : X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsRegularRing A) :=
    inferInstance
  let U : X → X.affineOpens := fun x ↦ Classical.choose (hX.out x)
  have hU_mem : ∀ x : X, x ∈ ((U x : X.affineOpens) : X.Opens) := fun x ↦
    (Classical.choose_spec (hX.out x)).1
  have hU_regular : ∀ x : X, IsRegularRing (Γ(X, ((U x : X.affineOpens) : X.Opens))) :=
    fun x ↦ (Classical.choose_spec (hX.out x)).2
  have hU_cover : ⨆ x, ((U x : X.affineOpens) : X.Opens) = ⊤ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hU_mem x⟩
  have hU_noetherian :
      ∀ x, IsNoetherianRing ↑Γ(X, ((U x : X.affineOpens) : X.Opens)) := by
    intro x
    letI : IsRegularRing (Γ(X, ((U x : X.affineOpens) : X.Opens))) := hU_regular x
    infer_instance
  exact AlgebraicGeometry.isLocallyNoetherian_of_affine_cover hU_cover hU_noetherian

/-- The stalk of a regular scheme at any point is a regular local ring. -/
theorem isRegularLocalRing_stalk (X : Scheme.{u}) [Regular X] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
