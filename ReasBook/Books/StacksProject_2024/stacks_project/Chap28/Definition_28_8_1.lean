import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap28.Definition_28_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the affine-open scheme owners `Scheme.affineOpens` and
-- `IsLocallyNoetherian.component_noetherian`. In this project, Definition `28.4.2` already
-- packages "a ring property holds locally on a scheme" as `HasRingPropertyLocally`, and the
-- source condition here is exactly its specialization to `CohenMacaulayRing`.

variable (X : Scheme.{u})

/- Definition 28.8.1: a scheme `X` is Cohen-Macaulay if every point of `X` admits an affine open
neighborhood whose ring of sections is Cohen-Macaulay, hence in particular Noetherian. The
canonical project owner is the specialization
`X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)`. -/
#check (X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) : Prop)

/-- On a scheme satisfying the Cohen-Macaulay affine-local condition, every point lies in an
affine open neighborhood with Cohen-Macaulay coordinate ring. -/
theorem exists_affineOpen_cohenMacaulayRing
    [X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)] (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ CohenMacaulayRing (Γ(X, (U : X.Opens))) := by
  exact HasRingPropertyLocally.exists_affineOpen X
    (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) x

/-- Unfold the Cohen-Macaulay affine-local condition into the affine-open neighborhood condition
on points. -/
theorem hasRingPropertyLocally_cohenMacaulayRing_iff :
    X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) ↔
      ∀ x : X,
        ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ CohenMacaulayRing (Γ(X, (U : X.Opens))) := by
  exact hasRingPropertyLocally_iff X (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)

/-- A scheme satisfying the Cohen-Macaulay affine-local condition is locally Noetherian. -/
instance instIsLocallyNoetherianOfHasRingPropertyLocallyCohenMacaulayRing
    [X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)] :
    IsLocallyNoetherian X := by
  let hX : X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) :=
    inferInstance
  let U : X → X.affineOpens := fun x ↦ Classical.choose (hX.out x)
  have hU_mem : ∀ x : X, x ∈ ((U x : X.affineOpens) : X.Opens) := fun x ↦
    (Classical.choose_spec (hX.out x)).1
  have hU_cohenMacaulay : ∀ x : X, CohenMacaulayRing (Γ(X, ((U x : X.affineOpens) : X.Opens))) :=
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
    letI : CohenMacaulayRing (Γ(X, ((U x : X.affineOpens) : X.Opens))) := hU_cohenMacaulay x
    infer_instance
  exact AlgebraicGeometry.isLocallyNoetherian_of_affine_cover hU_cover hU_noetherian

end AlgebraicGeometry.Scheme
