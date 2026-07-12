import Mathlib
import StacksProject_2024.Chap28.Definition_28_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-side owner
-- `AlgebraicGeometry.IsLocallyNoetherian`. At this point in Chapter 28 the source-facing Nagata
-- hypothesis is the affine-local predicate `Scheme.Nagata` from Definition `28.13.1`, so this
-- item is best stated as the thin bridge from that existing owner to `IsLocallyNoetherian`.

/-- Lemma 28.13.3: a Nagata scheme is locally Noetherian. -/
@[stacks 033U]
theorem isLocallyNoetherian_of_nagata (X : Scheme.{u}) (hX : Nagata X) :
    IsLocallyNoetherian X := by
  let U : X → X.affineOpens := fun x ↦ Classical.choose (hX.out x)
  let S : X → X.affineOpens := fun x ↦ U x
  have hU_mem : ∀ x : X, x ∈ ((U x : X.affineOpens) : X.Opens) := fun x ↦
    (Classical.choose_spec (hX.out x)).1
  have hU_nagata : ∀ x : X, NagataRing (Γ(X, ((U x : X.affineOpens) : X.Opens))) := fun x ↦
    (Classical.choose_spec (hX.out x)).2
  have hS : ⨆ x, ((S x : X.affineOpens) : X.Opens) = ⊤ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hU_mem x⟩
  have hS' : ∀ x, IsNoetherianRing ↑Γ(X, ((S x : X.affineOpens) : X.Opens)) := by
    intro x
    letI : NagataRing (Γ(X, ((U x : X.affineOpens) : X.Opens))) := hU_nagata x
    infer_instance
  exact AlgebraicGeometry.isLocallyNoetherian_of_affine_cover hS hS'

/-- A Nagata scheme is locally Noetherian. -/
theorem isLocallyNoetherian_of_isNagata (X : Scheme.{u}) (hX : Nagata X) :
    IsLocallyNoetherian X :=
  isLocallyNoetherian_of_nagata X hX

end AlgebraicGeometry.Scheme
