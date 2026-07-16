import Mathlib
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap30.Lemma_30_9_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

-- Semantic recall: `CategoryTheory.IsNoetherianObject` is the canonical owner for stabilization
-- of monotone subobject chains. The source only quantifies over quasi-coherent submodules, and
-- Chapter 30 already upgrades such submodules of a coherent module on a Noetherian scheme to
-- coherent ones in `isCoherent_subobject_of_isQuasicoherent`. This file therefore exposes the
-- canonical noetherian-object owner together with the source-facing quasi-coherent chain
-- stabilization companions.

/-- A coherent `\mathcal O_X`-module on a Noetherian scheme is a Noetherian object of
`X.Modules`. This is the canonical owner behind Lemma 30.10.1. -/
theorem isNoetherianObject_of_isCoherent : IsNoetherianObject ℱ := by
  sorry

/-- Lemma 30.10.1: let `X` be a Noetherian scheme and let `ℱ` be a coherent
`\mathcal O_X`-module. Then every ascending chain of quasi-coherent submodules of `ℱ`
stabilizes. -/
theorem quasiCoherentSubobject_monotone_stabilizes
    (f : ℕ →o Subobject ℱ)
    (hf_qc : ∀ n : ℕ, (((f n : Subobject ℱ) : X.Modules)).IsQuasicoherent) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m := by
  sorry

/-- Any monotone chain valued in the ordered subtype of quasi-coherent subobjects of a coherent
module on a Noetherian scheme stabilizes. -/
theorem quasiCoherentSubobjectSubtype_monotone_stabilizes
    (f : ℕ →o { G : Subobject ℱ // ((G : X.Modules)).IsQuasicoherent }) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m := by
  sorry

end AlgebraicGeometry.Scheme.Modules
