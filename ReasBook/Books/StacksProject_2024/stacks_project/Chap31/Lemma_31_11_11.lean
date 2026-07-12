import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap28.Lemma_28_9_2
import StacksProject_2024.Chap31.Definition_31_11_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the ring-level owners `Module.IsTorsionFree` and
-- PID freeness criteria, while local Chapter 31 precedent fixes the scheme-module owner
-- `Scheme.Modules.IsTorsionFree`, the regularity owner `Scheme.Regular`, and the Chapter 17
-- finite-locally-free owner `SheafOfModules.IsFiniteLocallyFree`. As in nearby Chapter 31 files,
-- the source-facing stalkwise regular-local formulation is kept as a bridge to the regular-scheme
-- owner-level statement.

section

variable {X : Scheme.{u}} [IsIntegral X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- In this file, coherent modules are used through the Chapter 17 finite-locally-free owner,
which is stated for quasi-coherent modules. -/
local instance instIsQuasicoherentOfIsCoherentForLemma311111 : ℱ.IsQuasicoherent := by
  let _ : ℱ.IsFinitePresentation :=
    (isCoherent_iff_isFinitePresentation (X := X) ℱ).mp inferInstance
  infer_instance

/-- Lemma 31.11.11: let `X` be an integral regular scheme of dimension `≤ 1`, and let `ℱ` be a
coherent `\mathcal O_X`-module. Then the following are equivalent: `ℱ` is torsion free, and `ℱ`
is finite locally free. The regularity hypothesis is encoded by the project owner
`Scheme.Regular X`, and the dimension hypothesis by `topologicalKrullDim X ≤ 1`. -/
@[stacks 0B32]
theorem isTorsionFree_iff_isFiniteLocallyFree_of_regular_and_topologicalKrullDim_le_one
    [Scheme.Regular X] (hdim : topologicalKrullDim X ≤ 1) :
    IsTorsionFree ℱ ↔ SheafOfModules.IsFiniteLocallyFree ℱ := by
  sorry

/-- Stalkwise regular-locality is a source-faithful bridge to the regular-scheme form of
Lemma 31.11.11. -/
theorem isTorsionFree_iff_isFiniteLocallyFree_of_regular_stalk_and_topologicalKrullDim_le_one
    [IsLocallyNoetherian X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X ≤ 1) :
    IsTorsionFree ℱ ↔ SheafOfModules.IsFiniteLocallyFree ℱ := by
  let hX : Scheme.Regular X :=
    (Scheme.regular_iff_isLocallyNoetherian_and_forall_isRegularLocalRing_stalk X).2
      ⟨inferInstance, hreg⟩
  letI : Scheme.Regular X := hX
  exact isTorsionFree_iff_isFiniteLocallyFree_of_regular_and_topologicalKrullDim_le_one ℱ hdim

end

end AlgebraicGeometry.Scheme.Modules
