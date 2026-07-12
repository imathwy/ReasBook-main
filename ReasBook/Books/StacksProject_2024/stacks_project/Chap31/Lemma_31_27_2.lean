import Mathlib
import StacksProject_2024.Chap31.Definition_31_23_3
import StacksProject_2024.Chap31.Definition_31_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]

attribute [local instance] Classical.propDecidable

local notation "ModX" => SheafOfModules X.ringCatSheaf
-- Semantic recall:
-- * `lean_leansearch` surfaced only analytic meromorphic-divisor owners, so the scheme-side
--   Stacks statement must stay on the local Chapter 31 owners already present in this project.
-- * local precedent in `Lemma_31_26_4` uses `LocallyFinite` families indexed by prime divisors,
--   while the proof of the current Stacks item reduces both source sets to prime divisors whose
--   generic points lie in the complement of an open on which the section generates `\mathcal L`.
-- * `Definition_31_27_1` records `ord_{Z,\mathcal L}(s)` through
--   `primeDivisorOrderOfVanishing`.

/-- Lemma 31.27.2 (1): let `X` be a locally Noetherian integral scheme, let `\mathcal L` be an
invertible `\mathcal O_X`-module, and let `s ∈ \mathcal K_X(\mathcal L)` be a regular meromorphic
section. If `U` is an open subset on which `s` is represented by a section generating
`\mathcal L`, then the prime divisors whose generic points lie outside `U` form a locally finite
family in `X`; this is the open-complement family controlling the first source set. -/
@[stacks 02SG]
theorem locallyFinite_primeDivisors_genericPoint_not_mem_open
    (ℒ : ModX)
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (U : Opens X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if Z.genericPoint ∈ (U : Set X) then
        (∅ : Set X)
      else
        (Z.support : Set X) := sorry

/-- Lemma 31.27.2 (2): with the same hypotheses, the family of prime divisors `Z \subset X` with
`\operatorname{ord}_{Z, \mathcal L}(s) \ne 0` is locally finite in `X`. In the current project,
the order along `Z` is recorded by chosen local presentation data
`PrimeDivisorOrderPresentation ℒ s Z` as in Definition `31.27.1`. -/
@[stacks 02SG]
theorem locallyFinite_primeDivisors_primeDivisorOrderOfVanishing_ne_zero
    (ℒ : ModX)
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if primeDivisorOrderOfVanishing s Z (data Z) = 0 then
        (∅ : Set X)
      else
        (Z.support : Set X) := sorry

end AlgebraicGeometry.Scheme
