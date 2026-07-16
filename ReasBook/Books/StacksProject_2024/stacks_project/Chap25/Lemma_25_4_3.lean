import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
import StacksProject_2024.stacks_project.Chap25.Definition_25_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open AlgebraicTopology
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open scoped Simplicial

-- Semantic search note: `lean_leansearch` recalled mathlib's owner predicates
-- `SimplicialObject.IsCoskeletal` and `Presheaf.IsLocallySurjective`; this item keeps the source
-- theorem in its original coskeleton-unit form and provides the `IsCoskeletal` version as the
-- canonical companion.

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))}

/-- Lemma 25.4.3: if `f : L ⟶ K` is degreewise an isomorphism in simplicial degrees `< n`, is
locally surjective in simplicial degree `n`, and the canonical unit maps
`L ⟶ \operatorname{cosk}_n \operatorname{sk}_n L` and
`K ⟶ \operatorname{cosk}_n \operatorname{sk}_n K` are isomorphisms, then the induced map
`H_i(f)` on homology sheaves is an isomorphism. -/
@[stacks 01GD]
theorem simplicialPresheafHomologyMap_isIso_of_isIso_below_of_locallySurjective_of_coskUnitIsIso
    (f : L ⟶ K) (n i : ℕ)
    (hbelow : ∀ j < n, IsIso (f.app (op ⦋j⦌)))
    (hSurj : Presheaf.IsLocallySurjective J (f.app (op ⦋n⦌)))
    (hL : IsIso ((coskAdj n).unit.app L))
    (hK : IsIso ((coskAdj n).unit.app K)) :
    IsIso (simplicialPresheafHomologyMap J f i) := sorry

/-- Canonical companion to Lemma 25.4.3: the source hypotheses on the two coskeleton-unit maps may
be supplied through the equivalent canonical predicate `IsCoskeletal`. -/
theorem simplicialPresheafHomologyMap_isIso_of_isIso_below_of_locallySurjective_of_coskeletal
    (f : L ⟶ K) (n i : ℕ)
    (hbelow : ∀ j < n, IsIso (f.app (op ⦋j⦌)))
    (hSurj : Presheaf.IsLocallySurjective J (f.app (op ⦋n⦌)))
    (hL : L.IsCoskeletal n) (hK : K.IsCoskeletal n) :
    IsIso (simplicialPresheafHomologyMap J f i) := by
  have hL' : IsIso ((coskAdj n).unit.app L) := (isCoskeletal_iff_isIso L n).1 hL
  have hK' : IsIso ((coskAdj n).unit.app K) := (isCoskeletal_iff_isIso K n).1 hK
  exact simplicialPresheafHomologyMap_isIso_of_isIso_below_of_locallySurjective_of_coskUnitIsIso
    J f n i hbelow hSurj hL' hK'

end

end CategoryTheory
