import Mathlib
import StacksProject_2024.Chap10.Definition_10_88_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace Module

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A directed colimit presentation of an `R`-module by a Mittag-Leffler directed system. -/
structure MittagLefflerPresentation (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] where
  index : Type v
  indexPreorder : Preorder index
  indexNonempty : Nonempty index
  indexDirected : IsDirectedOrder index
  diagram : index ⥤ ModuleCat R
  presentation_isMittagLeffler : @IsMittagLefflerDirectedSystem R _ index indexPreorder
    indexNonempty indexDirected diagram
  colimitIso : Nonempty (colimit diagram ≅ ModuleCat.of R M)

/-- Definition 10.88.7: an `R`-module `M` is Mittag-Leffler when it is the colimit of a directed
system satisfying `IsMittagLefflerDirectedSystem`. -/
class MittagLeffler (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] where
  exists_presentation : Nonempty (MittagLefflerPresentation R M)

-- Proof sketch: take the constant one-object directed system on `M`. Finite presentation gives the
-- stagewise hypothesis, the colimit is `M` itself, and the unique transition maps satisfy the
-- factorization condition tautologically.
/-- A finitely presented module is Mittag-Leffler. -/
instance instMittagLefflerOfFinitePresentation
    [Module.FinitePresentation R M] : MittagLeffler R M := sorry

end

end Module
