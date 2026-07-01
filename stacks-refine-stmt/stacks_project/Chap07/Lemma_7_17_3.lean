import Mathlib
import stacks_project.Chap07.Definition_7_17_1
import stacks_project.Chap07.Definition_7_17_4
import stacks_project.Chap07.Lemma_7_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open CategoryTheory.SemiRepresentableFamily.Over

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology

open scoped SheafifiedRepresentable

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-
Source/core/bridge triage for 7.17.3:
- source-facing predicate on the site side: `J.QuasiCompactObject U`
- core/canonical predicate on the sheaf side: `Sheaf.IsQuasiCompactObject`
- bridge/view object: `J.sheafifiedRepresentable U`
-/
-- Proof sketch: for `(1) → (2)`, turn a locally surjective coproduct map to `h_U^#` into a
-- covering family over `U` and then refine it to finitely many summands. For `(2) → (1)`, start
-- from a covering family of `U`, use the canonical locally surjective cover map
-- `J.sheafifiedRepresentableCoverMap`, apply the owner field
-- `Sheaf.IsQuasiCompactObject.finite_subcoproduct`, and convert the resulting finite locally
-- surjective coproduct map of sheafified representables back to a covering sieve on `U`.
/-- Lemma 7.17.3: an object `U` of a site `(C, J)` is quasi-compact if and only if the sheafified
representable `h_U^#` is a quasi-compact object of the topos `Sh(C, J)`. -/
theorem quasiCompactObject_iff_isQuasiCompactObject_sheafifiedRepresentable
    (U : C) :
    J.QuasiCompactObject U ↔ (h[U]^#[J]).IsQuasiCompactObject := by
  constructor
  · intro hU
    sorry
  · intro hU
    sorry

end CategoryTheory.GrothendieckTopology
