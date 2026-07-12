import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {n : ℕ}
variable [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/- Domain-style sampling for Lemma 14.19.12:
- primary domain: binary-product comparison morphisms for right adjoints in simplicial-object
  truncation/coskeleton theory;
- sampled owner API:
  `coskAdj`,
  `Adjunction.isRightAdjoint`,
  `PreservesLimitPair.iso`,
  `PreservesLimitPair.iso_hom`;
- best owner abstraction: the canonical comparison isomorphism is the binary-product owner
  `PreservesLimitPair.iso (Truncated.cosk n) U V`, and the source-facing comparison morphism is its
  hom, identified by `PreservesLimitPair.iso_hom`;
- source/core/bridge triage:
  `source-facing`: the map `cosk_n (U × V) ⟶ cosk_n U × cosk_n V`;
  `core/canonical`: `PreservesLimitPair.iso (Truncated.cosk n) U V`;
  `bridge/view`: the right-adjoint structure on `Truncated.cosk n` coming from `coskAdj n`.

Primitive data are only the truncated simplicial objects `U`, `V`, their binary product, and the
right Kan extension hypotheses defining `Truncated.cosk n`. The comparison map itself is derived
API from the owner isomorphism `PreservesLimitPair.iso`, so this item should recall that owner and
its canonical hom description rather than introduce a parallel local theorem. -/
noncomputable local instance :
    ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C)).IsRightAdjoint :=
  by
    simpa using (coskAdj n).isRightAdjoint

variable (U V : SimplicialObject.Truncated C n)
variable [HasBinaryProduct U V]

recall PreservesLimitPair.iso
recall PreservesLimitPair.iso_hom

/- Lemma 14.19.12: if the binary product `U × V` exists in `n`-truncated simplicial objects, then
the canonical comparison map `cosk_n (U × V) ⟶ cosk_n U × cosk_n V` is an isomorphism. The owner
object is the standard binary-product comparison isomorphism for the right adjoint
`Truncated.cosk n`, whose hom is definitionally `prodComparison (Truncated.cosk n) U V`. -/
#check PreservesLimitPair.iso (Truncated.cosk n) U V

end CategoryTheory
