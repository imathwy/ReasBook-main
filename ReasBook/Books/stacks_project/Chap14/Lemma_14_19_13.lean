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
variable {U V W : SimplicialObject.Truncated C n}
variable (f : U ⟶ V) (g : W ⟶ V)
variable [HasPullback f g]

/- Domain-style sampling for Lemma 14.19.13:
- primary domain: pullback-comparison isomorphisms for right adjoints in simplicial-object
  truncation/coskeleton theory;
- sampled owner API:
  `Definition_14_7_1`'s use of `PreservesPullback.iso ((evaluation _ _).obj n) a b`,
  `coskAdj`,
  `PreservesPullback.iso`,
  `PreservesPullback.iso_hom`;
- best owner abstraction: the canonical comparison isomorphism is
  `PreservesPullback.iso (Truncated.cosk n) f g`, whose hom is definitionally
  `pullbackComparison (Truncated.cosk n) f g`;
- source/core/bridge triage:
  `source-facing`: the map `cosk_n (U ×[V] W) ⟶ cosk_n U ×[cosk_n V] cosk_n W`;
  `core/canonical`: `PreservesPullback.iso (Truncated.cosk n) f g`;
  `bridge/view`: the right-adjoint structure on `Truncated.cosk n` coming from `coskAdj n`.

Primitive data are only the truncated simplicial objects, the morphisms `f`, `g`, and the source
pullback assumption `[HasPullback f g]`. The target pullback is derived API from right-adjoint
preservation via `hasPullback_of_preservesPullback`, so this file should recall the canonical owner
rather than keep a parallel theorem with the same content. -/
noncomputable local instance :
    ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C)).IsRightAdjoint :=
  by
  simpa using (coskAdj n).isRightAdjoint

attribute [local instance] hasPullback_of_preservesPullback

recall PreservesPullback.iso
recall PreservesPullback.iso_hom

/- Lemma 14.19.13: if the pullback `U ×[V] W` exists in `n`-truncated simplicial objects, then the
canonical comparison map to `cosk_n U ×[cosk_n V] cosk_n W` is an isomorphism. The target
pullback exists canonically because the right adjoint `Truncated.cosk n` preserves pullbacks, so
the owner object is the standard pullback-comparison isomorphism and the source-facing comparison
map is its canonical hom. -/
#check (PreservesPullback.iso (Truncated.cosk n) f g :
  (Truncated.cosk n).obj (pullback f g) ≅
    pullback ((Truncated.cosk n).map f) ((Truncated.cosk n).map g))

#check (PreservesPullback.iso_hom (Truncated.cosk n) f g :
  (PreservesPullback.iso (Truncated.cosk n) f g).hom =
    pullbackComparison (Truncated.cosk n) f g)

end CategoryTheory
