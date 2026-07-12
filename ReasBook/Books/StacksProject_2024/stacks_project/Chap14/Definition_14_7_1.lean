import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

section

variable {C : Type u} [Category.{v} C]
variable {U V W : SimplicialObject C}
variable (a : V ⟶ U) (b : W ⟶ U)
variable [∀ n : SimplexCategoryᵒᵖ, HasPullback (a.app n) (b.app n)]

/- Domain-style sampling for Definition 14.7.1:
- primary domain: pullbacks in the functor category `SimplicialObject C`;
- sampled owner declarations:
  `CategoryTheory.Limits.functorCategoryHasLimit`,
  `CategoryTheory.Limits.diagramIsoCospan`,
  `CategoryTheory.Limits.evaluation_preservesLimit`,
  `CategoryTheory.Limits.PreservesPullback.iso`;
- best owner abstraction:
  - `source-facing`: degreewise fibre products of simplicial objects;
  - `core/canonical`: the pullback object `pullback a b` in the functor category;
  - `bridge/view`: the induced `HasPullback a b` instance from the degreewise pullback hypotheses.
- primitive data: only the morphisms `a : V ⟶ U`, `b : W ⟶ U` and the degreewise assumptions
  `[∀ n, HasPullback (a.app n) (b.app n)]`;
- derived API: the simplicial pullback instance, the object `pullback a b`, its projections, and
  the canonical degreewise comparison `PreservesPullback.iso ((evaluation _ _).obj n) a b` with
  its projection identities.

Source/core/bridge triage:
- `source-facing`: the textbook assertion that degreewise fibre products assemble into a fibre
  product simplicial object;
- `core/canonical`: mathlib's pullback owner in the functor category;
- `bridge/view`: the passage from degreewise `HasPullback` hypotheses to `HasPullback a b`.

This item is not a new owner: the correct refinement is to expose the bridge instance and reuse the
canonical pullback object and evaluation-functor comparison API directly. The stronger
functor-category theorem `pullbackObjIso` would require the global assumption `HasPullbacks C`, so
the main public surface here stays at the source-faithful
`PreservesPullback.iso ((evaluation _ _).obj n) a b`. -/

namespace CategoryTheory.SimplicialObject

local instance pointwiseCospanHasLimit (n : SimplexCategoryᵒᵖ) :
    HasLimit ((cospan a b).flip.obj n) := by
  let e : ((cospan a b).flip.obj n) ≅ cospan (a.app n) (b.app n) := diagramIsoCospan _
  letI : HasPullback (a.app n) (b.app n) := inferInstance
  exact hasLimit_of_iso e.symm

noncomputable instance : HasPullback a b := by
  change HasLimit (cospan a b)
  infer_instance

/- Definition 14.7.1: assuming the degreewise fibre products `V_n ×_{U_n} W_n` exist, the fibre
product of simplicial objects `V` and `W` over `U` is the canonical pullback object `pullback a b`
in `SimplicialObject C`. The only additional chapter-level content here is the instance upgrading
the degreewise pullback hypotheses to `HasPullback a b`; the pullback object, its projections, and
the degreewise comparison isomorphisms are the existing functor-category owners. -/
#check (pullback a b : SimplicialObject C)

/- The canonical projection from the simplicial fibre product to `V` is `pullback.fst a b`. -/
#check (pullback.fst a b : pullback a b ⟶ V)

/- The canonical projection from the simplicial fibre product to `W` is `pullback.snd a b`. -/
#check (pullback.snd a b : pullback a b ⟶ W)

variable (n : SimplexCategoryᵒᵖ)

local instance evaluationPreservesCospanLimit :
    PreservesLimit (cospan a b) ((evaluation _ _).obj n) := by
  infer_instance

local instance evaluationHasPullback :
    HasPullback (((evaluation _ _).obj n).map a) (((evaluation _ _).obj n).map b) := by
  simpa using (inferInstance : HasPullback (a.app n) (b.app n))

/- Evaluating the simplicial pullback at `Δ` is the canonical pullback-comparison isomorphism for
the evaluation functor, namely `PreservesPullback.iso ((evaluation _ _).obj n) a b`. -/
#check (PreservesPullback.iso ((evaluation _ _).obj n) a b :
  (pullback a b).obj n ≅ pullback (a.app n) (b.app n))

/- Its projection identities are the canonical lemmas `PreservesPullback.iso_hom_fst` and
`PreservesPullback.iso_hom_snd`. -/
#check (PreservesPullback.iso_hom_fst ((evaluation _ _).obj n) a b :
  (PreservesPullback.iso ((evaluation _ _).obj n) a b).hom ≫
      pullback.fst (a.app n) (b.app n) =
    (pullback.fst a b).app n)

#check (PreservesPullback.iso_hom_snd ((evaluation _ _).obj n) a b :
  (PreservesPullback.iso ((evaluation _ _).obj n) a b).hom ≫
      pullback.snd (a.app n) (b.app n) =
    (pullback.snd a b).app n)

end CategoryTheory.SimplicialObject

end
