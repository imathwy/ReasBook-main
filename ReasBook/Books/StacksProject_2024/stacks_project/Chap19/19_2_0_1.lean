import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

universe v u

section

variable {J : Type v} [SmallCategory J]
variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for 19.2.0.1:
- primary domain: generic colimit comparison morphisms for `Type`-valued functors, specialized to
  represented Hom-functors `Hom(A, -) = coyoneda.obj (op A)`;
- sampled owner declarations:
  `colimit.post`,
  `colimit.ι_post`,
  `Functor.mapCocone`,
  `PreservesColimit`;
- best owner abstraction: the comparison map itself is the canonical owner
  `colimit.post B (coyoneda.obj (op A))`;
- primitive data: an object `A : C`, a diagram `B : J ⥤ C`, and a colimit of `B`;
- derived API: the stagewise formula obtained by evaluating `colimit.ι_post` on a morphism
  `φ : A ⟶ B.obj j`.

Source/core/bridge triage:
- `source-facing`: the Stacks comparison map
  `colim_j Hom_C(A, B_j) → Hom_C(A, colim_j B_j)`;
- `core/canonical`: `colimit.post`;
- `bridge/view`: the pointwise stage formula below.

The deleted local cocone and descendant were only implementation-level redefinitions of
`Functor.mapCocone (colimit.cocone B)` and `colimit.post`.
-/

variable (A : C) (B : J ⥤ C) [HasColimit B]

/- 19.2.0.1: the canonical comparison map from the colimit of the Hom-sets `Mor_C(A, B_j)` to the
Hom-set `Mor_C(A, colim B_j)` is exactly the specialization
`colimit.post B (coyoneda.obj (op A))` of the generic colimit comparison morphism. -/
#check
  (colimit.post B (coyoneda.obj (op A)) :
    colimit (B ⋙ coyoneda.obj (op A)) ⟶ (A ⟶ colimit B))

/-- Evaluating the canonical comparison map on the coprojection represented by
`φ : A ⟶ B.obj j` yields the composite `A ⟶ B.obj j ⟶ colimit B`. -/
theorem colimit_post_coyoneda_ι_app (A : C) (B : J ⥤ C) [HasColimit B] (j : J)
    (φ : A ⟶ B.obj j) :
    (colimit.ι (B ⋙ coyoneda.obj (op A)) j ≫ colimit.post B (coyoneda.obj (op A))) φ =
      φ ≫ colimit.ι B j := by
  simpa using congrFun (colimit.ι_post B (coyoneda.obj (op A)) j) φ

end
