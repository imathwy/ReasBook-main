import Mathlib
import stacks_project.Chap04.Definition_4_40_1
import stacks_project.Chap04.Lemma_4_39_6
import stacks_project.Chap04.Lemma_4_40_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Functor BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace FibredInGroupoidsOver

/- Domain-style sampling for Lemma 4.40.2:
- primary domain: representable categories fibred in groupoids over a fixed base and their
  comparison with fibred-in-setoids models and representable presheaves;
- inspected owner-level declarations:
  `FibredInGroupoidsOver.IsRepresentable`,
  `FibredInGroupoidsOver.isRepresentable_iff_exists_presentation`,
  `Functor.fiberIsoClassPresheaf`,
  `FibredInGroupoidsOver.overMap`,
  `FibredInGroupoidsOver.mor_isoClasses_equiv_hom`,
  `RepresentableBy.uniqueUpToIso`;
- best owner abstraction: the bundled object `FibredInGroupoidsOver C`, with presentation data
  expressed by morphisms in that owner category rather than by raw based-functor types. The
  bundled object `FibredInGroupoidsOver.ofFunctor p` is already universe-general, so the source-
  facing statement should use its owner predicate directly rather than a parallel wrapper;
- primitive data: the bundled owner object `P : FibredInGroupoidsOver C` and the chosen
  presentations by slice projections;
- derived API: the representability criterion via the iso-class presheaf and the uniqueness of the
  representing object via `Functor.RepresentableBy` on the iso-class presheaf.

Source/core/bridge triage:
- `source-facing`: the representability criterion and uniqueness of representing objects;
- `core/canonical`: `FibredInGroupoidsOver.IsRepresentable`, `Functor.IsRepresentable`,
  `Functor.fiberIsoClassPresheaf`, and `RepresentableBy.uniqueUpToIso`;
- `bridge/view`: the presentation morphisms over `C`, expressed in the owner category
  `FibredInGroupoidsOver C`, and the canonical slice comparison `overMap`. -/

-- Proof sketch: if `p` is representable, choose an equivalence with a slice category `C/X`; then
-- Lemma `4.39.5` gives the setoid condition, while Lemma `4.38.6` together with Example `4.38.7`
-- identifies the iso-class presheaf with the representable presheaf `h_X`. Conversely, if `p` is
-- fibred in setoids and this presheaf is representable, apply Lemma `4.39.5` to replace `p` by a
-- fibred-in-sets model and then use Lemma `4.38.6` to identify that model with a slice category.
/-- Lemma 4.40.2 (1): a category fibred in groupoids over `C` is representable if and only if its
projection is fibred in setoids and the presheaf of isomorphism classes in its fibers is
representable. -/
private theorem isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_representable_aux
    (P : FibredInGroupoidsOver C) :
    P.IsRepresentable ↔
      IsFibredInSetoids P.p ∧ (fiberIsoClassPresheaf P.p).IsRepresentable := sorry

end FibredInGroupoidsOver

end CategoryTheory

namespace CategoryTheory

open BasedFunctor
open FibredInGroupoidsMor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FibredInGroupoidsOver

open Functor Opposite

variable {P : FibredInGroupoidsOver C}
variable {X X' : C}

/-- Owner-level reformulation of Lemma 4.40.2 (1), re-exported on `FibredInGroupoidsOver` from the
statement-pipeline entry declaration. -/
theorem isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable
    (P : FibredInGroupoidsOver C) :
    P.IsRepresentable ↔
      IsFibredInSetoids P.p ∧ (fiberIsoClassPresheaf P.p).IsRepresentable := by
  simpa using isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_representable_aux P

private noncomputable def fiberIsoClassPresheaf_point_of_equivalence
    (e : P ≌ ofFunctor (Over.forget X)) :
    (fiberIsoClassPresheaf P.p).obj (op X) :=
  let hx : P.p.obj ((FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X))) = X := by
    simpa using
      (show
          P.p.obj ((FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X))) =
            (Over.forget X).obj (Over.mk (𝟙 X)) from
          congrArg
            (fun F : Over X ⥤ C ↦ F.obj (Over.mk (𝟙 X)))
            (FibredInGroupoidsMor.comm e.inv))
  let x : P.p.Fiber X :=
    ⟨(FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X)), hx⟩
  Quotient.mk'' x

-- Proof sketch: transport `P` to the canonical fibred-in-sets model of its iso-class presheaf
-- using Lemma `4.39.5`, then compare that model with the slice model `C/X` coming from `e` via
-- Lemma `4.38.6` and Example `4.38.7`. The image of `Over.mk (𝟙 X)` under `e.inv` gives the
-- universal element in the fiber over `X`.
private theorem fiberIsoClassPresheaf_isRepresentedBy_of_equivalence
    (e : P ≌ ofFunctor (Over.forget X)) :
    (fiberIsoClassPresheaf P.p).IsRepresentedBy
      (fiberIsoClassPresheaf_point_of_equivalence e) := by
  sorry

-- Proof sketch: a presentation morphism over `C` upgrades to a bicategorical equivalence by
-- `FibredInGroupoidsMor.exists_equivalence`; the corresponding represented object of the iso-class
-- presheaf is then obtained from the equivalence-level construction above.
private noncomputable def presentation_representableBy
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (hj : j.IsEquivalenceOverBase) :
    (fiberIsoClassPresheaf P.p).RepresentableBy X := by
  classical
  let e := Classical.choose (FibredInGroupoidsMor.exists_equivalence j hj)
  have he : e.hom = j := Classical.choose_spec (FibredInGroupoidsMor.exists_equivalence j hj)
  simpa [he] using (fiberIsoClassPresheaf_isRepresentedBy_of_equivalence e).representableBy

/-- The canonical comparison morphism on the representing base objects attached to two slice
presentations of the same represented fibred category in groupoids. It is extracted from the
identity morphism of `P` via the owner equivalence `mor_isoClasses_equiv_hom`. -/
noncomputable def presentationComparisonHom
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    X ⟶ X' :=
  mor_isoClasses_equiv_hom j j' hj hj' (Quotient.mk'' (𝟙 P))

/-- Lemma 4.40.2 (2): if `P : FibredInGroupoidsOver C` is represented over `C` both by `C/X`
and by `C/X'`, then the identity morphism of `P` induces the canonical comparison morphism
`X ⟶ X'` between the representing objects attached to the two presentations. Equivalently, the two
presentation morphisms differ only by whiskering with `overMap` on this comparison morphism, up to
`2`-isomorphism over `C`. This is the morphism-level bridge behind the pair-level uniqueness
statement below. -/
theorem presentationComparisonHom_induces
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    FibredInGroupoidsMor.InducesHom
      (𝟙 P) j j' (presentationComparisonHom j j' hj hj') := by
  exact
    (inducesHom_iff_mor_isoClasses_equiv_hom_eq j j' hj hj' (𝟙 P)
      (presentationComparisonHom j j' hj hj')).2 rfl

/-- The canonical isomorphism between the representing objects of two slice presentations of the
same represented fibred category in groupoids. This is the owner-level uniqueness isomorphism for
the represented iso-class presheaf, expressed through `RepresentableBy.uniqueUpToIso`. -/
private noncomputable def presentationIsoWitness
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    X ≅ X' :=
  RepresentableBy.uniqueUpToIso
    (presentation_representableBy j hj)
    (presentation_representableBy j' hj')

/-- The private witness isomorphism between two representing objects has underlying morphism equal
to the canonical comparison morphism induced from the identity presentation of `P`. -/
@[simp] private theorem presentationIsoWitness_hom
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    (presentationIsoWitness j j' hj hj').hom =
      presentationComparisonHom j j' hj hj' := by
  sorry

/-- The canonical comparison morphism between the two representing objects of slice presentations
is an isomorphism. The proof uses the private representability witness, while the public statement
is expressed entirely in terms of the canonical comparison morphism. -/
theorem presentationComparisonHom_isIso
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    IsIso (presentationComparisonHom j j' hj hj') := by
  simpa [presentationIsoWitness_hom j j' hj hj'] using
    (presentationIsoWitness j j' hj hj').isIso_hom

/-- The canonical isomorphism between the representing objects of two slice presentations of the
same represented fibred category in groupoids. It is the `asIso` of the canonical comparison
morphism `presentationComparisonHom`. -/
noncomputable def presentationIso
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    X ≅ X' :=
  letI := presentationComparisonHom_isIso j j' hj hj'
  asIso (presentationComparisonHom j j' hj hj')

/-- The canonical uniqueness isomorphism between two representing objects has underlying morphism
equal to the canonical comparison morphism induced from the identity presentation of `P`. -/
@[simp] theorem presentationIso_hom
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    (presentationIso j j' hj hj').hom =
      presentationComparisonHom j j' hj hj' := by
  simp [presentationIso]

/-- Lemma 4.40.2 (3): if `P : FibredInGroupoidsOver C` is represented over `C` both by `C/X`
and by `C/X'`, then the representing pair is unique up to isomorphism: the second presentation is
`2`-isomorphic over `C` to the first presentation whiskered by the canonical isomorphism of
representing objects. -/
theorem presentation_unique
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    Nonempty
      (j' ≅
        j ≫ overMap (presentationIso j j' hj hj').hom) := by
  simpa [FibredInGroupoidsMor.InducesHom] using
    presentationComparisonHom_induces j j' hj hj'
end FibredInGroupoidsOver

end CategoryTheory
