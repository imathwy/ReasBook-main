import Mathlib
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.EpiMono
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_3_1 (from Chap14) -/
open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (U U' : SimplicialObject C)

/- Domain-style sampling for Definition 14.3.1:
- primary domain: simplicial objects as presheaves on `SimplexCategory`;
- sampled owner API:
  `CategoryTheory.SimplicialObject`,
  `SimplicialObject.δ`,
  `SimplicialObject.const`,
  `SSet`;
- source/core/bridge triage:
  `source-facing`: the textbook notion of a simplicial object in `C`;
  `core/canonical`: the owner abbreviation `SimplicialObject C := SimplexCategoryᵒᵖ ⥤ C`;
  `bridge/view`: the specialization `SSet` and the underlying functor-category morphism view.

Primitive data are only the ambient category `C`. Face maps, degeneracy maps, constant simplicial
objects, and specializations such as simplicial sets or simplicial abelian groups are derived API
from this owner, so this file should recall the canonical owner directly rather than introduce any
parallel wrapper.
-/

/- Definition 14.3.1: a simplicial object of a category `C` is a contravariant functor from
`SimplexCategory` to `C`; this is the canonical mathlib abbreviation `SimplicialObject C`. -/
recall SimplicialObject

/- Companion check: a morphism of simplicial objects is canonically just a natural transformation
`U ⟶ U'`. -/
#check (U ⟶ U')

/- Companion recall: a simplicial set is a simplicial object in the category of types; this is the
canonical abbreviation `SSet`. -/
recall SSet

/- Companion check: a simplicial abelian group is a simplicial object in the category
`AddCommGrpCat`. -/
#check (SimplicialObject AddCommGrpCat)

end

/-! ### Lemma_14_3_2 (from Chap14) -/
universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.3.2:
- primary domain: simplicial objects as functors on `SimplexCategoryᵒᵖ`, together with the
  functor-category equivalence induced by an equivalence of indexing categories;
- sampled owner API:
  `inferInstance : SimplexCategoryGenRel.toSimplexCategory.IsEquivalence`,
  `Functor.asEquivalence`,
  `SimplicialObject.δ_naturality`,
  `SimplicialObject.σ_naturality`,
  `SimplicialObject.hom_ext`;
- best owner abstraction:
  `((Functor.whiskeringLeft _ _ C).obj SimplexCategoryGenRel.toSimplexCategory.op).asEquivalence`
  for the source-facing presentation of simplicial objects by generators and relations;
- primitive data: only the canonical functor
  `SimplexCategoryGenRel.toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory`;
- derived API: the induced precomposition equivalence on simplicial objects via
  `Functor.asEquivalence`, plus the naturality and extensionality lemmas for morphisms of
  simplicial objects;
- source/core/bridge triage:
  `source-facing`: the generators-and-relations presentation `SimplexCategoryGenRelᵒᵖ ⥤ C`;
  `core/canonical`: `SimplicialObject C := SimplexCategoryᵒᵖ ⥤ C`;
  `bridge/view`: precomposition along `SimplexCategoryGenRel.toSimplexCategory.op`.
-/

-- Proof sketch: by the canonical instance from Lemma 14.2.4,
-- `SimplexCategoryGenRel.toSimplexCategory` is an equivalence.
-- Precomposition with its opposite is again an equivalence on functor categories via
-- `whiskeringLeft`, and `SimplicialObject C` is definitionally `SimplexCategoryᵒᵖ ⥤ C`.
variable {C : Type u} [Category.{v} C]

/- Lemma 14.3.2: precomposition with the canonical functor
`SimplexCategoryGenRel.toSimplexCategory.op : SimplexCategoryGenRelᵒᵖ ⥤ SimplexCategoryᵒᵖ` is an
equivalence for every category `C`. This is the functor-category formulation of the statement that
simplicial objects in `C` are exactly sequences of objects with face and degeneracy maps
satisfying the simplicial identities, and that morphisms are degreewise families commuting with
these structure maps. The exact owner-level value is the canonical equivalence
`((Functor.whiskeringLeft _ _ C).obj SimplexCategoryGenRel.toSimplexCategory.op).asEquivalence`,
built by `Functor.asEquivalence` from the generic whiskering-left equivalence instance induced
from the canonical instance
`inferInstance : SimplexCategoryGenRel.toSimplexCategory.IsEquivalence`. -/
#check
  ((Functor.whiskeringLeft _ _ C).obj SimplexCategoryGenRel.toSimplexCategory.op).asEquivalence

/- Companion recall: the commutation of the degreewise components of a morphism of simplicial
objects with the face maps is the canonical owner lemma `SimplicialObject.δ_naturality`. -/
recall SimplicialObject.δ_naturality

/- Companion recall: the commutation with the degeneracy maps is the canonical owner lemma
`SimplicialObject.σ_naturality`. -/
recall SimplicialObject.σ_naturality

/- Companion recall: equality of morphisms of simplicial objects from their degreewise components
is already owned by `SimplicialObject.hom_ext`. -/
recall SimplicialObject.hom_ext

end CategoryTheory

/-! ### Remark_14_3_3 (from Chap14) -/
universe v u

namespace CategoryTheory

open SimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U : SimplicialObject C)

/- Domain-style sampling for Remark 14.3.3:
- primary domain: simplicial objects and the simplicial identities for their face and degeneracy
  maps;
- sampled owner API:
  `SimplicialObject.δ`,
  `SimplicialObject.σ`,
  `SimplicialObject.δ_comp_δ`,
  `SimplicialObject.δ_comp_σ_of_le`,
  `SimplicialObject.δ_comp_σ_self`,
  `SimplicialObject.δ_comp_σ_succ`,
  `SimplicialObject.δ_comp_σ_of_gt`,
  `SimplicialObject.σ_comp_σ`;
- source/core/bridge triage:
  `source-facing`: the textbook operators `d_i` and `s_i` and their relations for one simplicial
  object `U`;
  `core/canonical`: the mathlib owner declarations `U.δ`, `U.σ`, and the canonical simplicial
  identity theorems;
  `bridge/view`: local notation exposing the source operators directly as the canonical owner maps.
- primitive data: only the simplicial object `U`;
- derived API: the face maps, degeneracy maps, and all simplicial relations, which should be reused
  directly from the owner API rather than duplicated through new wrapper declarations.
- layer target: `bridge/view`, since the remark only rewrites the canonical owner maps and
  simplicial identities into the textbook notation for one fixed simplicial object.
-/

local notation "d_" i:arg => U.δ i
local notation "s_" i:arg => U.σ i

/- Remark 14.3.3 (1): for a simplicial object `U`, the face maps written in the text as
`d_i : U_n ⟶ U_{n - 1}` are the canonical morphisms `U.δ i`; the local notation `d_ i` exposes
that textbook surface. -/
recall SimplicialObject.δ
#check (fun {n : ℕ} (i : Fin (n + 2)) ↦ d_ i)

/- Remark 14.3.3 (2): likewise, the degeneracy maps written in the text as
`s_i : U_n ⟶ U_{n + 1}` are the canonical morphisms `U.σ i`; the local notation `s_ i` exposes
that textbook surface. -/
recall SimplicialObject.σ
#check (fun {n : ℕ} (i : Fin (n + 1)) ↦ s_ i)

/- Remark 14.3.3 (3): the first simplicial identity, namely
`d_i ∘ d_j = d_{j - 1} ∘ d_i` for `i < j`, whenever both composites are defined, is formalized by
`SimplicialObject.δ_comp_δ`, which reads in the source notation as follows. -/
#check (fun {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) ↦
  (show d_ j.succ ≫ d_ i = d_ i.castSucc ≫ d_ j from U.δ_comp_δ h))

/- Remark 14.3.3 (4): the relation
`d_i ∘ s_j = s_{j - 1} ∘ d_i` for `i < j`, whenever both composites are defined, is formalized by
`SimplicialObject.δ_comp_σ_of_le`, which becomes the following source-facing equality. -/
#check (fun {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (h : i ≤ j.castSucc) ↦
  (show s_ j.succ ≫ d_ i.castSucc = d_ i ≫ s_ j from U.δ_comp_σ_of_le h))

/- Remark 14.3.3 (5): the identity
`id = d_j ∘ s_j`, whenever the composite is defined, is formalized by
`SimplicialObject.δ_comp_σ_self`, equivalently `s_j ≫ d_j = 𝟙`. -/
#check (fun {n : ℕ} (j : Fin (n + 1)) ↦
  (show s_ j ≫ d_ j.castSucc = 𝟙 _ from U.δ_comp_σ_self))

/- Remark 14.3.3 (6): the identity
`id = d_{j + 1} ∘ s_j`, whenever the composite is defined, is formalized by
`SimplicialObject.δ_comp_σ_succ`, equivalently `s_j ≫ d_{j + 1} = 𝟙`. -/
#check (fun {n : ℕ} (j : Fin (n + 1)) ↦
  (show s_ j ≫ d_ j.succ = 𝟙 _ from U.δ_comp_σ_succ))

/- Remark 14.3.3 (7): the relation
`d_i ∘ s_j = s_j ∘ d_{i - 1}` for `i > j + 1`, whenever both composites are defined, is
formalized by `SimplicialObject.δ_comp_σ_of_gt`, which in the source notation is the relation
below. -/
#check (fun {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (h : j.castSucc < i) ↦
  (show s_ j.castSucc ≫ d_ i.succ = d_ i ≫ s_ j from U.δ_comp_σ_of_gt h))

/- Remark 14.3.3 (8): the relation
`s_i ∘ s_j = s_{j + 1} ∘ s_i` for `i ≤ j`, whenever both composites are defined, is formalized by
`SimplicialObject.σ_comp_σ`, which becomes the following equality in the source notation. -/
#check (fun {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) ↦
  (show s_ j ≫ s_ i.castSucc = s_ i ≫ s_ j.succ from U.σ_comp_σ h))

end CategoryTheory

/-! ### Example_14_3_4 (from Chap14) -/
universe v u

open CategoryTheory

section

variable (C : Type u) [Category.{v} C] (X : C)

/- Domain-style sampling for Example 14.3.4:
- primary domain: simplicial objects as presheaves on `SimplexCategory`;
- sampled owner API:
  `CategoryTheory.Functor.const`,
  `SimplicialObject.const`,
  `SimplicialObject.Augmented.const`,
  `CosimplicialObject.const`;
- best owner abstraction: the mathlib owner functor
  `SimplicialObject.const : C ⥤ SimplicialObject C`;
- source/core/bridge triage:
  `source-facing`: the textbook constant simplicial object on `X`;
  `core/canonical`: the owner functor `SimplicialObject.const`;
  `bridge/view`: the degreewise equalities showing that every term is `X` and every structure map
  is `𝟙 X`.

Primitive data are only the ambient category `C` and the object `X`. The degreewise object and map
descriptions are derived directly from the constant-functor owner, so this file should expose the
source-facing object `(SimplicialObject.const C).obj X` directly and keep the owner functor only
as companion context rather than introduce any parallel local wrapper.
-/

/- Example 14.3.4: the simplest simplicial object with value `X` is the constant simplicial
object `(SimplicialObject.const C).obj X`; equivalently, every term is `X` and every simplicial
structure map is `𝟙 X`. -/
#check ((SimplicialObject.const C).obj X)

/- Companion recall: the owner of constant simplicial objects is the functor
`SimplicialObject.const : C ⥤ SimplicialObject C`. -/
recall SimplicialObject.const

/- Companion check: each degree of the constant simplicial object is definitionally `X`. -/
#check (fun (Δ : SimplexCategoryᵒᵖ) ↦
  show ((SimplicialObject.const C).obj X).obj Δ = X from rfl)

/- Companion check: each simplicial structure map of the constant simplicial object is
definitionally `𝟙 X`. -/
#check (fun {Δ Δ' : SimplexCategoryᵒᵖ} (φ : Δ ⟶ Δ') ↦
  show ((SimplicialObject.const C).obj X).map φ = 𝟙 X from rfl)

end

/-! ### Example_14_3_5 (from Chap14) -/
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] (f : Arrow C)
variable [∀ n : ℕ, HasWidePullback.{0} f.right
  (fun _ : Fin (n + 1) ↦ f.left) (fun _ ↦ f.hom)]

/- Domain-style sampling for Example 14.3.5:
- primary domain: Čech nerves of arrows in a category with the required iterated wide pullbacks;
- sampled owner declarations:
  `Arrow.cechNerve`,
  `Arrow.augmentedCechNerve`,
  `SimplicialObject.cechNerve`,
  `SimplicialObject.augmentedCechNerve`;
- best owner abstraction: the source-facing object here is the arrow-level simplicial object
  `f.cechNerve`; the augmentation to the codomain is additional derived structure carried by
  `f.augmentedCechNerve`;
- primitive data: only the arrow `f` together with the wide-pullback existence assumptions needed
  by the canonical owner;
- derived API: the augmented companion `f.augmentedCechNerve`, the functorial construction
  `SimplicialObject.cechNerve`, the augmented functorial package
  `SimplicialObject.augmentedCechNerve`, and the degreewise wide-pullback face/degeneracy
  description coming from the owner definition.

Source/core/bridge triage:
- `source-facing`: the simplicial object `f.cechNerve` with `n`-simplices the `(n + 1)`-fold
  fibre product of `f.left` over `f.right`;
- `core/canonical`: the same mathlib owner `Arrow.cechNerve`;
- `bridge/view`: the augmented companion `Arrow.augmentedCechNerve` and the functorial packages
  `SimplicialObject.cechNerve` and `SimplicialObject.augmentedCechNerve`.

This file introduces no additional primitive data beyond the mathlib owner, so the correct
refinement is direct canonical use of `f.cechNerve`, with the augmentation recorded only as its
derived companion `f.augmentedCechNerve` rather than as a parallel local wrapper. -/

/- Example 14.3.5: for a morphism `f : Y ⟶ X` such that all iterated fibre products of `Y` over
`X` exist, the canonical simplicial object with `n`-simplices the `(n + 1)`-fold fibre product of
`Y` over `X` is `f.cechNerve`. In degree `0` one gets `Y`, in degree `1` one gets the self-fibre
product `Y ×[X] Y`, the two face maps are the projections, and the unique degeneracy is the
diagonal. -/
#check (f.cechNerve : SimplicialObject C)

/- Companion recall: the canonical owner declaration for this example is
`CategoryTheory.Arrow.cechNerve`. -/
recall cechNerve

/- Bridge/view: the augmentation to the constant simplicial object on `X` is the canonical derived
companion `f.augmentedCechNerve`. -/
#check (f.augmentedCechNerve : SimplicialObject.Augmented C)

/- Companion recall: the canonical augmented companion is
`CategoryTheory.Arrow.augmentedCechNerve`. -/
recall augmentedCechNerve

end CategoryTheory.Arrow

/-! ### Lemma_14_3_6 (from Chap14) -/
universe u v

namespace CategoryTheory

open SimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 1))

/- Domain-style sampling for Lemma 14.3.6:
- primary domain: simplicial identities for degeneracy morphisms in simplicial objects;
- sampled owner API:
  `SimplicialObject.σ`,
  `SimplicialObject.δ_comp_σ_self`,
  `CategoryTheory.SplitMono`,
  `CategoryTheory.SplitMono.mono`;
- source/core/bridge triage:
- `source-facing`: the degeneracy morphism `U.σ i` together with its canonical left inverse
    `U.δ i.castSucc`;
  - `core/canonical`: the category-theoretic split-mono witness `SplitMono (U.σ i)` and its
    derived `Mono (U.σ i)` consequence;
  - `bridge/view`: no extra local bridge is needed, since the simplicial identity
    `U.δ_comp_σ_self` feeds directly into the canonical `SplitMono` owner.
- primitive data: the simplicial object `U`, the index `i`, and the retraction identity
  `U.δ_comp_σ_self`;
- derived API: the canonical split-mono witness and the resulting `Mono` fact, obtained directly
  from `U.δ_comp_σ_self` rather than through local wrapper declarations.
- layer target: `source-facing`, with the theorem surface phrased for `U.σ i` and the proof
  centered on the owner lemma `U.δ_comp_σ_self`.
-/

/- Lemma 14.3.6: for a simplicial object `U`, the degeneracy morphism
`U.σ i : U _⦋n⦌ ⟶ U _⦋n + 1⦌` has left inverse `U.δ i.castSucc`, equivalently
`U.σ i ≫ U.δ (Fin.castSucc i) = 𝟙 _`. This is exactly the first half of the third simplicial
identity. -/
recall SimplicialObject.δ_comp_σ_self :
  U.σ i ≫ U.δ i.castSucc = 𝟙 _

/- Companion check: `U.δ i.castSucc` exhibits `U.σ i` as a split monomorphism. -/
#check
  SplitMono.mk (U.δ i.castSucc) U.δ_comp_σ_self

/- Companion check: hence degeneracy morphisms are monomorphisms. -/
#check
  SplitMono.mono (SplitMono.mk (U.δ i.castSucc) U.δ_comp_σ_self)

end CategoryTheory
