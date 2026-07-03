import Mathlib
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.EpiMono
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_5_1 (from Chap14) -/
open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (U U' : CosimplicialObject C)

/- Domain-style sampling for Definition 14.5.1:
- primary domain: simplicial/cosimplicial objects as functor categories on `SimplexCategory`;
- sampled owner API:
  `CategoryTheory.CosimplicialObject`,
  `CosimplicialObject.δ`,
  `CosimplicialObject.σ`,
  `CosimplicialObject.const`;
- source/core/bridge triage:
  `source-facing`: the textbook notion of a cosimplicial object in `C`;
  `core/canonical`: the owner `CosimplicialObject C := SimplexCategory ⥤ C`;
  `bridge/view`: the specialization to concrete target categories such as `Type` or
  `AddCommGrpCat`, and the morphism view `U ⟶ U'` as a natural transformation.
- layer target: `core/canonical`, since Definition 14.5.1 only recalls the ambient owner notion
  itself rather than adding new source-facing structure.

Primitive data are only the ambient category `C`. Coface maps, codegeneracy maps, constant
cosimplicial objects, and specializations such as cosimplicial sets or cosimplicial abelian groups
are derived API from this owner, so this file should recall the canonical owner directly rather
than introduce any parallel wrapper. Unlike simplicial sets, mathlib does not provide a separate
owner abbreviation for cosimplicial `Type`-valued objects, so the direct type expression
`CosimplicialObject (Type u)` is already the canonical companion surface.
-/

/- Definition 14.5.1: a cosimplicial object of a category `C` is a covariant functor from
`SimplexCategory` to `C`; this is the canonical mathlib notion `CosimplicialObject C`. -/
recall CosimplicialObject

/- Companion check: a morphism of cosimplicial objects is canonically just a natural
transformation `U ⟶ U'`. -/
#check (U ⟶ U')

/- Companion check: since there is no separate upstream abbreviation for cosimplicial sets, the
canonical specialization is the direct type expression `CosimplicialObject (Type u)`. -/
#check (CosimplicialObject (Type u))

/- Companion check: cosimplicial abelian groups are cosimplicial objects in `AddCommGrpCat`. -/
#check (CosimplicialObject AddCommGrpCat)

end

/-! ### Lemma_14_5_2 (from Chap14) -/
universe u v

namespace CategoryTheory

open SimplexCategoryGenRel

/- Domain-style sampling for Lemma 14.5.2:
- primary domain: cosimplicial objects as functors on `SimplexCategory`, together with the
  functor-category equivalence induced by an equivalence of indexing categories;
- sampled owner API:
  `Functor.asEquivalence`,
  `Functor.whiskeringLeft`,
  `inferInstance : toSimplexCategory.IsEquivalence`,
  `CosimplicialObject.σ_naturality`,
  `CosimplicialObject.δ_naturality`,
  `CosimplicialObject.hom_ext`;
- best owner abstractions:
  `((Functor.whiskeringLeft _ _ C).obj toSimplexCategory).asEquivalence` for the source-facing
  presentation of cosimplicial objects by generators and relations, and `CosimplicialObject` for
  the coface/codegeneracy and morphism API;
- primitive data: only the canonical functor
  `toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory`;
- derived API: the induced precomposition equivalence on cosimplicial objects via
  `Functor.whiskeringLeft` and `Functor.asEquivalence`, plus the naturality and extensionality
  lemmas for morphisms of cosimplicial objects;
- source/core/bridge triage:
  `source-facing`: the generators-and-relations presentation `SimplexCategoryGenRel ⥤ C`;
  `core/canonical`: `CosimplicialObject C := SimplexCategory ⥤ C`;
  `bridge/view`: precomposition along `toSimplexCategory`.
-/

-- Proof sketch: by the canonical instance from Lemma 14.2.4,
-- `toSimplexCategory` is an equivalence.
-- The induced source-change equivalence on functor categories is the canonical owner
-- `((Functor.whiskeringLeft _ _ C).obj toSimplexCategory).asEquivalence`, and
-- `CosimplicialObject C` is definitionally `SimplexCategory ⥤ C`.
variable {C : Type u} [Category.{v} C]

/- Lemma 14.5.2: precomposition with the canonical functor
`toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory` is an
equivalence for every category `C`. This is the functor-category formulation of the statement that
cosimplicial objects in `C` are exactly sequences of objects with coface and codegeneracy maps
satisfying the cosimplicial identities, and that morphisms are degreewise families commuting with
these structure maps. The exact owner-level value is the canonical source-change equivalence
`((Functor.whiskeringLeft _ _ C).obj toSimplexCategory).asEquivalence`, built by
`Functor.asEquivalence` from the generic whiskering-left equivalence instance induced from the
canonical instance `inferInstance : toSimplexCategory.IsEquivalence`. -/
#check
  ((Functor.whiskeringLeft _ _ C).obj toSimplexCategory).asEquivalence

/- Companion recall: the commutation of the degreewise components of a morphism of cosimplicial
objects with the coface maps is the canonical owner lemma `CosimplicialObject.δ_naturality`. -/
recall CosimplicialObject.δ_naturality

/- Companion recall: the commutation with the codegeneracy maps is the canonical owner lemma
`CosimplicialObject.σ_naturality`. -/
recall CosimplicialObject.σ_naturality

/- Companion recall: equality of morphisms of cosimplicial objects from their degreewise
components is already owned by `CosimplicialObject.hom_ext`. -/
recall CosimplicialObject.hom_ext

end CategoryTheory

/-! ### Remark_14_5_3 (from Chap14) -/
universe v u

namespace CategoryTheory

open CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U : CosimplicialObject C)

/- Domain-style sampling for Remark 14.5.3:
- primary domain: cosimplicial objects and the cosimplicial identities for their coface and
  codegeneracy maps;
- sampled owner API:
  `CosimplicialObject.δ`,
  `CosimplicialObject.σ`,
  `CosimplicialObject.δ_comp_δ`,
  `CosimplicialObject.δ_comp_σ_of_le`,
  `CosimplicialObject.σ_comp_σ`;
- source/core/bridge triage:
  `source-facing`: the textbook operators `δ_i` and `σ_i` for one cosimplicial object `U`;
  `core/canonical`: the mathlib owner declarations `U.δ`, `U.σ`, and the canonical cosimplicial
  identity theorems;
  `bridge/view`: local notation exposing the source operators directly as those owner maps.
- primitive data: only the cosimplicial object `U`;
- derived API: the coface maps, codegeneracy maps, and all cosimplicial relations, which should be
  reused directly from the owner API rather than duplicated through local wrapper declarations.
- layer target: `bridge/view`, since the remark only rewrites the canonical owner data and
  identities into the textbook `δ_i`/`σ_i` notation for one fixed cosimplicial object.
-/

local notation "δ_" i:arg => U.δ i
local notation "σ_" i:arg => U.σ i

/- Remark 14.5.3 (1): for a cosimplicial object `U`, the coface maps written in the text as
`δ_i : U_n ⟶ U_{n + 1}` are the canonical morphisms `U.δ i`; the local notation `δ_ i` exposes
that textbook surface. -/
recall CosimplicialObject.δ
#check (fun {n : ℕ} (i : Fin (n + 2)) ↦ δ_ i)

/- Remark 14.5.3 (2): likewise, the codegeneracy maps written in the text as
`σ_i : U_{n + 1} ⟶ U_n` are the canonical morphisms `U.σ i`; the local notation `σ_ i` exposes
that textbook surface. -/
recall CosimplicialObject.σ
#check (fun {n : ℕ} (i : Fin (n + 1)) ↦ σ_ i)

/- Remark 14.5.3 (3): the first cosimplicial identity, namely
`δ_j ∘ δ_i = δ_i ∘ δ_{j - 1}` for `i < j`, whenever both composites are defined, is formalized by
`CosimplicialObject.δ_comp_δ`, which reads in the source notation as follows. -/
#check
  (show ∀ {n : ℕ} {i j : Fin (n + 2)}, i ≤ j → δ_ i ≫ δ_ (j.succ) = δ_ j ≫ δ_ (i.castSucc)
    from U.δ_comp_δ)

/- Remark 14.5.3 (4): the relation
`σ_j ∘ δ_i = δ_i ∘ σ_{j - 1}` for `i < j`, whenever both composites are defined, is formalized by
`CosimplicialObject.δ_comp_σ_of_le`, which becomes the following source-facing equality. -/
#check
  (show ∀ {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)},
      i ≤ j.castSucc → δ_ (i.castSucc) ≫ σ_ (j.succ) = σ_ j ≫ δ_ i
    from U.δ_comp_σ_of_le)

/- Remark 14.5.3 (5): the identity
`id = σ_j ∘ δ_j`, whenever the composite is defined, is formalized by
`CosimplicialObject.δ_comp_σ_self`, equivalently `δ_j ≫ σ_j = 𝟙`. -/
#check
  (show ∀ {n : ℕ} (j : Fin (n + 1)), δ_ (Fin.castSucc j) ≫ σ_ j = 𝟙 _ from
    fun j ↦ (U.δ_comp_σ_self : δ_ (Fin.castSucc j) ≫ σ_ j = 𝟙 _))

/- Remark 14.5.3 (6): the identity
`id = σ_j ∘ δ_{j + 1}`, whenever the composite is defined, is formalized by
`CosimplicialObject.δ_comp_σ_succ`, equivalently `δ_{j + 1} ≫ σ_j = 𝟙`. -/
#check
  (show ∀ {n : ℕ} (j : Fin (n + 1)), δ_ (j.succ) ≫ σ_ j = 𝟙 _ from
    fun j ↦ (U.δ_comp_σ_succ : δ_ (j.succ) ≫ σ_ j = 𝟙 _))

/- Remark 14.5.3 (7): the relation
`σ_j ∘ δ_i = δ_{i - 1} ∘ σ_j` for `i > j + 1`, whenever both composites are defined, is
formalized by `CosimplicialObject.δ_comp_σ_of_gt`, which in the source notation is the relation
below. -/
#check
  (show ∀ {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)},
      j.castSucc < i → δ_ (i.succ) ≫ σ_ (j.castSucc) = σ_ j ≫ δ_ i
    from U.δ_comp_σ_of_gt)

/- Remark 14.5.3 (8): the relation
`σ_j ∘ σ_i = σ_i ∘ σ_{j + 1}` for `i ≤ j`, whenever both composites are defined, is formalized by
`CosimplicialObject.σ_comp_σ`, which becomes the following equality in the source notation. -/
#check
  (show ∀ {n : ℕ} {i j : Fin (n + 1)},
      i ≤ j → σ_ (i.castSucc) ≫ σ_ j = σ_ (j.succ) ≫ σ_ i
    from U.σ_comp_σ)

end CategoryTheory

/-! ### Example_14_5_4 (from Chap14) -/
universe v u

open CategoryTheory
open scoped Simplicial

section

variable (C : Type u) [Category.{v} C] (X : C)
variable (n : ℕ)

/- Domain-style sampling for Example 14.5.4:
- primary domain: cosimplicial objects as functors on `SimplexCategory`;
- sampled owner API:
  `CosimplicialObject`,
  `CosimplicialObject.const`,
  `CosimplicialObject.Augmented.const`,
  `SimplicialObject.const`;
- best owner abstraction: the mathlib owner functor
  `CosimplicialObject.const : C ⥤ CosimplicialObject C`;
- source/core/bridge triage:
  `source-facing`: the textbook constant cosimplicial object on `X`;
  `core/canonical`: the owner functor `CosimplicialObject.const`;
  `bridge/view`: the degreewise equalities showing that every term is `X` and every structure map
  is `𝟙 X`.

Primitive data are only the ambient category `C` and the object `X`. The degreewise object and map
descriptions are derived directly from the constant-functor owner, so this file should expose the
source-facing object `(CosimplicialObject.const C).obj X` directly and keep the owner functor only
as companion context rather than introduce any parallel local wrapper.
-/

/- Example 14.5.4: the simplest cosimplicial object with value `X` is the constant cosimplicial
object `(CosimplicialObject.const C).obj X`; equivalently, every term is `X` and every
cosimplicial structure map is `𝟙 X`. -/
#check ((CosimplicialObject.const C).obj X)

/- Companion recall: the owner of constant cosimplicial objects is the functor
`CosimplicialObject.const : C ⥤ CosimplicialObject C`. -/
recall CosimplicialObject.const

/- Companion check: the degree `n` term of the constant cosimplicial object is definitionally
`X`. -/
#check (rfl : ((CosimplicialObject.const C).obj X) ^⦋n⦌ = X)

/- Companion check: each cosimplicial structure map of the constant cosimplicial object is
definitionally `𝟙 X`. -/
#check (fun {Δ Δ' : SimplexCategory} (φ : Δ ⟶ Δ') ↦
  show ((CosimplicialObject.const C).obj X).map φ = 𝟙 X from rfl)

end

/-! ### Example_14_5_5 (from Chap14) -/
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] (f : Arrow C)
variable [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) ↦ f.right) fun _ ↦ f.hom]

/- Domain-style sampling for Example 14.5.5:
- primary domain: Čech conerves as cosimplicial objects attached to an arrow via iterated wide
  pushouts;
- sampled owner API:
  `CategoryTheory.Arrow.cechConerve`,
  `CategoryTheory.Arrow.augmentedCechConerve`,
  `CategoryTheory.Arrow.mapCechConerve`,
  `CategoryTheory.CosimplicialObject.cechConerve`;
- best owner abstraction: `CategoryTheory.Arrow.cechConerve`; the source-facing example is already
  the canonical owner declaration, so the main entry should be direct recall rather than a local
  wrapper or restatement;
- source/core/bridge triage:
  `source-facing`: the arrow-level cosimplicial object `f.cechConerve`;
  `core/canonical`: the same mathlib owner `CategoryTheory.Arrow.cechConerve`;
  `bridge/view`: the functorial packaging `CategoryTheory.CosimplicialObject.cechConerve` and the
  augmented variant `f.augmentedCechConerve`;
- primitive data: the arrow `f` and the degreewise wide-pushout existence assumptions;
- derived API: functoriality in morphisms of arrows, the augmented conerve, and the degreewise
  description by `(n + 1)`-fold pushouts. -/

/- Example 14.5.5: a morphism `f : X ⟶ Y` whose iterated pushouts exist determines the canonical
cosimplicial object `f.cechConerve`. Its term in degree `n` is the `(n + 1)`-fold pushout of
copies of `Y` over `X`, and a simplex map acts by sending the `i`-th copy of `Y` to the
`φ(i)`-th copy. In degree `0` and `1`, this gives the map `U₁ ⟶ U₀` that is the identity on each
component and the two maps `U₀ ⟶ U₁` given by the coprojections. -/
#check (f.cechConerve : CosimplicialObject C)

/- Companion recall: the canonical owner declaration for this example is
`CategoryTheory.Arrow.cechConerve`. -/
recall cechConerve

end CategoryTheory.Arrow

/-! ### Example_14_5_6 (from Chap14) -/
open CategoryTheory Opposite
open scoped Simplicial

scoped[Simplicial] notation3 "C[" n "]" =>
  (coyoneda.obj (op ⦋n⦌) : CosimplicialObject (Type))

variable (n : ℕ)

/- Domain-style sampling for Example 14.5.6:
- primary domain: representable functors on `SimplexCategory`, viewed covariantly as cosimplicial
  sets;
- sampled owner API:
  `CategoryTheory.coyoneda.obj`,
  `CategoryTheory.coyonedaEquiv`,
  `CategoryTheory.coyonedaEquiv_apply`,
  `CategoryTheory.coyonedaEquiv_symm_app_apply`;
- source/core/bridge triage:
  `source-facing`: the Stacks notation `C[n]` for the covariant representable functor on `Δ`
  represented by `[n]`;
  `core/canonical`: `coyoneda.obj (op ⦋n⦌)`;
  `bridge/view`: evaluation in cosimplicial degree `k`, written canonically as `^⦋k⦌`, giving the
  hom-set `Hom([n], [k])`.

Primitive data are only the simplex `[n]`. The value at `[k]` is derived API from the canonical
owner `coyoneda.obj`, so any local alias or theorem shell around that evaluation should be deleted
rather than kept as a parallel public wrapper.
-/

/- Example 14.5.6: for each `n ≥ 0`, the cosimplicial set denoted `C[n]` is the covariant
representable functor on `SimplexCategory` represented by `[n]`, with canonical owner
`coyoneda.obj (op ⦋n⦌)`. The source-facing chapter surface uses the notation `C[n]`. -/
#check (C[n] : CosimplicialObject (Type))

variable (k : ℕ)

/- Companion check: evaluating the costandard simplex `C[n]` at `[k]` is definitionally the
hom-set `Hom([n], [k])` in `SimplexCategory`, so this should stay a direct check of the owner’s
evaluation formula rather than a second named theorem. -/
#check
  (rfl :
    (C[n] : CosimplicialObject (Type)) ^⦋k⦌ = (⦋n⦌ ⟶ ⦋k⦌))

/-! ### Lemma_14_5_7 (from Chap14) -/
universe v u

namespace CategoryTheory

open CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 2))

/- Domain-style sampling for Lemma 14.5.7:
- primary domain: cosimplicial objects and the split-mono structure on their coface maps;
- sampled owner API:
  `CosimplicialObject.δ`,
  `CosimplicialObject.σ`,
  `CosimplicialObject.δ_comp_σ_self`,
  `CosimplicialObject.δ_comp_σ_succ`,
  `CategoryTheory.SplitMono.mk`,
  `CategoryTheory.SplitMono.mono`;
- best owner abstraction: the category-theoretic owner `SplitMono (U.δ i)`, with retraction
  chosen directly from the canonical codegeneracy maps of `U`;
- primitive data: the coface map `U.δ i`, the codegeneracy retraction
  `Fin.lastCases (U.σ (Fin.last n)) (fun j ↦ U.σ j) i`, and the two cosimplicial identities
  `U.δ_comp_σ_self` and `U.δ_comp_σ_succ`;
- derived API: the resulting `Mono (U.δ i)` fact, obtained from the `SplitMono` owner;
- source/core/bridge triage:
  `source-facing`: the textbook statement that every coface map has a left inverse, hence is
    monic;
  `core/canonical`: `SplitMono`;
  `bridge/view`: none, since the source retractions are already the canonical codegeneracy maps.
- layer target: `source-facing`, phrased directly in terms of the coface map `U.δ i` and the
  canonical categorical owner `SplitMono`.
-/

/- Lemma 14.5.7: for a cosimplicial object `U`, each coface morphism `U.δ i` has a canonical
left inverse, namely `U.σ j` when `i = j.castSucc` and `U.σ j` when `i = j.succ`. Equivalently,
the following term is the canonical split-mono witness for `U.δ i`. -/
#check
  let splitMonoδ : SplitMono (U.δ i) :=
    SplitMono.mk (Fin.lastCases (U.σ (Fin.last n)) (fun j ↦ U.σ j) i) <| by
      cases i using Fin.lastCases with
      | last =>
          simp only [Fin.lastCases_last]
          simpa using
            (show U.δ (Fin.last n).succ ≫ U.σ (Fin.last n) = 𝟙 _ from U.δ_comp_σ_succ)
      | cast j =>
          simp only [Fin.lastCases_castSucc]
          exact U.δ_comp_σ_self
  splitMonoδ

/- Companion check: hence every coface morphism in a cosimplicial object is monic. -/
#check
  let splitMonoδ : SplitMono (U.δ i) :=
    SplitMono.mk (Fin.lastCases (U.σ (Fin.last n)) (fun j ↦ U.σ j) i) <| by
      cases i using Fin.lastCases with
      | last =>
          simp only [Fin.lastCases_last]
          simpa using
            (show U.δ (Fin.last n).succ ≫ U.σ (Fin.last n) = 𝟙 _ from U.δ_comp_σ_succ)
      | cast j =>
          simp only [Fin.lastCases_castSucc]
          exact U.δ_comp_σ_self
  splitMonoδ.mono

end CategoryTheory
