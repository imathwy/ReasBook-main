import Mathlib
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.Tactic.Recall
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_6_21_1 (from Chap06) -/
/- Domain-style sampling for Lemma 6.21.1:
- primary domain: sheaf pushforward along a continuous map of topological spaces;
- sampled owner declarations:
  `TopCat.Sheaf.pushforward_sheaf_of_sheaf`,
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pushforwardForgetIso`,
  `TopCat.Presheaf.pushforward`;
- owner abstraction: the canonical owner is the sheaf-level theorem
  `TopCat.Sheaf.pushforward_sheaf_of_sheaf`;
- primitive data: a continuous map `f : X ⟶ Y` and a sheaf condition on the underlying presheaf;
- derived API: the sheaf pushforward functor and its forgetful comparison to presheaf pushforward.

Source/core/bridge triage:
- `source-facing`: the textbook assertion that the direct image of a sheaf of sets is again a
  sheaf of sets;
- `core/canonical`: `TopCat.Sheaf.pushforward_sheaf_of_sheaf`;
- `bridge/view`: the functor-level owner `TopCat.Sheaf.pushforward`, whose object part uses the
  recalled theorem.

The numbered item is only the `C := Type u` specialization of the canonical owner theorem, so the
refined file should recall that theorem directly rather than introduce a local wrapper or restate
the sheaf data as primitive structure. -/

namespace TopCat.Sheaf

/- Lemma 6.21.1: for a continuous map `f : X ⟶ Y`, the direct image of a sheaf of sets on `X`
is again a sheaf of sets on `Y`. In Lean this is the `C := Type u` specialization of the canonical
mathlib theorem `TopCat.Sheaf.pushforward_sheaf_of_sheaf`. -/
recall pushforward_sheaf_of_sheaf

end TopCat.Sheaf

/-! ### Lemma_6_21_2 (from Chap06) -/
universe u

open CategoryTheory TopCat

/- Domain-style sampling for Lemma 6.21.2:
- primary domain: pushforward of presheaves and sheaves of sets along continuous maps;
- inspected owner declarations:
  `TopCat.Presheaf.pushforward`,
  `TopCat.Presheaf.Pushforward.comp_eq`,
  `TopCat.Presheaf.Pushforward.comp`,
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pushforward_forget`;
- owner abstraction: for both presheaves and sheaves, the owner is the pushforward functor itself,
  `TopCat.Presheaf.pushforward` and `TopCat.Sheaf.pushforward`; the objectwise presheaf theorems
  `TopCat.Presheaf.Pushforward.comp_eq` and `TopCat.Presheaf.Pushforward.comp` are derived API;
- primitive data: continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`;
- derived API: the objectwise presheaf comparison isomorphism/equality; the functor-level
  comparison below is just the raw canonical equality expression and needs no local theorem wrapper.

Source/core/bridge triage:
- `source-facing`: Lemma 6.21.2 records how direct image behaves under composition;
- `core/canonical`: `TopCat.Presheaf.pushforward` and `TopCat.Sheaf.pushforward`;
- `bridge/view`: the objectwise presheaf API `TopCat.Presheaf.Pushforward.comp_eq` /
  `TopCat.Presheaf.Pushforward.comp`, which remains available as companion data beneath the
  source-facing functor equalities below.

Since both parts are definitional equalities of pushforward functors, the source-facing public
surface should state those equalities directly. The presheaf objectwise theorem
`TopCat.Presheaf.Pushforward.comp_eq` remains only companion API, and this file records the
functor-level statements by direct canonical checks instead of parallel theorem names. -/

namespace TopCat.Presheaf

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 6.21.2 (1): for continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`, the direct image of a
presheaf of sets along `g ∘ f` is definitionally the iterated direct image functor `g_* ∘ f_*`.
Objectwise this specializes to `TopCat.Presheaf.Pushforward.comp_eq`. -/
#check (rfl :
  TopCat.Presheaf.pushforward (Type u) (f ≫ g) =
    TopCat.Presheaf.pushforward (Type u) f ⋙ TopCat.Presheaf.pushforward (Type u) g)

end TopCat.Presheaf

namespace TopCat.Sheaf

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 6.21.2 (2): for continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`, the pushforward on sheaves
of sets along `g ∘ f` is definitionally the composite `g_* ∘ f_*`. -/
#check (rfl :
  TopCat.Sheaf.pushforward (Type u) (f ≫ g) =
    TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g)

end TopCat.Sheaf

/-! ### Lemma_6_21_3 (from Chap06) -/
universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TopCat.Presheaf

/- Domain-style sampling for Lemma 6.21.3:
- primary domain: inverse image of set-valued presheaves along a continuous map, organized as
  left Kan extension on the category of opens;
- sampled owner API:
  `TopCat.Presheaf.pullback`,
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `Functor.leftKanExtensionObjIsoColimit`,
  `IsFiltered (CostructuredArrow (Opens.map f).op (op U))`;
- source/core/bridge triage:
  `source-facing`: the Stacks description of `f⁻¹ 𝒢` and its objectwise colimit over neighborhoods
  of `f(U)`;
  `core/canonical`: the presheaf pullback owner `pullback (Type u) f` and its adjunction with
  pushforward;
  `bridge/view`: the specialization of `Functor.leftKanExtensionObjIsoColimit` to
  `(Opens.map f).op`, together with the filteredness instance for the indexing category.

Primitive data are only the continuous map `f`, the presheaf `𝒢`, and the open `U`. The pullback,
its adjunction, the objectwise colimit formula, and the filteredness of the costructured-arrow
indexing category are all derived from the canonical left-Kan-extension owner, so this file should
recall those owners directly rather than keep parallel wrapper declarations.
-/

/- Lemma 6.21.3: for a continuous map `f : X ⟶ Y`, the canonical presheaf pullback functor on
`Type`-valued presheaves is left adjoint to pushforward. In mathlib this is the canonical
adjunction `TopCat.Presheaf.pullbackPushforwardAdjunction`, specialized here to presheaves of
sets. -/
recall TopCat.Presheaf.pullbackPushforwardAdjunction

/- Companion owner recall: the pointwise description of a left Kan extension as a colimit is the
canonical declaration `Functor.leftKanExtensionObjIsoColimit`. -/
recall Functor.leftKanExtensionObjIsoColimit

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒢 : Y.Presheaf (Type u)) (U : Opens X)

/- Lemma 6.21.3, bridge/view recall: the value of the inverse-image presheaf on `U` is the
canonical colimit computing the left Kan extension along `(Opens.map f).op`; this is exactly
`Functor.leftKanExtensionObjIsoColimit` specialized to the opens functor. -/
#check
  ((Opens.map f).op.leftKanExtensionObjIsoColimit 𝒢 (op U) :
    (((pullback (Type u) f).obj 𝒢).obj (op U)) ≅
      colimit (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ 𝒢))

/- The same indexing category is filtered, expressing that neighborhoods of `f(U)` form a directed
system under reverse inclusion. This is direct instance recall, not a separate chapter-level
owner. -/
#check (inferInstance : IsFiltered (CostructuredArrow (Opens.map f).op (op U)))

end

/-! ### Lemma_6_21_4 (from Chap06) -/
universe u

open CategoryTheory TopCat

/- Domain-style sampling for Lemma 6.21.4:
- primary domain: stalks of presheaves under pullback along a continuous map;
- inspected owner declarations:
  `TopCat.Presheaf.stalkPullbackIso`,
  `TopCat.Presheaf.pullback`,
  `TopCat.Presheaf.stalk`,
  `TopCat.Sheaf.stalkPullbackIso`;
- owner abstraction: the canonical owner is `TopCat.Presheaf.stalkPullbackIso`;
- primitive data: a continuous map `f : X ⟶ Y`, a presheaf `𝒢 : Y.Presheaf (Type u)`, and a point
  `x : X`;
- derived API: none in this file beyond the direct recall of the canonical owner.

Source/core/bridge triage:
- `source-facing`: this numbered item is the set-valued specialization of the standard
  stalk-pullback comparison;
- `core/canonical`: `TopCat.Presheaf.stalkPullbackIso`;
- `bridge/view`: the sheaf-level analogue `TopCat.Sheaf.stalkPullbackIso`, treated separately in
  `Lemma_6_21_5`.

Since the textbook statement is exactly the `C := Type u` specialization of the canonical owner,
the refined file should expose that owner directly rather than keep a local wrapper. -/

/- Lemma 6.21.4: for a continuous map `f : X ⟶ Y`, a presheaf of sets `𝒢` on `Y`, and a point
`x : X`, the canonical bijection of stalks `(f_p 𝒢)_x = 𝒢_{f(x)}` is exactly the `Type u`
specialization of the canonical owner `TopCat.Presheaf.stalkPullbackIso`. -/
recall TopCat.Presheaf.stalkPullbackIso

namespace TopCat.Presheaf

section
variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒢 : Y.Presheaf (Type u)) (x : X)

/- Companion specialization of `TopCat.Presheaf.stalkPullbackIso` to set-valued presheaves. -/
#check
  (show 𝒢.stalk (f x) ≅ ((pullback (Type u) f).obj 𝒢).stalk x from
    TopCat.Presheaf.stalkPullbackIso (Type u) f 𝒢 x)

end

end TopCat.Presheaf

/-! ### Lemma_6_21_5 (from Chap06) -/
open CategoryTheory CategoryTheory.Limits TopCat
open TopCat.Presheaf
open scoped TopCat

noncomputable section

universe w v u

namespace TopCat

/- Source-facing notation for inverse image on sheaves. The ambient coefficient category is
inferred from the expected functor type. -/
scoped notation:max f:max "⁻¹" => TopCat.Sheaf.pullback _ f

end TopCat

namespace TopCat.Sheaf

/- Domain-style sampling for Lemma 6.21.5:
- primary domain: stalkwise comparison for inverse-image sheaves on topological spaces;
- sampled owner declarations:
  `TopCat.Presheaf.stalkPullbackIso`,
  `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pullbackIso`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`;
- owner abstraction: the core upstream owner is the presheaf-level stalk comparison
  `TopCat.Presheaf.stalkPullbackIso`; this file supplies the sheaf-level bridge owner obtained by
  composing that canonical isomorphism with the stalkwise sheafification comparison for pullback
  and the sheaf pullback comparison `TopCat.Sheaf.pullbackIso`;
- primitive data: a continuous map `f : X ⟶ Y`, a sheaf `𝒢 : Y.Sheaf A`, and a point `x : X`;
- derived API: only the comparison from the stalk of the presheaf pullback to the stalk of the
  sheaf pullback.

Source/core/bridge triage:
- `source-facing`: the Stacks-style statement that the stalk of `f⁻¹𝒢` at `x` is the stalk of
  `𝒢` at `f x`;
- `core/canonical`: `TopCat.Presheaf.stalkPullbackIso`;
- `bridge/view`: the stalkwise comparison between the presheaf pullback and the sheaf pullback. -/

variable {A : Type u} [Category.{w} A] {FA : A → A → Type v} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

private noncomputable abbrev pullbackSheafifyStalkIso
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    ((TopCat.Presheaf.pullback A f).obj 𝒢.presheaf).stalk x ≅
      ((pullback A f).obj 𝒢).presheaf.stalk x := by
  let F := ((forget A Y ⋙ TopCat.Presheaf.pullback A f).obj 𝒢)
  let h : IsIso
      ((stalkFunctor A x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F)) := by
    simpa [F] using stalkFunctor_map_unit_toSheafify_isIso x A F
  exact
    @asIso _ _ _ _
      ((stalkFunctor A x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F)) h ≪≫
    ((stalkFunctor A x).mapIso ((forget A X).mapIso ((pullbackIso A f).app 𝒢))).symm

/-- Lemma 6.21.5: for a continuous map `f : X ⟶ Y`, a sheaf `𝒢` on `Y`, and a point `x : X`,
the canonical map on stalks identifies the stalk of `𝒢` at `f x` with the stalk of the inverse-
image sheaf at `x`. For the textbook statement take `A := Type u`; the same construction works for
any ambient category satisfying the hypotheses needed to form `TopCat.Sheaf.pullback`. -/
noncomputable abbrev stalkPullbackIso
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    𝒢.presheaf.stalk (f x) ≅ ((f⁻¹).obj 𝒢).presheaf.stalk x :=
  TopCat.Presheaf.stalkPullbackIso A f 𝒢.presheaf x ≪≫ pullbackSheafifyStalkIso f 𝒢 x

-- Proof sketch: unfold `stalkPullbackIso`; it is defined as the composite of the presheaf-level
-- stalk pullback isomorphism with the stalkwise comparison between presheaf pullback and sheaf
-- pullback.
/-- Unfolding `stalkPullbackIso` identifies it with the composite of the canonical presheaf stalk
comparison and the pullback-sheafification stalk comparison. -/
theorem stalkPullbackIso_def
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    stalkPullbackIso f 𝒢 x =
      TopCat.Presheaf.stalkPullbackIso A f 𝒢.presheaf x ≪≫ pullbackSheafifyStalkIso f 𝒢 x := by
  -- Unfold the abbreviation: the sheaf-level comparison is defined to be this composite.
  rfl

end TopCat.Sheaf

/-! ### Lemma_6_21_6 (from Chap06) -/
open CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe w v u

/- Domain-style sampling for Lemma 6.21.6:
- primary domain: inverse image functors on presheaves and sheaves over topological spaces;
- sampled owner declarations:
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `Adjunction.leftAdjointCompIso`,
  `Adjunction.conjugateEquiv_leftAdjointCompIso_inv`,
  and the raw definitional equality
  `TopCat.{Presheaf,Sheaf}.pushforward A (f ≫ g) =
    TopCat.{Presheaf,Sheaf}.pushforward A f ⋙
      TopCat.{Presheaf,Sheaf}.pushforward A g`;
- owner abstraction: the canonical owner is `Adjunction.leftAdjointCompIso`, applied to the
  pullback-pushforward adjunctions and the definitional equality of the right-adjoint
  pushforward functors under composition;
- primitive data: composable continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`;
- derived API: the source-facing comparison isomorphisms
  `TopCat.Sheaf.pullbackComp` and `TopCat.Presheaf.pullbackComp`.

Source/core/bridge triage:
- `source-facing`: inverse image along a composite continuous map agrees with the composite inverse
  image functor; the textbook item is the `Type u` specialization;
- `core/canonical`: `Adjunction.leftAdjointCompIso`;
- `bridge/view`: the namespace-specialized `pullbackComp` declarations below, kept because the
  immediate downstream files use this source-facing vocabulary directly. -/

/-- Helper for Lemma 6.21.6: if the composite right adjoint is definitionally equal to a given
right adjoint, then uniqueness of left adjoints yields the corresponding comparison isomorphism on
left adjoints. -/
private noncomputable def leftAdjointCompIsoOfEq
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)
    (h : G₂₀ = G₂₁ ⋙ G₁₀) :
    F₀₁ ⋙ F₁₂ ≅ F₀₂ :=
  -- Package the definitional equality of right adjoints as an isomorphism, then invoke
  -- uniqueness of left adjoints for the two adjunction presentations.
  Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ (eqToIso h.symm)

namespace TopCat.Sheaf

variable {A : Type u} [Category.{w} A] {FA : A → A → Type v} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- Lemma 6.21.6 (1), in canonical owner form: pullback of sheaves along a composite continuous
map is canonically isomorphic to the composite pullback functor. The Stacks statement is the
specialization `A = Type u`. -/
def pullbackComp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback A g ⋙ pullback A f ≅ pullback A (f ≫ g) :=
  -- Follow the source proof: both functors are left adjoint to the same pushforward functor,
  -- since pushforward along a composite is definitionally the composite pushforward.
  leftAdjointCompIsoOfEq
    (pullbackPushforwardAdjunction A g)
    (pullbackPushforwardAdjunction A f)
    (pullbackPushforwardAdjunction A (f ≫ g))
    (show pushforward A (f ≫ g) = pushforward A f ⋙ pushforward A g from rfl)

end TopCat.Sheaf

namespace TopCat.Presheaf

variable {C : Type u} [Category.{w} C] [HasColimits C]

/-- Lemma 6.21.6 (2), in canonical owner form: pullback of presheaves along a composite
continuous map is canonically isomorphic to the composite pullback functor. The Stacks statement
is the specialization `C = Type u`. -/
def pullbackComp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback C g ⋙ pullback C f ≅ pullback C (f ≫ g) :=
  -- The presheaf case is the same adjunction-uniqueness argument, now using the presheaf
  -- pullback-pushforward adjunctions.
  leftAdjointCompIsoOfEq
    (pullbackPushforwardAdjunction C g)
    (pullbackPushforwardAdjunction C f)
    (pullbackPushforwardAdjunction C (f ≫ g))
    (show pushforward C (f ≫ g) = pushforward C f ⋙ pushforward C g from rfl)

end TopCat.Presheaf

/-! ### Definition_6_21_7 (from Chap06) -/
universe u v

open CategoryTheory TopCat
open TopCat.Sheaf

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒢 : Y.Sheaf (Type v)) (ℱ : X.Sheaf (Type v))

/- Domain-style sampling for Definition 6.21.7:
- primary domain: pushforward of sheaves of sets along a continuous map, together with the
  pullback-pushforward adjunction on `TopCat.Sheaf`;
- sampled owner declarations:
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pushforward_sheaf_of_sheaf`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `TopCat.Presheaf.pushforward`;
- owner abstraction: the canonical owner for the direct-image sheaf is `TopCat.Sheaf.pushforward`,
  and the Stacks notion of an `f`-map is the resulting hom type into `f_* ℱ`;
- primitive data: only the continuous map `f` and the two sheaves `𝒢` and `ℱ`;
- derived API: the adjunction bijection and the explicit two-open-set description treated in the
  following lemma.

Source/core/bridge triage:
- `source-facing`: the textbook notion of an `f`-map from `𝒢` to `ℱ`;
- `core/canonical`: the owner functor `TopCat.Sheaf.pushforward`;
- `bridge/view`: the Hom-set adjunction
  `TopCat.Sheaf.pullbackPushforwardAdjunction`, and the compatible-family description in
  `Lemma_6_21_8`.

Since the source item is only naming the canonical morphism type into the direct image, this file
should remain a direct `#check` of that type expression rather than introducing a duplicate local
alias or wrapper. -/

/- Definition 6.21.7: for a continuous map `f : X ⟶ Y`, an `f`-map from a sheaf of sets `𝒢` on
`Y` to a sheaf of sets `ℱ` on `X` is exactly a morphism `𝒢 ⟶ f_* ℱ` of sheaves on `Y`. The
canonical mathlib expression for this notion is the following hom type. -/
#check (𝒢 ⟶ (pushforward (Type v) f).obj ℱ)

/-! ### Lemma_6_21_8 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace TopCat.Sheaf
open scoped AlgebraicGeometry

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe u v

/-
Domain-style sampling for Lemma 6.21.8:
- primary domain: sheaf pushforward along a continuous map and the pullback-pushforward adjunction
  on `TopCat.Sheaf`;
- sampled owner declarations:
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `TopCat.Presheaf.pushforward`,
  `CategoryTheory.CommSq`;
- owner abstraction: the canonical owner for an `f`-map is the Hom type
  `𝒢 ⟶ (pushforward (Type v) f).obj ℱ`, already fixed in `Definition_6_21_7`;
- primitive data: only the two-open-set family `η U V h`;
- derived API: the source/target `CommSq` naturality predicates, conversion to and from the
  canonical Hom type, the precomposition/postcomposition actions on compatible families, and the
  resulting equivalence with its naturality in both sheaf variables.

Source/core/bridge triage:
- `source-facing`: the Stacks-compatible family of maps `ξ_{U,V} : 𝒢(V) → ℱ(U)` for
  `U ⊆ f⁻¹(V)`;
- `core/canonical`: the sheaf pushforward owner `pushforward (Type v) f`;
- `bridge/view`: the equivalence between the compatible-family presentation and the canonical Hom
  type.

No upstream owner packages this two-open-set compatibility datum, so the bridge layer should remain
as a thin family type together with its compatibility predicates, not as a second bundled root API.
-/

/-- The explicit two-open-set family `ξ_{U,V} : 𝒢(V) → ℱ(U)` appearing in the fourth presentation
of Lemma 6.21.8, for opens `U ⊆ f⁻¹(V)`. Compatibility is recorded separately below. -/
abbrev ContinuousMapSheafMapFamily {X Y : TopCat.{u}} (f : X ⟶ Y)
    (𝒢 : Y.Sheaf (Type v)) (ℱ : X.Sheaf (Type v)) : Type (max u v) :=
  ∀ (U : Opens X) (V : Opens Y) (_ : U ≤ (Opens.map f).obj V),
    (𝒢.presheaf.obj (op V) ⟶ ℱ.presheaf.obj (op U))

section

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
variable {𝒢 : Y.Sheaf (Type v)} {ℱ : X.Sheaf (Type v)}
variable {𝒢' : Y.Sheaf (Type v)} {ℱ' : X.Sheaf (Type v)}

namespace ContinuousMapSheafMapFamily

/-- Compatibility with restriction in the `X`-variable. -/
def SourceNatural (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) : Prop :=
  ∀ {U U' : Opens X} {V : Opens Y} (i : U' ⟶ U) (h : U ≤ (Opens.map f).obj V),
    CommSq (η U V h) (𝟙 _) (ℱ.presheaf.map i.op) (η U' V (i.le.trans h))

/-- Compatibility with restriction in the `Y`-variable. -/
def TargetNatural (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) : Prop :=
  ∀ {U : Opens X} {V V' : Opens Y} (j : V ⟶ V') (h : U ≤ (Opens.map f).obj V),
    CommSq (𝒢.presheaf.map j.op) (η U V' (h.trans ((Opens.map f).map j).le)) (η U V h) (𝟙 _)

/-- The full compatibility condition for the fourth Stacks-style presentation. -/
def Compatible (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) : Prop :=
  η.SourceNatural ∧ η.TargetNatural

/-- Precompose a two-open-set family with a sheaf morphism in the `Y`-variable. -/
def precomp (α : 𝒢' ⟶ 𝒢) (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) :
    ContinuousMapSheafMapFamily f 𝒢' ℱ :=
  fun U V h ↦ α.1.app (op V) ≫ η U V h

/-- Postcompose a two-open-set family with a sheaf morphism in the `X`-variable. -/
def postcomp (β : ℱ ⟶ ℱ') (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) :
    ContinuousMapSheafMapFamily f 𝒢 ℱ' :=
  fun U V h ↦ η U V h ≫ β.1.app (op U)

/-- Source-side naturality is preserved by precomposition in the `Y`-variable. -/
theorem SourceNatural.precomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.SourceNatural) (α : 𝒢' ⟶ 𝒢) : (precomp α η).SourceNatural := by
  intro U U' V i h
  -- Left-whisker the original source-side square by the component of `α`.
  refine CommSq.mk ?_
  dsimp [precomp]
  simpa [Category.assoc] using
    congrArg (fun k => α.1.app (op V) ≫ k) (CommSq.w (hη i h))

/-- Target-side naturality is preserved by precomposition in the `Y`-variable. -/
theorem TargetNatural.precomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.TargetNatural) (α : 𝒢' ⟶ 𝒢) : (precomp α η).TargetNatural := by
  intro U V V' j h
  -- Move `α` past the restriction map using naturality, then apply the original square.
  have hα := α.1.naturality j.op
  have hη' :
      𝒢.presheaf.map j.op ≫ η U V h = η U V' (h.trans ((Opens.map f).map j).le) :=
    (hη (U := U) (V := V) (V' := V') j h).w
  refine CommSq.mk ?_
  calc
    𝒢'.presheaf.map j.op ≫ ContinuousMapSheafMapFamily.precomp α η U V h
        = α.1.app (op V') ≫ 𝒢.presheaf.map j.op ≫ η U V h := by
            dsimp [ContinuousMapSheafMapFamily.precomp]
            rw [← Category.assoc, hα, Category.assoc]
    _ = α.1.app (op V') ≫ η U V' (h.trans ((Opens.map f).map j).le) := by
            rw [hη']
    _ = α.1.app (op V') ≫ η U V' (h.trans ((Opens.map f).map j).le) ≫ 𝟙 _ := by
            simp
    _ = ContinuousMapSheafMapFamily.precomp α η U V' (h.trans ((Opens.map f).map j).le) ≫ 𝟙 _ := by
            rfl

/-- Source-side naturality is preserved by postcomposition in the `X`-variable. -/
theorem SourceNatural.postcomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.SourceNatural) (β : ℱ ⟶ ℱ') : (postcomp β η).SourceNatural := by
  intro U U' V i h
  -- Right-whisker the original source-side square by the component of `β`.
  refine CommSq.mk ?_
  dsimp [postcomp]
  simpa [Category.assoc] using
    congrArg (fun k => k ≫ β.1.app (op U')) (CommSq.w (hη i h))

/-- Target-side naturality is preserved by postcomposition in the `X`-variable. -/
theorem TargetNatural.postcomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.TargetNatural) (β : ℱ ⟶ ℱ') : (postcomp β η).TargetNatural := by
  intro U V V' j h
  -- Right-whisker the target-side square by the component of `β`.
  refine CommSq.mk ?_
  dsimp [postcomp]
  simpa [Category.assoc] using
    congrArg (fun k => k ≫ β.1.app (op U)) (CommSq.w (hη j h))

/-- Compatibility is preserved by precomposition in the `Y`-variable. -/
theorem Compatible.precomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.Compatible) (α : 𝒢' ⟶ 𝒢) : (precomp α η).Compatible :=
  ⟨SourceNatural.precomp hη.1 α, TargetNatural.precomp hη.2 α⟩

/-- Compatibility is preserved by postcomposition in the `X`-variable. -/
theorem Compatible.postcomp {η : ContinuousMapSheafMapFamily f 𝒢 ℱ}
    (hη : η.Compatible) (β : ℱ ⟶ ℱ') : (postcomp β η).Compatible :=
  ⟨SourceNatural.postcomp hη.1 β, TargetNatural.postcomp hη.2 β⟩

/-- Precomposition on compatible families in the source sheaf variable. -/
def precompCompatible (α : 𝒢' ⟶ 𝒢) :
    { η : ContinuousMapSheafMapFamily f 𝒢 ℱ // η.Compatible } →
      { η : ContinuousMapSheafMapFamily f 𝒢' ℱ // η.Compatible }
  | ⟨η, hη⟩ => ⟨precomp α η, hη.precomp α⟩

/-- Postcomposition on compatible families in the target sheaf variable. -/
def postcompCompatible (β : ℱ ⟶ ℱ') :
    { η : ContinuousMapSheafMapFamily f 𝒢 ℱ // η.Compatible } →
      { η : ContinuousMapSheafMapFamily f 𝒢 ℱ' // η.Compatible }
  | ⟨η, hη⟩ => ⟨postcomp β η, hη.postcomp β⟩

/-- The two-open-set family determined by an `f`-map of sheaves. -/
def ofHom (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) : ContinuousMapSheafMapFamily f 𝒢 ℱ :=
  fun _ V h ↦ ξ.1.app (op V) ≫ ℱ.presheaf.map (homOfLE h).op

/-- Converting a precomposition of sheaf maps to families matches family-level precomposition. -/
private theorem ofHom_precomp (α : 𝒢' ⟶ 𝒢) (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    ofHom (α ≫ ξ) = precomp α (ofHom ξ) := by
  -- Compare the two descriptions componentwise on each pair `(U, V)`.
  funext U V h
  rfl

/-- Converting a postcomposition of sheaf maps to families matches family-level postcomposition. -/
private theorem ofHom_postcomp (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) (β : ℱ ⟶ ℱ') :
    ofHom (ξ ≫ (pushforward (Type v) f).map β) = postcomp β (ofHom ξ) := by
  -- The pushforward map is componentwise postcomposition by `β`.
  funext U V h
  dsimp [ofHom, postcomp]
  calc
    (ξ ≫ (pushforward (Type v) f).map β).1.app (op V) ≫ ℱ'.presheaf.map (homOfLE h).op
        = ξ.1.app (op V) ≫ β.1.app (op ((Opens.map f).obj V)) ≫
            ℱ'.presheaf.map (homOfLE h).op := by
              rfl
    _ = ξ.1.app (op V) ≫ ℱ.presheaf.map (homOfLE h).op ≫ β.1.app (op U) := by
          simp [β.1.naturality (homOfLE h).op]

-- Proof sketch: expand both sides as iterated restriction maps in the presheaf `ℱ`; functoriality
-- of restrictions along inclusions of opens identifies the two composites.
/-- Restricting the collection attached to an `f`-map in the `X`-variable is compatible with the
restriction maps of `ℱ`. -/
private theorem ofHom_sourceNatural (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    (ofHom ξ).SourceNatural := by
  intro U U' V i h
  -- Both routes are successive restrictions in `ℱ`, so compose the inclusions of opens.
  refine CommSq.mk ?_
  dsimp [ofHom]
  rw [Category.assoc, ← Functor.map_comp]
  rw [show (homOfLE h).op ≫ i.op = (homOfLE (i.le.trans h)).op by rfl]
  simp

-- Proof sketch: use the naturality of the underlying morphism `ξ : 𝒢 ⟶ f_* ℱ`; after evaluating
-- the naturality square on a section `s`, postcompose with the restriction map from `f⁻¹(V)` to
-- `U`.
/-- The collection attached to an `f`-map is compatible with restriction in the `Y`-variable. -/
private theorem ofHom_targetNatural (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    (ofHom ξ).TargetNatural := by
  intro U V V' j h
  -- Start from naturality of `ξ` and then restrict from `f⁻¹(V)` to `U`.
  refine CommSq.mk ?_
  dsimp [ofHom]
  have hξ :
      𝒢.presheaf.map j.op ≫ ξ.1.app (op V) =
        ξ.1.app (op V') ≫ ((pushforward (Type v) f).obj ℱ).presheaf.map j.op :=
    ξ.1.naturality j.op
  rw [← Category.assoc]
  calc
    (𝒢.presheaf.map j.op ≫ ξ.1.app (op V)) ≫ ℱ.presheaf.map (homOfLE h).op
        = (ξ.1.app (op V') ≫ ((pushforward (Type v) f).obj ℱ).presheaf.map j.op) ≫
            ℱ.presheaf.map (homOfLE h).op := by
              exact congrArg (fun k => k ≫ ℱ.presheaf.map (homOfLE h).op) hξ
    _ = ξ.1.app (op V') ≫ ℱ.presheaf.map (homOfLE (h.trans ((Opens.map f).map j).le)).op := by
          rw [show ((pushforward (Type v) f).obj ℱ).presheaf.map j.op =
              ℱ.presheaf.map ((Opens.map f).map j).op by rfl]
          have hcomp :
              ℱ.presheaf.map ((Opens.map f).map j).op ≫ ℱ.presheaf.map (homOfLE h).op =
                ℱ.presheaf.map (homOfLE (h.trans ((Opens.map f).map j).le)).op := by
            rw [← Functor.map_comp]
            rfl
          simpa [Category.assoc] using congrArg (fun k => ξ.1.app (op V') ≫ k) hcomp

/-- The family attached to an `f`-map satisfies the Stacks compatibility conditions. -/
theorem ofHom_compatible (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    (ofHom ξ).Compatible :=
  ⟨ofHom_sourceNatural ξ, ofHom_targetNatural ξ⟩

-- Proof sketch: the target-side naturality of `η` with `U = f⁻¹(V)` and `U' = f⁻¹(V')` yields
-- the naturality square of the corresponding natural transformation `𝒢 ⟶ f_* ℱ`.
/-- The family `η_{U,V}` defines a natural transformation `𝒢 ⟶ f_* ℱ` by evaluating at
`U = f⁻¹(V)`. -/
private theorem toHom_naturality'
    (η : ContinuousMapSheafMapFamily f 𝒢 ℱ) (hηS : η.SourceNatural) (hηT : η.TargetNatural) :
    ∀ ⦃V V' : (Opens Y)ᵒᵖ⦄ (j : V ⟶ V'),
      𝒢.presheaf.map j ≫ η ((Opens.map f).obj (unop V')) (unop V') le_rfl =
        η ((Opens.map f).obj (unop V)) (unop V) le_rfl ≫
          ((pushforward (Type v) f).obj ℱ).presheaf.map j := by
  intro V V' j
  -- First move in the `Y`-variable, then identify the resulting restriction in `X`.
  calc
    𝒢.presheaf.map j ≫ η ((Opens.map f).obj (unop V')) (unop V') le_rfl
        = η ((Opens.map f).obj (unop V')) (unop V) (((Opens.map f).map j.unop).le) := by
            simpa using
              (hηT (U := (Opens.map f).obj (unop V')) (V := unop V')
                (V' := unop V) j.unop le_rfl).w
    _ = η ((Opens.map f).obj (unop V)) (unop V) le_rfl ≫
          ((pushforward (Type v) f).obj ℱ).presheaf.map j := by
            symm
            simpa using
              (hηS (U := (Opens.map f).obj (unop V))
                (U' := (Opens.map f).obj (unop V')) (V := unop V)
                ((Opens.map f).map j.unop) le_rfl).w

/-- Recover an `f`-map from a compatible family by evaluating it on `U = f⁻¹(V)`. -/
def toHom (η : ContinuousMapSheafMapFamily f 𝒢 ℱ)
    (hηS : η.SourceNatural) (hηT : η.TargetNatural) :
    𝒢 ⟶ (pushforward (Type v) f).obj ℱ :=
  ObjectProperty.homMk
    { app := fun V ↦ η ((Opens.map f).obj V.unop) V.unop le_rfl
      naturality := toHom_naturality' η hηS hηT }

-- Proof sketch: starting from `ξ`, evaluating on `U = f⁻¹(V)` and then restricting back along the
-- identity inclusion leaves each component unchanged; extensionality of sheaf morphisms finishes.
/-- Passing from an `f`-map to its compatible family and back recovers the original `f`-map. -/
private theorem hom_left_inv (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    toHom (ofHom ξ) (ofHom_sourceNatural ξ) (ofHom_targetNatural ξ) = ξ := by
  -- After evaluating at `V`, the extra restriction is along the identity inclusion.
  apply ObjectProperty.hom_ext
  ext V
  simp [toHom, ofHom]

-- Proof sketch: starting from `η`, evaluating at `U = f⁻¹(V)` and then restricting to a smaller
-- open `U ⊆ f⁻¹(V)` recovers `η_{U,V}` by the source-side naturality of `η`; extensionality of
-- collections gives equality.
/-- Passing from a compatible family to an `f`-map and back recovers the original family. -/
private theorem hom_right_inv (η : ContinuousMapSheafMapFamily f 𝒢 ℱ)
    (hηS : η.SourceNatural) (hηT : η.TargetNatural) :
    ofHom (toHom η hηS hηT) = η := by
  -- Evaluate at `f⁻¹(V)` and restrict back to `U`; source-side naturality gives the component.
  funext U V h
  simpa [ofHom, toHom] using CommSq.w (hηS (homOfLE h) le_rfl)

/-- Lemma 6.21.8: for a continuous map `f : X ⟶ Y`, the set of `f`-maps
`ξ : 𝒢 ⟶ f_* ℱ` is canonically equivalent to the set of compatible collections of maps
`ξ_{U,V} : 𝒢(V) → ℱ(U)` for opens `U ⊆ f⁻¹(V)`. Together with Definition 6.21.7 and the
canonical adjunction equivalence
`((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv 𝒢 ℱ).symm`, this yields the
four bijective descriptions in the Stacks statement; the companion theorems
`equiv_naturality_left` and `equiv_naturality_right` record functoriality in `𝒢` and `ℱ`. -/
noncomputable def equiv :
    (𝒢 ⟶ (pushforward (Type v) f).obj ℱ) ≃
      { η : ContinuousMapSheafMapFamily f 𝒢 ℱ // η.Compatible } where
  toFun := fun ξ ↦ ⟨ofHom ξ, ofHom_compatible ξ⟩
  invFun := fun η ↦ toHom η.1 η.2.1 η.2.2
  left_inv := hom_left_inv
  right_inv η := Subtype.ext (hom_right_inv η.1 η.2.1 η.2.2)

/-- The compatible-family equivalence is natural under precomposition on the source sheaf `𝒢`. -/
theorem equiv_naturality_left (α : 𝒢' ⟶ 𝒢) (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) :
    equiv (α ≫ ξ) = precompCompatible α (equiv ξ) := by
  apply Subtype.ext
  exact ofHom_precomp α ξ

/-- The compatible-family equivalence is natural under postcomposition on the target sheaf `ℱ`. -/
theorem equiv_naturality_right (ξ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ) (β : ℱ ⟶ ℱ') :
    equiv (ξ ≫ (pushforward (Type v) f).map β) = postcompCompatible β (equiv ξ) := by
  apply Subtype.ext
  exact ofHom_postcomp ξ β

end ContinuousMapSheafMapFamily

end

/-! ### Definition_6_21_9 (from Chap06) -/
universe u v

open CategoryTheory TopCat
open TopCat.Sheaf

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable {ℱ : X.Sheaf (Type v)} {𝒢 : Y.Sheaf (Type v)} {ℋ : Z.Sheaf (Type v)}
variable (φ : 𝒢 ⟶ (pushforward (Type v) f).obj ℱ)
variable (ψ : ℋ ⟶ (pushforward (Type v) g).obj 𝒢)

/- Domain-style sampling for Definition 6.21.9:
- primary domain: sheaf pushforward along continuous maps and morphisms into pushforwards;
- inspected owner declarations:
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pushforward_map`,
  `TopCat.Presheaf.pushforward`,
  `TopCat.Presheaf.Pushforward.comp`;
- owner abstraction: an `f`-map is already the canonical morphism type
  `𝒢 ⟶ (TopCat.Sheaf.pushforward (Type v) f).obj ℱ`, and composition is ordinary categorical
  composition together with `Functor.map`; the identification with a `(g ∘ f)`-map comes from the
  canonical presheaf-level comparison `TopCat.Presheaf.Pushforward.comp`, since sheaf pushforward is
  definitionally the underlying sheaf-category lift of presheaf pushforward;
- primitive data: continuous maps `f : X ⟶ Y`, `g : Y ⟶ Z`, and morphisms
  `φ : 𝒢 ⟶ f_* ℱ`, `ψ : ℋ ⟶ g_* 𝒢`;
- derived API: the induced `(g ∘ f)`-map, obtained by the canonical sheaf-pushforward owner.

Source/core/bridge triage:
- `source-facing`: Definition 6.21.9 names the composite of an `f`-map and a `g`-map;
- `core/canonical`: `TopCat.Sheaf.pushforward` together with ordinary composition in the sheaf
  category;
- `bridge/view`: the textbook phrase “the induced `(g ∘ f)`-map”, which is just the canonical term
  checked below and should not survive as a parallel wrapper definition. -/

/- Definition 6.21.9: after Definition 6.21.7 identifies an `f`-map with a morphism
`𝒢 ⟶ f_* ℱ`, and Lemma 6.21.2 identifies `(g ∘ f)_*` with the iterated pushforward `g_* ∘ f_*`,
the composite `(g ∘ f)`-map is the ordinary categorical composite below. -/
#check (ψ ≫ (pushforward (Type v) g).map φ :
  ℋ ⟶ (pushforward (Type v) (f ≫ g)).obj ℱ)

/-! ### Lemma_6_21_10 (from Chap06) -/
open CategoryTheory CategoryTheory.Limits TopCat TopCat.Presheaf TopCat.Sheaf
open AlgebraicGeometry

universe v u

noncomputable section

namespace TopCat.Sheaf

variable {A : Type u} [Category.{v} A] [HasColimits A]

/-- Helper for Lemma 6.21.10: package a sheaf on `X` as the corresponding sheafed space. -/
private abbrev toSheafedSpace {X : TopCat.{v}} (ℱ : X.Sheaf A) : SheafedSpace A :=
  { carrier := X
    presheaf := ℱ.presheaf
    IsSheaf := ℱ.2 }

/-- Helper for Lemma 6.21.10: turn an `f`-map of sheaves into the corresponding morphism of
sheafed spaces over `f`. -/
private abbrev toSheafedSpaceHom {X Y : TopCat.{v}} (f : X ⟶ Y) {ℱ : X.Sheaf A} {𝒢 : Y.Sheaf A}
    (φ : 𝒢 ⟶ (pushforward A f).obj ℱ) :
    ℱ.toSheafedSpace ⟶ 𝒢.toSheafedSpace :=
  InducedCategory.homMk { base := f, c := φ.1 }

/-- Helper for Lemma 6.21.10: the induced stalk map of an `f`-map of sheaves. -/
abbrev stalkMap {X Y : TopCat.{v}} (f : X ⟶ Y) {ℱ : X.Sheaf A} {𝒢 : Y.Sheaf A}
    (φ : 𝒢 ⟶ (pushforward A f).obj ℱ) (x : X) :
    𝒢.presheaf.stalk (f x) ⟶ ℱ.presheaf.stalk x :=
  (toSheafedSpaceHom f φ).hom.stalkMap x

end TopCat.Sheaf

/- Domain-style sampling for Lemma 6.21.10:
- primary domain: stalk functoriality for morphisms of sheafed spaces, specialized to sheaf
  morphisms into a pushforward along a continuous map, at the generic coefficient-category level;
- inspected owner declarations:
  `PresheafedSpace.Hom.stalkMap`,
  `PresheafedSpace.stalkMap.comp`,
  `RingedSpace.Hom.stalkMap`,
  `TopCat.Sheaf.pushforward`,
  `SheafedSpace`;
- owner abstraction: an `f`-map `φ : 𝒢 ⟶ f_* ℱ` is exactly the sheaf component of a morphism
  between the sheafed spaces attached to `ℱ` and `𝒢`; the internal bridge to
  `PresheafedSpace.Hom.stalkMap` is proof support only, while the public source-facing bridge
  owner is `TopCat.Sheaf.stalkMap`; its correct ambient level is the same generic coefficient
  category `A` used by the canonical owners, and the set-valued textbook statement is recovered by
  specializing `A := Type u`; composition is therefore derived from the canonical theorem
  `PresheafedSpace.stalkMap.comp`;
- primitive data: a continuous map `f : X ⟶ Y`, a sheaf morphism `φ : 𝒢 ⟶ f_* ℱ`, and a point
  `x : X`, with coefficients in a category `A` carrying the colimits needed for stalks;
- derived API: the source-facing owner `TopCat.Sheaf.stalkMap`, internally implemented via the
  bridge from an `f`-map to a morphism of sheafed spaces.

Source/core/bridge triage:
- `source-facing`: the induced stalk map `TopCat.Sheaf.stalkMap` and its compatibility with
  composition of `f`-maps;
- `core/canonical`: `PresheafedSpace.Hom.stalkMap` and
  `PresheafedSpace.stalkMap.comp`;
- `bridge/view`: the private conversion sending a sheaf `ℱ` on `X` to the sheafed space `(X, ℱ)`
  and an `f`-map `φ : 𝒢 ⟶ f_* ℱ` to the corresponding sheafed-space morphism with base `f`. -/

namespace TopCat.Sheaf

variable {A : Type u} [Category.{v} A] [HasColimits A]

/-- Lemma 6.21.10: for composable continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`, a coefficient
category `A` with the colimits needed for stalks, and `f`- and `g`-maps of `A`-valued sheaves,
the map on stalks of the composite `(φ ∘ ψ)` is the composition `ψ_{f(x)} ≫ φ_x`. The Stacks
Project statement is the specialization `A := Type u`. -/
theorem stalkMap_comp {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {ℱ : X.Sheaf A} {𝒢 : Y.Sheaf A} {ℋ : Z.Sheaf A}
    (φ : 𝒢 ⟶ (pushforward A f).obj ℱ) (ψ : ℋ ⟶ (pushforward A g).obj 𝒢) (x : X) :
    stalkMap (f ≫ g) (ψ ≫ (pushforward A g).map φ) x =
      stalkMap g ψ (f x) ≫ stalkMap f φ x := by
  -- Rewrite the textbook stalk maps through the sheafed-space bridge and apply the canonical
  -- composition theorem for stalk maps of morphisms of presheafed spaces.
  simpa only [stalkMap, toSheafedSpaceHom] using
    (PresheafedSpace.stalkMap.comp (toSheafedSpaceHom f φ).hom (toSheafedSpaceHom g ψ).hom x)

end TopCat.Sheaf
