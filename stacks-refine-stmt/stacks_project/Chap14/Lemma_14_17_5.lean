import stacks_project.Chap14.Lemma_14_13_3
import stacks_project.Chap14.Lemma_14_17_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.17.5:
- primary domain: internal simplicial mapping objects and their contravariance in the source
  simplicial set, compared against pushouts and pullbacks in the functor category
  `SimplicialObject C`;
- sampled owner-style declarations:
  `simplicialHomPresheaf`,
  `simplicialHom`,
  `Functor.RepresentableBy.comp_homEquiv_symm`,
  `PullbackCone.IsLimit.equivPullbackObj`;
- best owner abstraction:
  the source-facing object `simplicialHom (pushout a b) T`, compared to the canonical pullback
  object of the precomposition maps
  `simplicial_hom_precomp a T` and `simplicial_hom_precomp b T`;
- primitive data:
  the precomposition morphisms on internal hom objects induced by simplicial-set maps;
- auxiliary existence route:
  under the chapter finiteness and eventual-degeneracy hypotheses, the required pushout-specific
  degreewise finiteness, `0`-simplex, and eventual-degeneracy facts are supplied below, while the
  owner-level coproduct and representability APIs are reused from earlier chapter files;
- derived API:
  the pushout closure bridge to
  `(simplicialHomPresheaf (pushout a b) T).IsRepresentable`, the pullback comparison morphism
  `simplicial_hom_pushout_to_pullback`, its `IsIso` theorem, and the companion hom-set bijection
  obtained by evaluating that pullback comparison at a test simplicial object.

Source/core/bridge triage:
- `source-facing`: `simplicialHom (pushout a b) T`, expressing that the internal hom out of a
  pushout is the expected mapping object from the source text;
- `core/canonical`: the pullback object
  `pullback (simplicial_hom_precomp a T) (simplicial_hom_precomp b T)` in `SimplicialObject C`;
- `bridge/view`: the explicit hom-set map into `Types.PullbackObj` for a test object `X`. -/

/-- Degreewise finiteness of the target legs induces degreewise finiteness of the simplicial
pushout. This is the source-facing finiteness bridge needed to apply Lemma `14.17.4` to
`pushout a b`. -/
instance degreewiseFinite_pushout
    {U V W : SSet.{w}}
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (V.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (W.obj Δ)]
    (a : U ⟶ V) (b : U ⟶ W) :
    ∀ Δ : SimplexCategoryᵒᵖ, Finite ((pushout a b).obj Δ) := by
  intro Δ
  let e₁ := pushoutObjIso a b Δ
  let e₂ : pushout (a.app Δ) (b.app Δ) ≅ Types.Pushout (a.app Δ) (b.app Δ) :=
    IsColimit.coconePointUniqueUpToIso (pushout.isColimit (a.app Δ) (b.app Δ))
      (Types.Pushout.isColimitCocone (a.app Δ) (b.app Δ))
  letI : Finite (Types.Pushout (a.app Δ) (b.app Δ)) := by
    change Finite (Quot (Types.Pushout.Rel (a.app Δ) (b.app Δ)))
    infer_instance
  exact Finite.of_equiv (Types.Pushout (a.app Δ) (b.app Δ)) ((e₁ ≪≫ e₂).symm.toEquiv)

/-- A `0`-simplex in the left target leg induces a `0`-simplex in the simplicial pushout. This is
the source-facing nonemptiness bridge needed to apply Lemma `14.17.4` to `pushout a b`. -/
instance pushout_objZero_nonempty
    {U V W : SSet.{w}}
    [Nonempty (V _⦋0⦌)]
    (a : U ⟶ V) (b : U ⟶ W) :
    Nonempty ((pushout a b) _⦋0⦌) := by
  let e₁ := pushoutObjIso a b (op ⦋0⦌)
  let e₂ : pushout (a.app (op ⦋0⦌)) (b.app (op ⦋0⦌)) ≅
      Types.Pushout (a.app (op ⦋0⦌)) (b.app (op ⦋0⦌)) :=
    IsColimit.coconePointUniqueUpToIso (pushout.isColimit (a.app (op ⦋0⦌)) (b.app (op ⦋0⦌)))
      (Types.Pushout.isColimitCocone _ _)
  exact ⟨(e₁ ≪≫ e₂).inv (Types.Pushout.inl _ _ (Classical.choice inferInstance))⟩

/-- Eventual degeneracy is preserved by pushouts of simplicial sets once both target legs are
eventually degenerate. -/
theorem simplicialSetEventuallyDegenerate_pushout
    {U V W : SSet.{w}}
    (hV : ∃ d : ℕ, V.HasDimensionLE d)
    (hW : ∃ d : ℕ, W.HasDimensionLE d)
    (a : U ⟶ V) (b : U ⟶ W) :
    ∃ d : ℕ, (pushout a b).HasDimensionLE d := sorry

/-- Under the chapter finiteness and eventual-degeneracy hypotheses on the two target legs, plus a
`0`-simplex in the left target leg, Lemma `14.17.4` applies to the simplicial pushout. This is the
public source-facing bridge from the hypotheses in the statement of Lemma `14.17.5` to the
owner-level internal-hom representability hypothesis on `pushout a b`. -/
theorem simplicialHomPresheaf_pushout_isRepresentable_of_eventually_degenerate
    [HasBinaryCoproducts C] [HasFiniteLimits C]
    {U V W : SSet.{w}}
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (V.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (W.obj Δ)]
    [Nonempty (V _⦋0⦌)]
    (hV : ∃ d : ℕ, V.HasDimensionLE d)
    (hW : ∃ d : ℕ, W.HasDimensionLE d)
    (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C) :
    (simplicialHomPresheaf (pushout a b) T).IsRepresentable := by
  let _ := degreewiseFinite_pushout a b
  let _ := pushout_objZero_nonempty a b
  exact simplicialHomPresheaf_isRepresentable_of_eventually_degenerate (pushout a b) T
    (simplicialSetEventuallyDegenerate_pushout hV hW a b)

instance simplicialHomPresheaf_pushout_isRepresentable_of_fact_eventually_degenerate
    [HasBinaryCoproducts C] [HasFiniteLimits C]
    {U V W : SSet.{w}}
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (V.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (W.obj Δ)]
    [Nonempty (V _⦋0⦌)]
    [Fact (∃ d : ℕ, V.HasDimensionLE d)]
    [Fact (∃ d : ℕ, W.HasDimensionLE d)]
    (a : U ⟶ V) (b : U ⟶ W)
    (T : SimplicialObject C) :
    (simplicialHomPresheaf (pushout a b) T).IsRepresentable :=
  simplicialHomPresheaf_pushout_isRepresentable_of_eventually_degenerate
    (Fact.out : ∃ d : ℕ, V.HasDimensionLE d)
    (Fact.out : ∃ d : ℕ, W.HasDimensionLE d) a b T

section Precomp

variable {U V : SSet.{w}} (a : U ⟶ V) (T : SimplicialObject C)
variable
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    [Functor.IsRepresentable (simplicialHomPresheaf U T)]
    [Functor.IsRepresentable (simplicialHomPresheaf V T)]

/-- Precomposition by a simplicial-set morphism induces the corresponding morphism of internal
simplicial mapping objects. This is the minimal bridge from the owner-level representing
equivalences to the source-facing precomposition map. -/
def simplicial_hom_precomp : simplicialHom V T ⟶ simplicialHom U T :=
  let eU :
      (simplicialHom V T ⟶ simplicialHom U T) ≃
        (U × simplicialHom V T ⟶ T) :=
    (simplicialHomPresheaf U T).representableBy.homEquiv
  let eV :
      (simplicialHom V T ⟶ simplicialHom V T) ≃
        (V × simplicialHom V T ⟶ T) :=
    (simplicialHomPresheaf V T).representableBy.homEquiv
  eU.symm (simplicialCopowerIndexHom (simplicialHom V T) a ≫ eV (𝟙 _))

-- Proof sketch: unfold `simplicial_hom_precomp`, then apply the canonical naturality lemma
-- `Functor.RepresentableBy.comp_homEquiv_symm` for the owner equivalence
-- `(simplicialHomPresheaf U T).representableBy.homEquiv`.
/-- Under the representing equivalence, composition with `simplicial_hom_precomp` is
precomposition on the coproduct-indexed source simplicial set. -/
theorem simplicial_hom_homEquiv_precomp
    (X : SimplicialObject C) (f : X ⟶ simplicialHom V T) :
    (simplicialHomPresheaf U T).representableBy.homEquiv (f ≫ simplicial_hom_precomp a T) =
      simplicialCopowerIndexHom X a ≫
        (simplicialHomPresheaf V T).representableBy.homEquiv f := sorry

end Precomp

section PushoutComparison

variable {U V W : SSet.{w}} (a : U ⟶ V) (b : U ⟶ W) (T : SimplicialObject C)
variable
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : W.obj Δ ↦ X.obj Δ)]
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : (pushout a b).obj Δ ↦ X.obj Δ)]
    [Functor.IsRepresentable (simplicialHomPresheaf U T)]
    [Functor.IsRepresentable (simplicialHomPresheaf V T)]
    [Functor.IsRepresentable (simplicialHomPresheaf W T)]
    [Functor.IsRepresentable (simplicialHomPresheaf (pushout a b) T)]

-- Proof sketch: both composites are induced by precomposition along the two maps
-- `U ⟶ pushout a b` obtained from the pushout cocone, and these agree because
-- `pushout.condition a b` gives the commutative square in the simplicial-set variable.
/-- Precomposition along the two structure maps of the simplicial pushout forms the canonical
commutative square over the two precomposition morphisms to `Hom(U, T)`. -/
theorem simplicial_hom_precomp_pushout_condition
    :
    CommSq
      (simplicial_hom_precomp (pushout.inl a b) T)
      (simplicial_hom_precomp (pushout.inr a b) T)
      (simplicial_hom_precomp a T)
      (simplicial_hom_precomp b T) := sorry

variable [HasPullback (simplicial_hom_precomp a T) (simplicial_hom_precomp b T)]

/-- The canonical comparison morphism from the internal hom out of a simplicial pushout to the
pullback of the two precomposition morphisms. -/
def simplicial_hom_pushout_to_pullback
    :
    simplicialHom (pushout a b) T ⟶
      pullback (simplicial_hom_precomp a T) (simplicial_hom_precomp b T) :=
  pullback.lift
    (simplicial_hom_precomp (pushout.inl a b) T)
    (simplicial_hom_precomp (pushout.inr a b) T)
    (simplicial_hom_precomp_pushout_condition a b T).w

/-- Lemma 14.17.5 in owner form: the internal hom out of a simplicial pushout is canonically the
pullback of the two precomposition morphisms. -/
theorem simplicial_hom_pushout_to_pullback_isIso
    :
    IsIso (simplicial_hom_pushout_to_pullback a b T) := sorry

section HomPullbackComparison

variable (X : SimplicialObject C)

local notation "homPullbackIsLimit" =>
  isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op X))
    (simplicial_hom_precomp a T) (simplicial_hom_precomp b T)

local notation "homPullbackEquiv" => PullbackCone.IsLimit.equivPullbackObj homPullbackIsLimit

/-- Evaluating the canonical pushout-to-pullback comparison isomorphism and then applying the
pullback universal-property equivalence on hom-sets. -/
noncomputable def simplicial_hom_pushout_hom_to_pullback
    :
    (X ⟶ simplicialHom (pushout a b) T) →
      Types.PullbackObj
        (fun f : X ⟶ simplicialHom V T ↦ f ≫ simplicial_hom_precomp a T)
        (fun g : X ⟶ simplicialHom W T ↦ g ≫ simplicial_hom_precomp b T) :=
  let _ := simplicial_hom_pushout_to_pullback_isIso a b T
  let i := asIso (simplicial_hom_pushout_to_pullback a b T)
  fun h ↦ homPullbackEquiv (h ≫ i.hom)

-- Proof sketch: for every test simplicial object `X`, use `simplicial_hom_homEquiv_precomp` to
-- identify morphisms `X ⟶ Hom(V ⨿[U] W, T)` with maps
-- `X × (V ⨿[U] W) ⟶ T`, then apply the pushout universal property from `Lemma 14.8.2` to rewrite
-- these as a pullback of the two mapping sets out of `X × V` and `X × W`.
/-- Lemma 14.17.5 in bridge form: once the internal mapping objects out of `U`, `V`, `W`, and the
simplicial pushout `V ⨿[U] W` exist and the pullback of the two precomposition morphisms exists,
the canonical map
`Hom(X, Hom(V ⨿[U] W, T)) → Hom(X, Hom(V, T)) ×_{Hom(X, Hom(U, T))} Hom(X, Hom(W, T))`
is bijective for every simplicial object `X`. Thus `Hom(V ⨿[U] W, T)` represents the fibre
product `Hom(V, T) ×_{Hom(U, T)} Hom(W, T)`. -/
-- Proof sketch: for every test simplicial object `X`, use `simplicial_hom_homEquiv_precomp` to
-- identify morphisms `X ⟶ Hom(V ⨿[U] W, T)` with maps
-- `X × (V ⨿[U] W) ⟶ T`, then apply the pushout universal property from `Lemma 14.8.2` to rewrite
-- these as a pullback of the two mapping sets out of `X × V` and `X × W`.
theorem simplicial_hom_pushout_hom_to_pullback_bijective
    :
    Function.Bijective (simplicial_hom_pushout_hom_to_pullback a b T X) := by
  let e := homPullbackEquiv
  let _ := simplicial_hom_pushout_to_pullback_isIso a b T
  let i := asIso (simplicial_hom_pushout_to_pullback a b T)
  change Function.Bijective (fun h ↦ e (h ≫ i.hom))
  refine e.bijective.comp ?_
  refine ⟨?_, ?_⟩
  · intro f g hfg
    have := congrArg (fun k ↦ k ≫ i.inv) hfg
    simpa [Category.assoc] using this
  · intro h
    refine ⟨h ≫ i.inv, ?_⟩
    simp [Category.assoc]

end HomPullbackComparison

end PushoutComparison

end CategoryTheory
