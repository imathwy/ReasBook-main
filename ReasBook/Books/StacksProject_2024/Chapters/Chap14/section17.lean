import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_17_1 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite
open SSet.stdSimplex
open scoped Simplicial

noncomputable section

universe uC vC uS uI

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

/-- A `0`-simplex of a simplicial set induces a simplex in every degree by pulling back along the
unique map to `[0]`. -/
theorem nonempty_obj_of_nonempty_zero (U : SSet.{uS}) [Nonempty (U _⦋0⦌)]
    (Δ : SimplexCategoryᵒᵖ) : Nonempty (U.obj Δ) :=
  ⟨U.map (SimplexCategory.isTerminalZero.from Δ.unop).op (Classical.choice inferInstance)⟩

/-- Degreewise finite simplicial sets remain degreewise finite after tensoring with a standard
simplex. -/
instance degreewiseFinite_tensor_stdSimplex (U : SSet.{uS})
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] (n : ℕ) :
    ∀ Δ : SimplexCategoryᵒᵖ, Finite ((U ⊗ Δ[n]).obj Δ) := by
  intro Δ
  change Finite (U.obj Δ × (Δ[n] : SSet.{uS}).obj Δ)
  infer_instance

/-- If `U` has a `0`-simplex, then `U ⊗ Δ[n]` also has a `0`-simplex. -/
instance tensor_stdSimplex_objZero_nonempty (U : SSet.{uS}) [Nonempty (U _⦋0⦌)] (n : ℕ) :
    Nonempty ((U ⊗ Δ[n]) _⦋0⦌) := by
  change Nonempty (U _⦋0⦌ × (Δ[n] : SSet.{uS}) _⦋0⦌)
  exact ⟨Classical.choice inferInstance, obj₀Equiv.symm 0⟩

section FiniteNonemptyCoproducts

variable [HasBinaryCoproducts C]

omit [HasBinaryCoproducts C] in
private theorem hasCoproduct_singleton (f : Fin 1 → C) : HasCoproduct f := by
  let c : Cofan f :=
    Cofan.mk (f 0) (fun i ↦ eqToHom (by simpa using congrArg f (Subsingleton.elim i 0)))
  refine HasColimit.mk ⟨c, ?_⟩
  refine mkCofanColimit c (fun s ↦ s.ι.app ⟨0⟩) ?_ ?_
  · intro s j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [c, Cofan.inj]
  · intro s m h
    simpa [c, Cofan.inj] using h 0

/-- A finite nonempty family in a category with binary coproducts admits a coproduct. -/
private theorem hasCoproduct_finSucc (n : ℕ) (f : Fin (n + 1) → C) : HasCoproduct f := by
  induction n with
  | zero =>
      exact hasCoproduct_singleton f
  | succ n ih =>
      let tail : Fin (n + 1) → C := fun i ↦ f i.succ
      haveI : HasCoproduct tail := ih tail
      let c₁ : Cofan tail := colimit.cocone (Discrete.functor tail)
      let c₂ : BinaryCofan (f 0) c₁.pt := colimit.cocone (pair (f 0) c₁.pt)
      exact HasColimit.mk
        ⟨extendCofan c₁ c₂,
          extendCofanIsColimit f (colimit.isColimit (Discrete.functor tail))
            (colimit.isColimit (pair (f 0) c₁.pt))⟩

/-- A finite nonempty family in a category with binary coproducts has a coproduct. This is the
auxiliary existence route used later to construct simplicial copowers from degreewise finiteness
plus one `0`-simplex. -/
noncomputable instance hasCoproduct_of_finite_nonempty {ι : Type uI} [Finite ι] [Nonempty ι]
    (f : ι → C) : HasCoproduct f := by
  classical
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  cases n with
  | zero =>
      exfalso
      exact Fin.elim0 (e (Classical.choice inferInstance))
  | succ n =>
      let g : Fin (n + 1) → C := fun j ↦ f (e.symm j)
      haveI : HasCoproduct g := hasCoproduct_finSucc n g
      exact hasCoproduct_of_equiv_of_iso g f e (fun j ↦ eqToIso (by simp [g]))

/-- Degreewise finiteness plus a `0`-simplex is a sufficient route to the coproduct hypotheses
needed for the simplicial copower owner `U × X`. -/
instance simplicialCopower_hasCoproducts_of_finite_nonempty_zero (U : SSet.{uS})
    [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)] :
    ∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ) := by
  intro X Δ
  letI : Nonempty (U.obj Δ) := nonempty_obj_of_nonempty_zero U Δ
  infer_instance

end FiniteNonemptyCoproducts

section MappingObject

variable (U : SSet.{uS})
variable
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]

/-- The presheaf `W ↦ Mor(U × W, V)` on simplicial objects, assuming the chapter copower
`U × W` exists for every simplicial object `W`. -/
def simplicialHomPresheaf (V : SimplicialObject C) : (SimplicialObject C)ᵒᵖ ⥤ Type vC :=
  (simplicialCopowerFunctor U).op ⋙ yoneda.obj V

/- Source/core/bridge triage for Definition 14.17.1:
- sampled owner-style declarations in this domain:
  `simplicialCopower`,
  `simplicialCopowerFunctor`,
  `Functor.reprX`,
  `RepresentableBy.homEquiv`
- best owner abstraction: the simplicial mapping object `simplicialHom U V`
- `source-facing`: the mapping object `simplicialHom U V`
- `core/canonical`: the chosen representing object `(simplicialHomPresheaf U V).reprX`
  with representing data `(simplicialHomPresheaf U V).representableBy`
- `bridge/view`: the presheaf `simplicialHomPresheaf U V`
- primitive data: the bridge presheaf `simplicialHomPresheaf U V` together with the chapter owner
  hypothesis that the simplicial copower `U × W` exists for every simplicial object `W`
- auxiliary existence route: under binary coproducts, degreewise finiteness of `U` and one
  `0`-simplex supply those copower hypotheses through the instance
  `simplicialCopower_hasCoproducts_of_finite_nonempty_zero`
- derived API: the mapping object `simplicialHom U V`; its universal bijection is the canonical
  owner data `(simplicialHomPresheaf U V).representableBy.homEquiv`
- notation decision: the textbook surface `Hom(U, V)` clashes with ordinary morphism notation, and
  mathlib already reserves `SimplicialCategory.sHom` for simplicial categories, so the short owner
  name `simplicialHom` is the public surface here.
-/
/-- Definition 14.17.1: assuming the copowers `U × W` exist for simplicial objects `W`, when the
presheaf `W ↦ Mor(U × W, V)` is representable, its representing object is the simplicial mapping
object from `U` to `V`. -/
noncomputable abbrev simplicialHom (V : SimplicialObject C)
    [Functor.IsRepresentable (simplicialHomPresheaf U V)] :
    SimplicialObject C :=
  (simplicialHomPresheaf U V).reprX

/- Companion recall: the universal bijection for `simplicialHom U V` is already the canonical
owner data `(simplicialHomPresheaf U V).representableBy.homEquiv`; no parallel local wrapper is
needed. -/

end MappingObject

end CategoryTheory

/-! ### Lemma_14_17_2 (from Chap14) -/
open CategoryTheory.Limits
open scoped Simplicial

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.17.2:
- primary domain: representable presheaves obtained by restricting the simplicial mapping-object
  presheaf along constant simplicial objects;
- sampled owner-style declarations:
  `SimplicialObject.const`,
  `simplicialCopower_hasCoproducts_of_finite_nonempty_zero`,
  `simplicialHomPresheaf`,
  `Functor.IsRepresentable`;
- best owner abstraction: the ambient owner is `simplicialHomPresheaf U V`, while the present file
  is only its `C`-indexed `bridge/view` specialization along `SimplicialObject.const`;
- primitive data: the simplicial set `U`, the target simplicial object `V`, and the owner
  hypothesis that the simplicial copowers `U × W` exist for every simplicial object `W`;
- auxiliary source hypotheses: binary coproducts on `C`, degreewise finiteness of `U`, and a
  `0`-simplex of `U`, which only supply the owner hypothesis through
  `simplicialCopower_hasCoproducts_of_finite_nonempty_zero`;
- derived API: the representability statement for the constant-object restriction
  `(SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V` under the stronger source-facing
  hypotheses.

This file therefore deletes the parallel compatible-family model and reuses the upstream owner
construction directly. -/

variable {C : Type u} [Category.{v} C]

section Restriction

variable [HasBinaryCoproducts C]
variable (U : SSet.{w}) (V : SimplicialObject C)
variable [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)]

-- Proof sketch: this is the source-facing `C`-indexed specialization of the owner presheaf
-- `simplicialHomPresheaf U V`; the representability argument is unchanged, but now expressed on
-- the canonical restricted presheaf rather than a parallel compatible-family model.
/-- Lemma 14.17.2: assume `C` has binary coproducts and countable limits, and that `U` is
degreewise finite with a `0`-simplex. Then the presheaf `X ↦ Mor_{Simp(C)}(X × U, V)` is
representable. In Lean this presheaf is the constant-object restriction
`(SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V` of the owner presheaf
`simplicialHomPresheaf U V`. -/
theorem simplicialHomPresheaf_const_isRepresentable
    [HasCountableLimits C] :
    ((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable := sorry

attribute [instance] simplicialHomPresheaf_const_isRepresentable

end Restriction

end CategoryTheory

/-! ### Lemma_14_17_3 (from Chap14) -/
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open scoped Simplicial

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable [HasBinaryCoproducts C] [HasFiniteLimits C]

section Restriction

variable (U : SSet.{w}) (V : SimplicialObject C)
variable [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)]

/- Domain-style sampling for Lemma 14.17.3:
- primary domain: representability of the `C`-indexed restriction of the simplicial mapping-object
  presheaf under a finite-dimensionality hypothesis on the source simplicial set;
- sampled owner-style declarations:
  `Functor.IsRepresentable`,
  `simplicialHomPresheaf`,
  `(const C).op ⋙ simplicialHomPresheaf U V`,
  `SSet.HasDimensionLE`;
- best owner abstraction: the ambient owner remains `simplicialHomPresheaf U V`, while this lemma
  is the `source-facing` `bridge/view` statement for its restriction along constant simplicial
  objects, so it should not be collapsed to the later owner-level statement of Lemma `14.17.4`;
- primitive data: the simplicial set `U`, the simplicial object `V`, the direct degreewise-finite
  family on `U`, a `0`-simplex of `U`, and the chapter owner predicate
  `∃ d : ℕ, U.HasDimensionLE d`;
- derived API: representability of the restricted presheaf
  `(const C).op ⋙ simplicialHomPresheaf U V`, expressed with the canonical owner
  `((const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable`.
-/

-- Proof sketch: choose `d` with `U.HasDimensionLE d`, replace the indexing category from the proof
-- of `Lemma 14.17.2` by its finite full subcategory on simplices in degrees at most `2d`, and use
-- the initial-functor criterion from `Definition 4.17.3` and `Lemma 4.17.4` to identify the
-- resulting finite limit with the original compatible-family limit.
/-- Lemma 14.17.3: if `C` has binary coproducts and finite limits, if `U` is degreewise finite
with a `0`-simplex, and if all sufficiently high simplices of `U` are degenerate (formalized as
`∃ d : ℕ, U.HasDimensionLE d`), then the presheaf
`X ↦ Mor_{Simp(C)}(X × U, V)` is representable.
Here this presheaf is the constant-object restriction
`(const C).op ⋙ simplicialHomPresheaf U V` from Lemma 14.17.2. -/
theorem simplicialHomPresheaf_const_isRepresentable_of_eventually_degenerate
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    ((const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable := sorry

instance simplicialHomPresheaf_const_isRepresentable_of_fact_eventually_degenerate
    [Fact (∃ d : ℕ, U.HasDimensionLE d)] :
    ((const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable :=
  simplicialHomPresheaf_const_isRepresentable_of_eventually_degenerate U V Fact.out

end Restriction

end

end CategoryTheory

/-! ### Lemma_14_17_4 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.17.4:
- primary domain: representable simplicial mapping-object presheaves;
- sampled owner-style declarations:
  `Functor.IsRepresentable`,
  `Functor.representableBy`,
  `simplicialHomPresheaf`,
  `simplicialHom`;
- best owner abstraction: the source-facing owner remains `simplicialHomPresheaf U V`, and the
  file’s main content is the owner predicate `(simplicialHomPresheaf U V).IsRepresentable`;
- primitive data: the simplicial set `U`, the target simplicial object `V`, the degreewise
  finiteness family on `U`, a `0`-simplex of `U`, and the eventual degeneracy hypothesis;
- derived API: the source-facing representability theorem and its `Fact`-packaged instance.

Any later comparison between concrete representing objects should be expressed through the
canonical owner API `Functor.RepresentableBy.uniqueUpToIso` or `Functor.RepresentableBy.isoReprX`,
not by introducing a parallel local chosen-object wrapper here. -/

-- Proof sketch: evaluate the presheaf `W ↦ Mor(W × U, V)` degreewise at each simplex `[n]`.
-- Lemma `14.17.3` gives representability of the resulting `C`-valued presheaf
-- `X ↦ Mor(X × (U ⊗ Δ[n]), V)`, and Lemma `14.13.4` identifies maps out of `X × Δ[n]` with maps
-- into the `n`-th component, allowing these representing objects to assemble into a simplicial
-- object. This yields representability of `simplicialHomPresheaf U V`.
section EventuallyDegenerate

variable [HasBinaryCoproducts C] [HasFiniteLimits C]
variable (U : SSet.{w}) [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)]
variable (V : SimplicialObject C)

/-- Lemma 14.17.4: if `C` has binary coproducts and finite limits, if `U` is degreewise finite
with a `0`-simplex, and if all sufficiently high simplices of `U` are degenerate, then the presheaf
`W ↦ Mor_{Simp(C)}(W × U, V)` is representable. Equivalently, the simplicial mapping object
`simplicialHom U V` exists. -/
theorem simplicialHomPresheaf_isRepresentable_of_eventually_degenerate
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    (simplicialHomPresheaf U V).IsRepresentable := sorry

instance simplicialHomPresheaf_isRepresentable_of_fact_eventually_degenerate
    [Fact (∃ d : ℕ, U.HasDimensionLE d)] :
    (simplicialHomPresheaf U V).IsRepresentable :=
  simplicialHomPresheaf_isRepresentable_of_eventually_degenerate U V Fact.out

end EventuallyDegenerate

end CategoryTheory

/-! ### Lemma_14_17_5 (from Chap14) -/
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
