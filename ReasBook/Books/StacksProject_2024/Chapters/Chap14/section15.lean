import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_15_1 (from Chap14) -/
open Opposite
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type w} [Category.{w} D]
variable (U : D ⥤ Type w) (V : Dᵒᵖ ⥤ C)
variable [∀ d : D, HasProductsOfShape (U.obj d) C]

/-
Domain-style sampling for Definition 14.15.1:
- primary domain: source-facing cotensors of a presheaf by a set-valued copresheaf, implemented
  degreewise by categorical products;
- inspected owner declarations:
  `CategoryTheory.Limits.piObj`,
  `CategoryTheory.Limits.Pi.π`,
  `CategoryTheory.Limits.Pi.map'`,
  `CategoryTheory.evaluationRightAdjoint`;
- target layer: `source-facing`;
- owner abstraction:
  the public owner here is the source-facing presheaf `homFromCosimplicialSet U V`, but its
  minimal canonical implementation under the source assumptions is the degreewise product functor
  assembled from mathlib's product owner `∏ᶜ` and the reindexing map `Pi.map'`;
- primitive-vs-derived split:
  primitive data are the indexing category `D`, the set-valued copresheaf `U`, the presheaf `V`,
  and the product-shape hypotheses `[HasProductsOfShape (U.obj d) C]`;
  the product objects and their reindexing maps are derived from `∏ᶜ`, `Pi.map'`, and the
  composition/projection formulas `Pi.map'_comp_map'` and `Pi.map'_comp_π`;
  the source's degreewise finiteness and nonemptiness are sufficient conditions for these product
  shapes to exist, but they are not primitive data of the canonical owner and therefore do not
  belong in the refined public API;
  the object and structure-map formulas themselves are definitional data of the owner, so the
  refined public API keeps only the source-facing owner together with the projection square and
  morphism-level naturality bridge.
- notation decision:
  the obvious textbook surfaces `Hom(U, V)` and exponent-style notation are too ambiguous here,
  since they clash with ordinary morphism notation and internal-hom/exponential readings in Lean;
  the short owner name `homFromCosimplicialSet` is therefore kept as the public surface.

Source/core/bridge triage:
- `source-facing`: `homFromCosimplicialSet U V`;
- `core/canonical`: the degreewise product object
  `Δ ↦ ∏ᶜ (fun _ : U.obj (unop Δ) ↦ V.obj Δ)` with structure maps
  `Pi.map' (U.map f.unop) (fun _ ↦ V.map f)`;
- `bridge/view`: `homFromCosimplicialSet_map_π`.
-/

/-- Definition 14.15.1: assuming the products indexed by the sets `U.obj d` exist in `C`,
`homFromCosimplicialSet U V` is the presheaf whose value at `Δ : Dᵒᵖ` is the product of
`U.obj (unop Δ)` copies of `V.obj Δ`, with structure maps induced by precomposition with `U` and
postcomposition with `V`. -/
def homFromCosimplicialSet : Dᵒᵖ ⥤ C where
  obj Δ := ∏ᶜ (fun _ : U.obj (unop Δ) ↦ V.obj Δ)
  map f := Pi.map' (U.map f.unop) (fun _ ↦ V.map f)
  map_id Δ := by
    ext u
    simp
  map_comp {Δ₁ Δ₂ Δ₃} f g := by
    ext u
    simp [Category.assoc]

/-- The structure map of `homFromCosimplicialSet U V` and the corresponding projections form the
canonical commutative square induced by reindexing on `U` and the presheaf structure map on
`V`. -/
theorem homFromCosimplicialSet_map_π
    {Δ₁ Δ₂ : Dᵒᵖ} (f : Δ₁ ⟶ Δ₂) (u : U.obj (unop Δ₂)) :
    CommSq
      ((homFromCosimplicialSet U V).map f)
      (Pi.π (fun _ : U.obj (unop Δ₁) ↦ V.obj Δ₁) (U.map f.unop u))
      (Pi.π (fun _ : U.obj (unop Δ₂) ↦ V.obj Δ₂) u)
      (V.map f) := by
  refine ⟨?_⟩
  simpa [homFromCosimplicialSet] using
    (Pi.map'_comp_π (U.map f.unop) (fun _ ↦ V.map f) u)

/-- A morphism into `homFromCosimplicialSet U V` is componentwise natural with respect to the
indexing morphisms. -/
theorem homFromCosimplicialSet_hom_naturality
    {X : Dᵒᵖ ⥤ C}
    (h : X ⟶ homFromCosimplicialSet U V)
    {Δ₁ Δ₂ : Dᵒᵖ} (f : Δ₁ ⟶ Δ₂) (u : U.obj (unop Δ₂)) :
    CommSq
      (X.map f)
      (h.app Δ₁ ≫ Pi.π (fun _ : U.obj (unop Δ₁) ↦ V.obj Δ₁) (U.map f.unop u))
      (h.app Δ₂ ≫ Pi.π (fun _ : U.obj (unop Δ₂) ↦ V.obj Δ₂) u)
      (V.map f) := by
  simpa using
    (CommSq.vert_comp
      (CommSq.mk (h.naturality f))
      (homFromCosimplicialSet_map_π U V f u))

section Coyoneda

variable {E : Type w} [Category.{w} E]
variable (d : E)
variable [∀ a : E, HasProductsOfShape ((coyoneda.obj (op d)).obj a) C]
variable [∀ a b : Eᵒᵖ, HasProductsOfShape (a ⟶ b) C]

private noncomputable def homFromCoyonedaEvaluationComponent
    (X : C) (Δ : Eᵒᵖ) :
    (homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X)).obj Δ ≅
      ((evaluationRightAdjoint C (op d)).obj X).obj Δ where
  hom :=
    Pi.lift (fun g : Δ ⟶ op d ↦
      Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (op d)) g))
  inv :=
    Pi.lift (fun g : (coyoneda.obj (op d)).obj (unop Δ) ↦
      Pi.π (fun _ : Δ ⟶ op d ↦ X) ((opEquiv Δ (op d)).symm g))
  hom_inv_id := by
    apply Pi.hom_ext
    intro g
    have h₁ :=
      congrArg
        (fun t ↦
          Pi.lift (fun g : Δ ⟶ op d ↦
              Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X)
                ((opEquiv Δ (op d)) g)) ≫
            t)
        (Pi.lift_π
          (fun g : (coyoneda.obj (op d)).obj (unop Δ) ↦
            Pi.π (fun _ : Δ ⟶ op d ↦ X) ((opEquiv Δ (op d)).symm g))
          g)
    have h₂ :=
      Pi.lift_π
        (fun g : Δ ⟶ op d ↦
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X)
            ((opEquiv Δ (op d)) g))
        ((opEquiv Δ (op d)).symm g)
    have h₁' := by simpa [Category.assoc] using h₁
    have h₂' := by simpa [Category.assoc] using h₂
    have hcomp := h₁'.trans h₂'
    have hid :
        Pi.π
            (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ ((Functor.const Eᵒᵖ).obj X).obj Δ)
            g =
          𝟙 ((homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X)).obj Δ) ≫
            Pi.π
              (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ ((Functor.const Eᵒᵖ).obj X).obj Δ)
              g := by
      simpa [homFromCosimplicialSet] using (Category.id_comp
        (Pi.π
          (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ ((Functor.const Eᵒᵖ).obj X).obj Δ)
          g)).symm
    convert hcomp.trans hid using 1 <;> simp [Category.assoc, homFromCosimplicialSet]
  inv_hom_id := by
    apply Pi.hom_ext
    intro g
    have h₁ :=
      congrArg
        (fun t ↦
          Pi.lift (fun g : (coyoneda.obj (op d)).obj (unop Δ) ↦
              Pi.π (fun _ : Δ ⟶ op d ↦ X) ((opEquiv Δ (op d)).symm g)) ≫
            t)
        (Pi.lift_π
          (fun g : Δ ⟶ op d ↦
            Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X)
              ((opEquiv Δ (op d)) g))
          g)
    have h₂ :=
      Pi.lift_π
        (fun g : (coyoneda.obj (op d)).obj (unop Δ) ↦
          Pi.π (fun _ : Δ ⟶ op d ↦ X) ((opEquiv Δ (op d)).symm g))
        ((opEquiv Δ (op d)) g)
    have h₁' := by simpa [Category.assoc] using h₁
    have h₂' := by simpa [Category.assoc] using h₂
    simpa using h₁'.trans h₂'

/-- For a representable copresheaf, `homFromCosimplicialSet` is canonically the evaluation right
adjoint at the representing object. -/
noncomputable def homFromCoyonedaIsoEvaluationRightAdjoint (X : C) :
    homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X) ≅
      (evaluationRightAdjoint C (op d)).obj X :=
  NatIso.ofComponents
    (homFromCoyonedaEvaluationComponent d X)
    (by
      intro Δ₁ Δ₂ f
      apply Pi.hom_ext
      intro g
      have h₁ :
          (homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X)).map f ≫
              (homFromCoyonedaEvaluationComponent d X Δ₂).hom ≫
              Pi.π (fun _ : Δ₂ ⟶ op d ↦ X) g
            =
          (homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X)).map f ≫
            Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₂) ↦ X)
              ((opEquiv Δ₂ (op d)) g) := by
        simpa [homFromCoyonedaEvaluationComponent, Category.assoc] using
          congrArg
            (fun k ↦
              (homFromCosimplicialSet (coyoneda.obj (op d))
                ((Functor.const Eᵒᵖ).obj X)).map f ≫ k)
            (Pi.lift_π
              (fun g : Δ₂ ⟶ op d ↦
                Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₂) ↦ X)
                  ((opEquiv Δ₂ (op d)) g))
              g)
      have h₂ :
          (homFromCosimplicialSet (coyoneda.obj (op d)) ((Functor.const Eᵒᵖ).obj X)).map f ≫
              Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₂) ↦ X)
                ((opEquiv Δ₂ (op d)) g)
            =
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₁) ↦ X)
            (((coyoneda.obj (op d)).map f.unop) ((opEquiv Δ₂ (op d)) g)) := by
        simpa [Category.assoc] using
          (homFromCosimplicialSet_map_π
            (coyoneda.obj (op d))
            ((Functor.const Eᵒᵖ).obj X)
            f
            ((opEquiv Δ₂ (op d)) g)).w
      have h₃ :
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₁) ↦ X)
              (((coyoneda.obj (op d)).map f.unop) ((opEquiv Δ₂ (op d)) g))
            =
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₁) ↦ X)
            ((opEquiv Δ₁ (op d)) (f ≫ g)) := by
        rfl
      have h₄ :
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₁) ↦ X)
              ((opEquiv Δ₁ (op d)) (f ≫ g))
            =
          (homFromCoyonedaEvaluationComponent d X Δ₁).hom ≫
            Pi.π (fun _ : Δ₁ ⟶ op d ↦ X) (f ≫ g) := by
        simpa [homFromCoyonedaEvaluationComponent, Category.assoc] using
          (Pi.lift_π
            (fun g : Δ₁ ⟶ op d ↦
              Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ₁) ↦ X)
                ((opEquiv Δ₁ (op d)) g))
            (f ≫ g)).symm
      have h₅ :
          Pi.π (fun _ : Δ₁ ⟶ op d ↦ X) (f ≫ g) =
            ((evaluationRightAdjoint C (op d)).obj X).map f ≫
              Pi.π (fun _ : Δ₂ ⟶ op d ↦ X) g := by
        dsimp [evaluationRightAdjoint]
        exact
          (Pi.lift_π
            (fun g' : Δ₂ ⟶ op d ↦
              Pi.π (fun _ : Δ₁ ⟶ op d ↦ X) (f ≫ g'))
            g).symm
      have h₆ :
          (homFromCoyonedaEvaluationComponent d X Δ₁).hom ≫
              Pi.π (fun _ : Δ₁ ⟶ op d ↦ X) (f ≫ g)
            =
          (homFromCoyonedaEvaluationComponent d X Δ₁).hom ≫
            ((evaluationRightAdjoint C (op d)).obj X).map f ≫
              Pi.π (fun _ : Δ₂ ⟶ op d ↦ X) g := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ (homFromCoyonedaEvaluationComponent d X Δ₁).hom ≫ k) h₅
      simpa [Category.assoc] using h₁.trans (h₂.trans (h₃.trans (h₄.trans h₆))))

/-- On each component, `homFromCoyonedaIsoEvaluationRightAdjoint` reindexes the product factors by
the canonical equivalence between arrows into `op d` and arrows out of `d`. -/
theorem homFromCoyonedaIsoEvaluationRightAdjoint_hom_app_π
    (X : C) (Δ : Eᵒᵖ) (g : Δ ⟶ op d) :
    (homFromCoyonedaIsoEvaluationRightAdjoint d X).hom.app Δ ≫
        Pi.π (fun _ : Δ ⟶ op d ↦ X) g =
      Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (op d)) g) := by
  change
    Pi.lift
        (fun g' : Δ ⟶ op d ↦
          Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X)
            ((opEquiv Δ (op d)) g')) ≫
      Pi.π (fun _ : Δ ⟶ op d ↦ X) g =
    Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (op d)) g)
  simpa using
    Pi.lift_π
      (fun g' : Δ ⟶ op d ↦
        Pi.π (fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (op d)) g'))
      g

end Coyoneda

end CategoryTheory

/-! ### Lemma_14_15_2 (from Chap14) -/
open Opposite
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Truncated
open SimplexCategory.Truncated.Hom
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.15.2:
- primary domain: simplicial objects defined from a costandard simplex and the right adjoint to
  evaluation at a simplex;
- sampled owner API:
  `homFromCosimplicialSet`,
  `homFromCoyonedaIsoEvaluationRightAdjoint`,
  `coyoneda.obj`,
  `truncation`,
  `evaluationRightAdjoint`,
  `evaluationAdjunctionLeft`;
- source/core/bridge triage:
  `source-facing`: the specialization of `homFromCosimplicialSet` to the costandard simplex
    `C[k] = coyoneda.obj (op ⦋k⦌)`, viewed as a functor `X ↦ Hom(C[k], X)`, together with its
    `k`-truncation;
  `core/canonical`: the right adjoint to evaluation at `op ⦋k⦌` in simplicial objects, and at the
    terminal truncated simplex `op ⦋k, le_rfl⦌ₖ` in `k`-truncated
    simplicial objects;
  `bridge/view`: the natural isomorphism from the source-facing functor to
    `evaluationRightAdjoint`, together with the induced Hom-set equivalence and its explicit
    identity-simplex projection formula, and the same bridge after `k`-truncation.

Primitive data are only the simplex `[k]` and the object `X`. The source-facing construction is
already owned upstream by `homFromCosimplicialSet`; the product formula and universal bijection are
derived API of that owner and of the canonical evaluation adjunction.
-/

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

private instance finiteOpHom {D : Type*} [Category D] [∀ a b : D, Finite (a ⟶ b)]
    (a b : Dᵒᵖ) : Finite (a ⟶ b) :=
  Finite.of_equiv (unop b ⟶ unop a) (opEquiv _ _).symm

private instance finiteTruncatedSimplexHom {k : ℕ} (a b : SimplexCategory.Truncated k) :
    Finite (a ⟶ b) := by
  refine Finite.of_injective (fun f ↦ f.hom) ?_
  intro f g h
  exact ObjectProperty.hom_ext _ h

private instance finiteCoyonedaObj
    {D : Type*} [Category D] [∀ a b : D, Finite (a ⟶ b)] (d a : D) :
    Finite ((coyoneda.obj (op d)).obj a) := by
  change Finite (d ⟶ a)
  infer_instance

private instance finiteCostandardSimplexObj (k : ℕ) (Δ : SimplexCategory) :
    Finite ((C[k] : CosimplicialObject (Type)).obj Δ) :=
  finiteCoyonedaObj ⦋k⦌ Δ

private abbrev topTruncatedSimplex (k : ℕ) : SimplexCategory.Truncated k := ⦋k, le_rfl⦌ₖ

/-- The canonical Hom-set equivalence for `Hom(C[k], X)` is the evaluation adjunction transported
across the canonical representable-owner isomorphism. -/
noncomputable def homFromCostandardSimplex_homEquiv (k : ℕ) (X : C) (V : SimplicialObject C) :
    (V ⟶ homFromCosimplicialSet C[k] ((SimplicialObject.const C).obj X)) ≃
      (V _⦋k⦌ ⟶ X) := by
  exact ((Iso.refl V).homCongr (homFromCoyonedaIsoEvaluationRightAdjoint ⦋k⦌ X)).trans
    (((evaluationAdjunctionLeft C (op ⦋k⦌)).homEquiv V X).symm)

omit [HasFiniteProducts C] in
private theorem evaluationRightAdjoint_homEquiv_apply
    {D : Type*} [Category D] [∀ a b : Dᵒᵖ, HasProductsOfShape (a ⟶ b) C]
    (d : D) (X : C) (V : Dᵒᵖ ⥤ C)
    (γ : V ⟶ (evaluationRightAdjoint C (op d)).obj X) :
    ((evaluationAdjunctionLeft C (op d)).homEquiv V X).symm γ =
      γ.app (op d) ≫ Pi.π (fun _ ↦ X) (𝟙 _) := by
  rw [Adjunction.homEquiv_symm_apply, evaluationAdjunctionLeft_counit_app]
  simp

/-- The canonical equivalence of `Hom(C[k], X)` evaluates a simplicial morphism at degree `k`
and projects to the identity-indexed factor. -/
theorem homFromCostandardSimplex_homEquiv_apply (k : ℕ) (X : C) (V : SimplicialObject C)
    (γ : V ⟶ homFromCosimplicialSet C[k] ((SimplicialObject.const C).obj X)) :
    homFromCostandardSimplex_homEquiv k X V γ =
      γ.app (op ⦋k⦌) ≫ Pi.π (fun _ ↦ X) (𝟙 _) := by
  change
    ((evaluationAdjunctionLeft C (op ⦋k⦌)).homEquiv V X).symm
        (((Iso.refl V).homCongr (homFromCoyonedaIsoEvaluationRightAdjoint ⦋k⦌ X)) γ) =
      γ.app (op ⦋k⦌) ≫ Pi.π (fun _ ↦ X) (𝟙 _)
  simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
  have hcore :
      ((evaluationAdjunctionLeft C (op ⦋k⦌)).homEquiv V X).symm
          (γ ≫ (homFromCoyonedaIsoEvaluationRightAdjoint ⦋k⦌ X).hom) =
        γ.app (op ⦋k⦌) ≫
          (homFromCoyonedaIsoEvaluationRightAdjoint ⦋k⦌ X).hom.app (op ⦋k⦌) ≫
          Pi.π (fun _ ↦ X) (𝟙 _) := by
    simpa [Category.assoc] using
      evaluationRightAdjoint_homEquiv_apply ⦋k⦌ X V
        (γ ≫ (homFromCoyonedaIsoEvaluationRightAdjoint ⦋k⦌ X).hom)
  exact hcore.trans <| by
    simpa [Category.assoc] using
      congrArg (fun t ↦ γ.app (op ⦋k⦌) ≫ t)
        (homFromCoyonedaIsoEvaluationRightAdjoint_hom_app_π ⦋k⦌ X (op ⦋k⦌) (𝟙 _))

private abbrev truncatedCostandardSimplexIndexEquiv (k : ℕ)
    (Δ : SimplexCategory.Truncated k) :
    (C[k] : CosimplicialObject (Type)).obj Δ.obj ≃
      (coyoneda.obj (op (topTruncatedSimplex k))).obj Δ where
  toFun f := ObjectProperty.homMk f
  invFun f := f.hom
  left_inv f := rfl
  right_inv f := by
    exact ObjectProperty.hom_ext _ rfl

private theorem truncatedCostandardSimplexIndexEquiv_naturality (k : ℕ)
    {Δ₁ Δ₂ : SimplexCategory.Truncated k} (f : Δ₂ ⟶ Δ₁)
    (g : (coyoneda.obj (op (topTruncatedSimplex k))).obj Δ₂) :
    (C[k] : CosimplicialObject (Type)).map f.hom
        ((truncatedCostandardSimplexIndexEquiv k Δ₂).symm g) =
      (truncatedCostandardSimplexIndexEquiv k Δ₁).symm
        ((coyoneda.obj (op (topTruncatedSimplex k))).map f g) := by
  rfl

private noncomputable def truncationHomFromCostandardSimplexIso (k : ℕ) (X : C) :
    (truncation k).obj
      (homFromCosimplicialSet C[k] ((SimplicialObject.const C).obj X)) ≅
    homFromCosimplicialSet
      (coyoneda.obj (op (topTruncatedSimplex k)))
      ((Functor.const (SimplexCategory.Truncated k)ᵒᵖ).obj X) :=
  NatIso.ofComponents
    (fun Δ ↦ Pi.reindex (truncatedCostandardSimplexIndexEquiv k (unop Δ)) (fun _ ↦ X))
    (fun {Δ₁ Δ₂} f ↦ by
      apply Pi.hom_ext
      intro g
      let φ := f.unop.hom
      have h₁ :
          (((truncation k).obj
                (homFromCosimplicialSet C[k] ((SimplicialObject.const C).obj X))).map f ≫
              (Pi.reindex
                  (truncatedCostandardSimplexIndexEquiv k (unop Δ₂))
                  (fun _ ↦ X)).hom) ≫
            Pi.π (fun _ ↦ X) g =
          ((truncation k).obj
              (homFromCosimplicialSet C[k] ((SimplicialObject.const C).obj X))).map f ≫
            Pi.π (fun _ ↦ X) ((truncatedCostandardSimplexIndexEquiv k (unop Δ₂)).symm g) := by
        simpa only [Category.assoc, Equiv.apply_symm_apply] using
          congrArg
            (fun t ↦
              ((truncation k).obj
                  (homFromCosimplicialSet C[k] ((SimplicialObject.const C).obj X))).map f ≫
                t)
            (Pi.reindex_hom_π
              (truncatedCostandardSimplexIndexEquiv k (unop Δ₂))
              (fun _ ↦ X)
              ((truncatedCostandardSimplexIndexEquiv k (unop Δ₂)).symm g))
      have h₂ :
          ((truncation k).obj
              (homFromCosimplicialSet C[k] ((SimplicialObject.const C).obj X))).map f ≫
            Pi.π (fun _ ↦ X) ((truncatedCostandardSimplexIndexEquiv k (unop Δ₂)).symm g) =
          Pi.π (fun _ ↦ X)
            ((C[k] : CosimplicialObject (Type)).map φ
              ((truncatedCostandardSimplexIndexEquiv k (unop Δ₂)).symm g)) := by
        simpa [SimplicialObject.truncation] using
          (homFromCosimplicialSet_map_π
            C[k]
            ((SimplicialObject.const C).obj X)
            φ.op
            ((truncatedCostandardSimplexIndexEquiv k (unop Δ₂)).symm g)).w
      have h₃ :
          Pi.π (fun _ ↦ X)
            ((C[k] : CosimplicialObject (Type)).map φ
              ((truncatedCostandardSimplexIndexEquiv k (unop Δ₂)).symm g)) =
          Pi.π (fun _ ↦ X)
            ((truncatedCostandardSimplexIndexEquiv k (unop Δ₁)).symm
              ((coyoneda.obj (op (topTruncatedSimplex k))).map f.unop g)) := by
        rw [truncatedCostandardSimplexIndexEquiv_naturality]
      have h₄ :
          Pi.π (fun _ ↦ X)
            ((truncatedCostandardSimplexIndexEquiv k (unop Δ₁)).symm
              ((coyoneda.obj (op (topTruncatedSimplex k))).map f.unop g)) =
          (Pi.reindex
              (truncatedCostandardSimplexIndexEquiv k (unop Δ₁))
              (fun _ ↦ X)).hom ≫
            Pi.π (fun _ ↦ X) ((coyoneda.obj (op (topTruncatedSimplex k))).map f.unop g) := by
        symm
        simpa [Category.assoc] using
          (Pi.reindex_hom_π
            (truncatedCostandardSimplexIndexEquiv k (unop Δ₁))
            (fun _ ↦ X)
            ((truncatedCostandardSimplexIndexEquiv k (unop Δ₁)).symm
              ((coyoneda.obj (op (topTruncatedSimplex k))).map f.unop g)))
      have h₅ :
          (Pi.reindex
              (truncatedCostandardSimplexIndexEquiv k (unop Δ₁))
              (fun _ ↦ X)).hom ≫
            Pi.π (fun _ ↦ X) ((coyoneda.obj (op (topTruncatedSimplex k))).map f.unop g) =
          ((Pi.reindex
                  (truncatedCostandardSimplexIndexEquiv k (unop Δ₁))
                  (fun _ ↦ X)).hom ≫
              (homFromCosimplicialSet
                  (coyoneda.obj (op (topTruncatedSimplex k)))
                  ((Functor.const (SimplexCategory.Truncated k)ᵒᵖ).obj X)).map f) ≫
            Pi.π (fun _ ↦ X) g := by
        simpa [homFromCosimplicialSet, Category.assoc] using
          congrArg
            (fun t ↦
              (Pi.reindex
                  (truncatedCostandardSimplexIndexEquiv k (unop Δ₁))
                  (fun _ ↦ X)).hom ≫ t)
            ((Pi.map'_comp_π
              ((coyoneda.obj (op (topTruncatedSimplex k))).map f.unop)
              (fun _ ↦ 𝟙 X)
              g).symm)
      exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
    )

private theorem truncationHomFromCostandardSimplexIso_hom_app_π (k : ℕ) (X : C) :
    (truncationHomFromCostandardSimplexIso k X).hom.app
        (op (topTruncatedSimplex k)) ≫
          Pi.π (fun _ ↦ X) (𝟙 _) =
      Pi.π (fun _ ↦ X) (𝟙 _) := by
  simpa [truncationHomFromCostandardSimplexIso, truncatedCostandardSimplexIndexEquiv] using
    (Pi.reindex_hom_π
      (truncatedCostandardSimplexIndexEquiv k (topTruncatedSimplex k))
      (fun _ ↦ X)
      (𝟙 _))

private noncomputable def truncatedHomFromCostandardSimplexEvaluationIso (k : ℕ) (X : C) :
    (truncation k).obj
      (homFromCosimplicialSet C[k] ((SimplicialObject.const C).obj X)) ≅
      (evaluationRightAdjoint C (op (topTruncatedSimplex k))).obj X :=
  truncationHomFromCostandardSimplexIso k X ≪≫
    homFromCoyonedaIsoEvaluationRightAdjoint (topTruncatedSimplex k) X

private theorem truncatedHomFromCostandardSimplexEvaluationIso_hom_app_π (k : ℕ) (X : C) :
    (truncatedHomFromCostandardSimplexEvaluationIso k X).hom.app
        (op (topTruncatedSimplex k)) ≫
          Pi.π (fun _ ↦ X) (𝟙 _) =
      Pi.π (fun _ ↦ X) (𝟙 _) := by
  have hcore :
      (homFromCoyonedaIsoEvaluationRightAdjoint (topTruncatedSimplex k) X).hom.app
          (op (topTruncatedSimplex k)) ≫
          Pi.π (fun _ ↦ X) (𝟙 _) =
        Pi.π (fun _ ↦ X) (𝟙 _) := by
    simpa using
      homFromCoyonedaIsoEvaluationRightAdjoint_hom_app_π
        (topTruncatedSimplex k) X (op (topTruncatedSimplex k)) (𝟙 _)
  calc
    (truncatedHomFromCostandardSimplexEvaluationIso k X).hom.app (op (topTruncatedSimplex k)) ≫
        Pi.π (fun _ ↦ X) (𝟙 _)
      =
        (truncationHomFromCostandardSimplexIso k X).hom.app (op (topTruncatedSimplex k)) ≫
          (homFromCoyonedaIsoEvaluationRightAdjoint (topTruncatedSimplex k) X).hom.app
            (op (topTruncatedSimplex k)) ≫
          Pi.π (fun _ ↦ X) (𝟙 _) := by
            simp [truncatedHomFromCostandardSimplexEvaluationIso, Category.assoc]
    _ =
        (truncationHomFromCostandardSimplexIso k X).hom.app (op (topTruncatedSimplex k)) ≫
          Pi.π (fun _ ↦ X) (𝟙 _) := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  (truncationHomFromCostandardSimplexIso k X).hom.app
                    (op (topTruncatedSimplex k)) ≫ t)
                hcore
    _ = Pi.π (fun _ ↦ X) (𝟙 _) := by
      simpa using truncationHomFromCostandardSimplexIso_hom_app_π k X

/-- Lemma 14.15.2 (truncated clause): for a `k`-truncated simplicial object `W`, morphisms
`W ⟶ sk_k U`, where `sk_k U` is the source's `k`-truncation of `U = Hom(C[k], X)`, are
canonically in bijection with morphisms `W_k ⟶ X`. In the project API, `sk_k U` is
`(truncation k).obj U`. -/
noncomputable def truncatedHomFromCostandardSimplex_homEquiv (k : ℕ) (X : C)
    (W : SimplicialObject.Truncated C k) :
    (W ⟶ (truncation k).obj
      (homFromCosimplicialSet C[k] ((SimplicialObject.const C).obj X))) ≃
      (W _⦋k, le_rfl⦌ₖ ⟶ X) := by
  exact
    ((Iso.refl W).homCongr (truncatedHomFromCostandardSimplexEvaluationIso k X)).trans
      (((evaluationAdjunctionLeft C
        (op (topTruncatedSimplex k))).homEquiv W X).symm)

/-- The truncated canonical equivalence evaluates a morphism at the top truncated simplex and
projects to the identity-indexed factor. -/
theorem truncatedHomFromCostandardSimplex_homEquiv_apply (k : ℕ) (X : C)
    (W : SimplicialObject.Truncated C k)
    (γ : W ⟶ (truncation k).obj
      (homFromCosimplicialSet C[k] ((SimplicialObject.const C).obj X))) :
    truncatedHomFromCostandardSimplex_homEquiv k X W γ =
      γ.app (op (topTruncatedSimplex k)) ≫ Pi.π (fun _ ↦ X) (𝟙 _) := by
  change
    ((evaluationAdjunctionLeft C
        (op (topTruncatedSimplex k))).homEquiv W X).symm
        (((Iso.refl W).homCongr (truncatedHomFromCostandardSimplexEvaluationIso k X)) γ) =
      γ.app (op (topTruncatedSimplex k)) ≫ Pi.π (fun _ ↦ X) (𝟙 _)
  simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
  have hcore :
      ((evaluationAdjunctionLeft C
          (op (topTruncatedSimplex k))).homEquiv W X).symm
          (γ ≫ (truncatedHomFromCostandardSimplexEvaluationIso k X).hom) =
        γ.app (op (topTruncatedSimplex k)) ≫
          (truncatedHomFromCostandardSimplexEvaluationIso k X).hom.app
            (op (topTruncatedSimplex k)) ≫
          Pi.π (fun _ ↦ X) (𝟙 _) := by
    simpa [Category.assoc] using
      evaluationRightAdjoint_homEquiv_apply
        (topTruncatedSimplex k) X W
        (γ ≫ (truncatedHomFromCostandardSimplexEvaluationIso k X).hom)
  exact hcore.trans <| by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ γ.app (op (topTruncatedSimplex k)) ≫ t)
        (truncatedHomFromCostandardSimplexEvaluationIso_hom_app_π k X)

end CategoryTheory
