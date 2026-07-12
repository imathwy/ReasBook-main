import Mathlib.Tactic
import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.Monoidal
import StacksProject_2024.Chap20.«20_9_0_1»
import StacksProject_2024.Chap20.Lemma_20_9_3
import StacksProject_2024.Chap20.«20_25_3_1»
import StacksProject_2024.Chap20.OpensInstances

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace ComplexShape HomologicalComplex HomologicalComplex₂
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u v

variable {X : TopCat.{u}} {I : Type v}

local notation "PresheafCochain" => CochainComplex (X.Presheaf AddCommGrpCat) ℤ

/-- The extended Čech row functor attached to the indexed family `𝒰`. -/
abbrev rowCechFunctor (𝒰 : I → Opens X) :
    X.Presheaf AddCommGrpCat.{max u v} ⥤ CochainComplex AddCommGrpCat.{max u v} ℤ :=
  (cechComplexFunctor 𝒰 :
      X.Presheaf AddCommGrpCat.{max u v} ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ) ⋙
    embeddingUpNat.extendFunctor AddCommGrpCat.{max u v}

private instance cechComplexFunctor_preservesZeroMorphisms (𝒰 : I → Opens X) :
    ((cechComplexFunctor 𝒰 :
        X.Presheaf AddCommGrpCat.{max u v} ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ)
      ).PreservesZeroMorphisms where
  map_zero F G := by
    apply HomologicalComplex.hom_ext
    intro n
    change Limits.Pi.map
        (fun i ↦ (0 : F.obj (op (∏ᶜ 𝒰 ∘ i)) ⟶ G.obj (op (∏ᶜ 𝒰 ∘ i)))) = 0
    apply Limits.Pi.hom_ext
    intro j
    rw [Limits.Pi.map_π, comp_zero, zero_comp]

private instance rowCechFunctor_preservesZeroMorphisms (𝒰 : I → Opens X) :
    (rowCechFunctor 𝒰).PreservesZeroMorphisms where
  map_zero F G := by
    change
      HomologicalComplex.extendMap ((cechComplexFunctor 𝒰).map (0 : F ⟶ G))
          embeddingUpNat = 0
    have hzero : (cechComplexFunctor 𝒰).map (0 : F ⟶ G) = 0 :=
      Functor.map_zero (cechComplexFunctor 𝒰) F G
    rw [hzero]
    simpa using
      (HomologicalComplex.extendMap_zero
        ((cechComplexFunctor 𝒰).obj F)
        ((cechComplexFunctor 𝒰).obj G)
        embeddingUpNat)

/-- The rowwise Čech double-complex functor attached to `𝒰`. -/
abbrev doubleCechFunctor (𝒰 : I → Opens X) :
    PresheafCochain ⥤ HomologicalComplex₂ AddCommGrpCat.{max u v} (up ℤ) (up ℤ) :=
  (rowCechFunctor 𝒰).mapHomologicalComplex (up ℤ)

/-- The total Čech complex functor attached to `𝒰`. -/
abbrev totalCechFunctor (𝒰 : I → Opens X) :
    PresheafCochain ⥤ CochainComplex AddCommGrpCat.{max u v} ℤ :=
  doubleCechFunctor 𝒰 ⋙ totalFunctor AddCommGrpCat.{max u v} (up ℤ) (up ℤ) (up ℤ)

/- Domain-style sampling for 20.25.3.2:
- primary domain: Čech double complexes of presheaf-valued cochain complexes, their totalization,
  and the resulting total Čech functor;
- sampled owner declarations:
  * `(inferInstance : HasFiniteProducts (Opens X))`;
  * `cechComplexFunctor` and `embeddingUpNat.extendFunctor`;
  * `Functor.mapHomologicalComplex`;
  * `HomologicalComplex₂.total.map` and `HomologicalComplex₂.totalFunctor` from mathlib's
    total-complex API.
- best owner abstraction in this file: the canonical composite of `cechComplexFunctor 𝒰`,
  `embeddingUpNat.extendFunctor`, `Functor.mapHomologicalComplex`, and
  `HomologicalComplex₂.totalFunctor`, together with the canonical finite-product instance on
  `Opens X`;
- primitive data: the cover `𝒰` together with the objectwise `HasTotal` instances for the
  associated rowwise Čech double complexes;
- derived API: totalization of these bicomplexes and the induced refinement maps built in the
  immediately downstream file `20_25_0_2`.

Source/core/bridge triage:
- `source-facing`: the total Čech functor
  sending a presheaf cochain complex `F` to the total complex of the rowwise Čech bicomplex of
  `𝒰` and `F`;
- `core/canonical`: the canonical finite-product instance on `Opens X`, `cechComplexFunctor`,
  `embeddingUpNat.extendFunctor`, `Functor.mapHomologicalComplex`,
  `HomologicalComplex₂.totalFunctor`;
- `bridge/view`: none in this owner file. The tensor-side comparison discussed later in the
  chapter is not provided by a canonical upstream `LaxMonoidal` owner for `totalCechFunctor`, so
  this file should stop at the honest total Čech functor owner rather than introduce a
  placeholder monoidal structure assumption. -/

section TotalCechFunctor

variable (𝒰 : I → Opens X)

/- The total Čech complex functor sending `F` to the total complex of the rowwise Čech bicomplex
of `𝒰` and `F` is the canonical composite of the rowwise Čech double-complex functor with
`totalFunctor`. -/
#check
  (totalCechFunctor 𝒰 :
      PresheafCochain ⥤ CochainComplex AddCommGrpCat.{max u v} ℤ)

end TotalCechFunctor

section NaiveCupProduct

-- Route correction: the owner-only file had no item declaration. This section therefore records
-- the actual textbook morphism surface first, while keeping the source-faithful Alexander-Whitney
-- construction itself as the remaining blocker.

/-- Helper for 20.25.3.2: the front truncation of a `(p + q)`-simplex keeps the first `p + 1`
vertices. This is the Alexander-Whitney source object used in the ordinary Čech cup-product
component. -/
private theorem cech_front_simplex_bound (p q : ℕ) (i : Fin (p + 1)) :
    i.1 < p + q + 1 := by
  -- The front truncation only forgets vertices after the first `p + 1`, so the original index is
  -- still a valid vertex of the `(p + q)`-simplex.
  omega

/-- Helper for 20.25.3.2: the back truncation of a `(p + q)`-simplex starts at the `p`-th vertex.
This is the Alexander-Whitney source object for the second tensor factor. -/
private theorem cech_back_simplex_bound (p q : ℕ) (j : Fin (q + 1)) :
    p + j.1 < p + q + 1 := by
  -- Shifting a vertex of the tail simplex by `p` still lands inside the ambient `(p + q)`-simplex.
  omega

/-- Helper for 20.25.3.2: the front Alexander-Whitney truncation of a Čech simplex. -/
private def cechFrontSimplex (p q : ℕ) (σ : Fin (p + q + 1) → I) : Fin (p + 1) → I :=
  fun i ↦ σ ⟨i.1, cech_front_simplex_bound p q i⟩

/-- Helper for 20.25.3.2: the back Alexander-Whitney truncation of a Čech simplex. -/
private def cechBackSimplex (p q : ℕ) (σ : Fin (p + q + 1) → I) : Fin (q + 1) → I :=
  fun j ↦ σ ⟨p + j.1, cech_back_simplex_bound p q j⟩

/-- Helper for 20.25.3.2: evaluating the front truncation just reads the corresponding front
vertex of the ambient simplex. -/
private theorem cech_front_simplex_apply (p q : ℕ) (σ : Fin (p + q + 1) → I) (i : Fin (p + 1)) :
    cechFrontSimplex p q σ i = σ ⟨i.1, cech_front_simplex_bound p q i⟩ := by
  -- The front truncation was defined by direct reindexing of the ambient simplex.
  rfl

/-- Helper for 20.25.3.2: evaluating the back truncation just reads the shifted tail vertex of the
ambient simplex. -/
private theorem cech_back_simplex_apply (p q : ℕ) (σ : Fin (p + q + 1) → I) (j : Fin (q + 1)) :
    cechBackSimplex p q σ j = σ ⟨p + j.1, cech_back_simplex_bound p q j⟩ := by
  -- The back truncation is the same direct reindexing, now after shifting the vertex by `p`.
  rfl

/-- Helper for 20.25.3.2: the full Čech intersection is contained in the front-truncated
intersection of the same simplex. -/
private theorem cechIntersection_le_frontSimplex (𝒰 : I → Opens X) (p q : ℕ)
    (σ : Fin (p + q + 1) → I) :
    cechIntersection 𝒰 σ ≤ cechIntersection 𝒰 (cechFrontSimplex p q σ) := by
  -- The full intersection imposes every front condition, so it is contained in the front block.
  refine le_iInf fun i ↦ ?_
  rw [cech_front_simplex_apply]
  simpa [cechIntersection] using
    (iInf_le (fun j : Fin (p + q + 1) ↦ 𝒰 (σ j))
      ⟨i.1, cech_front_simplex_bound p q i⟩)

/-- Helper for 20.25.3.2: the full Čech intersection is contained in the back-truncated
intersection of the same simplex. -/
private theorem cechIntersection_le_backSimplex (𝒰 : I → Opens X) (p q : ℕ)
    (σ : Fin (p + q + 1) → I) :
    cechIntersection 𝒰 σ ≤ cechIntersection 𝒰 (cechBackSimplex p q σ) := by
  -- The full intersection also imposes every tail condition, so it is contained in the back block.
  refine le_iInf fun j ↦ ?_
  rw [cech_back_simplex_apply]
  simpa [cechIntersection] using
    (iInf_le (fun k : Fin (p + q + 1) ↦ 𝒰 (σ k))
      ⟨p + j.1, cech_back_simplex_bound p q j⟩)

/-- Helper for 20.25.3.2: sections on the front-truncated intersection restrict to the full Čech
intersection. -/
private abbrev cechFrontRestriction (𝒰 : I → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p q : ℕ)
    (σ : Fin (p + q + 1) → I) :
    F.obj (op (cechIntersection 𝒰 (cechFrontSimplex p q σ))) ⟶
      F.obj (op (cechIntersection 𝒰 σ)) :=
  F.map (homOfLE (cechIntersection_le_frontSimplex 𝒰 p q σ)).op

/-- Helper for 20.25.3.2: sections on the back-truncated intersection restrict to the full Čech
intersection. -/
private abbrev cechBackRestriction (𝒰 : I → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p q : ℕ)
    (σ : Fin (p + q + 1) → I) :
    F.obj (op (cechIntersection 𝒰 (cechBackSimplex p q σ))) ⟶
      F.obj (op (cechIntersection 𝒰 σ)) :=
  F.map (homOfLE (cechIntersection_le_backSimplex 𝒰 p q σ)).op

/-- Helper for 20.25.3.2: the sectionwise product comparison is natural under restriction of
opens. This is the owner-level square needed before descending the Alexander-Whitney component
through `mapBifunctorDesc`. -/
private theorem presheaf_product_section_hom_naturality
    (A B : X.Presheaf AddCommGrpCat.{max u v}) {V U : Opens X} (h : V ≤ U) :
    (A ⨯ B).map (homOfLE h).op ≫
        (PreservesLimitPair.iso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op V))
          A B).hom =
      (PreservesLimitPair.iso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op U))
        A B).hom ≫
        prod.map (A.map (homOfLE h).op) (B.map (homOfLE h).op) := by
  -- Route correction: `evaluation` does not expose a monoidal functor instance here, so we use
  -- the canonical product-comparison square coming from preservation of binary products.
  -- Proof comment: the restriction map is exactly the naturality square of `prodComparison`
  -- for the evaluation natural transformation induced by `h`.
  simpa [PreservesLimitPair.iso_hom] using
    (prodComparison_natural_of_natTrans
      (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).map (homOfLE h).op)))

/-- Helper for 20.25.3.2: the inverse sectionwise product comparison is natural under restriction
of opens. This is the source-facing Alexander-Whitney bridge from separate restricted sections to
the restricted section of the product presheaf. -/
private theorem presheaf_product_section_inv_naturality
    (A B : X.Presheaf AddCommGrpCat.{max u v}) {V U : Opens X} (h : V ≤ U) :
    (PreservesLimitPair.iso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op U))
      A B).inv ≫
        (A ⨯ B).map (homOfLE h).op =
      prod.map (A.map (homOfLE h).op) (B.map (homOfLE h).op) ≫
        (PreservesLimitPair.iso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op V))
          A B).inv := by
  let eU : (A ⨯ B).obj (op U) ≅ A.obj (op U) ⨯ B.obj (op U) :=
    PreservesLimitPair.iso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op U)) A B
  let eV : (A ⨯ B).obj (op V) ≅ A.obj (op V) ⨯ B.obj (op V) :=
    PreservesLimitPair.iso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op V)) A B
  have hhom : (A ⨯ B).map (homOfLE h).op ≫ eV.hom =
      eU.hom ≫ prod.map (A.map (homOfLE h).op) (B.map (homOfLE h).op) := by
    simpa [eU, eV] using presheaf_product_section_hom_naturality A B h
  change eU.inv ≫ (A ⨯ B).map (homOfLE h).op =
    prod.map (A.map (homOfLE h).op) (B.map (homOfLE h).op) ≫ eV.inv
  -- Proof comment: cancel the right-hand isomorphism `eV.hom`, rewrite the middle square by the
  -- forward naturality identity, and then simplify both isomorphism pairs.
  apply (cancel_mono eV.hom).1
  have hcomp :
      eU.inv ≫ (A ⨯ B).map (homOfLE h).op ≫ eV.hom =
        prod.map (A.map (homOfLE h).op) (B.map (homOfLE h).op) := by
    calc
      eU.inv ≫ (A ⨯ B).map (homOfLE h).op ≫ eV.hom
        = eU.inv ≫ ((A ⨯ B).map (homOfLE h).op ≫ eV.hom) := by
            simp
      _ = eU.inv ≫ (eU.hom ≫ prod.map (A.map (homOfLE h).op) (B.map (homOfLE h).op)) := by
            rw [hhom]
      _ = prod.map (A.map (homOfLE h).op) (B.map (homOfLE h).op) := by
            simp
  calc
    eU.inv ≫ (A ⨯ B).map (homOfLE h).op ≫ eV.hom
      = prod.map (A.map (homOfLE h).op) (B.map (homOfLE h).op) := hcomp
    _ = prod.map (A.map (homOfLE h).op) (B.map (homOfLE h).op) ≫ eV.inv ≫ eV.hom := by
          simp

/-- Helper for 20.25.3.2: the `σ`-coordinate of the tuplewise Alexander-Whitney product reads the
front and back coordinates, restricts both sections to the full intersection, and then applies the
sectionwise product comparison. -/
private noncomputable abbrev cechTerm_product_coordinate
    (𝒰 : I → Opens X) (A B : X.Presheaf AddCommGrpCat.{max u v}) (p q : ℕ)
    (σ : Fin (p + q + 1) → I) :
    cechTerm 𝒰 A p ⨯ cechTerm 𝒰 B q ⟶ (A ⨯ B).obj (op (cechIntersection 𝒰 σ)) :=
  Limits.prod.lift
      (Limits.prod.fst ≫
        cechTermEval 𝒰 A p (cechFrontSimplex p q σ) ≫
        cechFrontRestriction 𝒰 A p q σ)
      (Limits.prod.snd ≫
        cechTermEval 𝒰 B q (cechBackSimplex p q σ) ≫
        cechBackRestriction 𝒰 B p q σ) ≫
    (PreservesLimitPair.iso
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op (cechIntersection 𝒰 σ))) A B).inv

/-- Helper for 20.25.3.2: the tuplewise Alexander-Whitney product is the additive map whose
`σ`-coordinate is `cechTerm_product_coordinate`. This is the source-faithful raw Čech coordinate
map before any row extension to `ℤ`. -/
private noncomputable def cechTerm_product_map
    (𝒰 : I → Opens X) (A B : X.Presheaf AddCommGrpCat.{max u v}) (p q : ℕ) :
    cechTerm 𝒰 A p ⨯ cechTerm 𝒰 B q ⟶ cechTerm 𝒰 (A ⨯ B) (p + q) :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun s σ ↦ (ConcreteCategory.hom (cechTerm_product_coordinate 𝒰 A B p q σ)) s)
      (fun s t ↦ by
        ext σ
        exact map_add (ConcreteCategory.hom (cechTerm_product_coordinate 𝒰 A B p q σ)) s t)

/-- Helper for 20.25.3.2: postcomposing the tuplewise Alexander-Whitney product with evaluation at
`σ` recovers the chosen front/back restriction composite. -/
private theorem cechTerm_product_map_eval
    (𝒰 : I → Opens X) (A B : X.Presheaf AddCommGrpCat.{max u v}) (p q : ℕ)
    (σ : Fin (p + q + 1) → I) :
    cechTerm_product_map 𝒰 A B p q ≫ cechTermEval 𝒰 (A ⨯ B) (p + q) σ =
      cechTerm_product_coordinate 𝒰 A B p q σ := by
  -- Proof comment: the raw Čech product was defined by prescribing each simplex coordinate.
  rfl

/-- Helper for 20.25.3.2: after transporting raw Čech degrees through `cechTermIso`, the
Alexander-Whitney coordinate map becomes a morphism between the owner degrees of
`cechComplexFunctor`. This is the raw source-side branch that will later be inserted into the
rowwise `mapBifunctorDesc` over `rowCechFunctor`. -/
private noncomputable def cechComplex_product_branch
    (𝒰 : I → Opens X) (A B : X.Presheaf AddCommGrpCat.{max u v}) (p q : ℕ) :
    (((cechComplexFunctor 𝒰).obj A).X p ⨯ ((cechComplexFunctor 𝒰).obj B).X q) ⟶
      ((cechComplexFunctor 𝒰).obj (A ⨯ B)).X (p + q) :=
  prod.map (cechTermIso 𝒰 A p).hom (cechTermIso 𝒰 B q).hom ≫
    cechTerm_product_map 𝒰 A B p q ≫
      (cechTermIso 𝒰 (A ⨯ B) (p + q)).inv

/-- Helper for 20.25.3.2: after transporting the target degree by `cechTermIso`, the owner-level
raw branch has the same simplex-coordinate formula as `cechTerm_product_map`, now after first
transporting the two source degrees through their `cechTermIso` identifications. -/
private theorem cechComplex_product_branch_eval
    (𝒰 : I → Opens X) (A B : X.Presheaf AddCommGrpCat.{max u v}) (p q : ℕ)
    (σ : Fin (p + q + 1) → I) :
    cechComplex_product_branch 𝒰 A B p q ≫
        (cechTermIso 𝒰 (A ⨯ B) (p + q)).hom ≫
          cechTermEval 𝒰 (A ⨯ B) (p + q) σ =
      prod.map (cechTermIso 𝒰 A p).hom (cechTermIso 𝒰 B q).hom ≫
        cechTerm_product_coordinate 𝒰 A B p q σ := by
  -- Route correction: there is no `tensorObj` owner on the raw `ℕ`-indexed Čech complexes, so
  -- we first normalize the source-faithful Alexander-Whitney formula on raw degrees and only then
  -- lift it to the extended row complexes where `mapBifunctorDesc` is available.
  -- Proof comment: after composing with the target `cechTermIso`, the owner-level branch is
  -- literally the transported tuplewise product map. A single reassociation exposes the target
  -- `inv ≫ hom = 𝟙`, and the remaining coordinate evaluation is
  -- `cechTerm_product_map_eval`.
  have htarget_cancel :
      (cechTermIso 𝒰 (A ⨯ B) (p + q)).inv ≫
          (cechTermIso 𝒰 (A ⨯ B) (p + q)).hom ≫
            cechTermEval 𝒰 (A ⨯ B) (p + q) σ =
        cechTermEval 𝒰 (A ⨯ B) (p + q) σ := by
    -- Proof comment: the target transport is an isomorphism, so its inverse followed by its
    -- forward map cancels before evaluation.
    simpa using
      (Iso.inv_hom_id_assoc (cechTermIso 𝒰 (A ⨯ B) (p + q))
        (cechTermEval 𝒰 (A ⨯ B) (p + q) σ))
  calc
    cechComplex_product_branch 𝒰 A B p q ≫
        (cechTermIso 𝒰 (A ⨯ B) (p + q)).hom ≫
          cechTermEval 𝒰 (A ⨯ B) (p + q) σ
      =
        prod.map (cechTermIso 𝒰 A p).hom (cechTermIso 𝒰 B q).hom ≫
          (cechTerm_product_map 𝒰 A B p q ≫
            cechTermEval 𝒰 (A ⨯ B) (p + q) σ) := by
              rw [cechComplex_product_branch]
              simp only [Category.assoc]
              exact congrArg
                (fun k ↦
                  prod.map (cechTermIso 𝒰 A p).hom (cechTermIso 𝒰 B q).hom ≫
                    cechTerm_product_map 𝒰 A B p q ≫ k)
                htarget_cancel
    _ =
        prod.map (cechTermIso 𝒰 A p).hom (cechTermIso 𝒰 B q).hom ≫
          cechTerm_product_coordinate 𝒰 A B p q σ := by
            rw [cechTerm_product_map_eval]

section TensorDesc

variable [MonoidalCategory AddCommGrpCat.{max u v}]
variable [CategoryTheory.MonoidalPreadditive AddCommGrpCat.{max u v}]

/-- Helper for 20.25.3.2: postcomposing a descended tensor map can be checked on each
`(p,q)`-summand of the tensor totalization. This is the standard `ιTensorObj` adapter needed for
the rowwise and double-complex `mapBifunctorDesc` packaging steps. -/
@[reassoc]
private theorem iTensorObj_mapBifunctorDesc_assoc
    {K L : CochainComplex AddCommGrpCat.{max u v} ℤ} (n : ℤ)
    {B C : AddCommGrpCat.{max u v}}
    (f : ∀ p q
      (_ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((CategoryTheory.MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj
        (K.X p)).obj (L.X q) ⟶ B)
    (u : B ⟶ C) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc f ≫
        u =
      f p q h ≫ u := by
  -- Proof comment: cross the `tensorObj` abbreviation once and then postcompose the owner
  -- universal-property formula `ι_mapBifunctorDesc`.
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc f p q h)

end TensorDesc

/-- The nonnegative row-degree Alexander-Whitney branch from the rowwise Čech product data to the
rowwise Čech complex of the product presheaf. This is the source-facing product bridge that any
later tensor-level cup-product packaging must descend. -/
noncomputable def rowCechProductBranch
    (𝒰 : I → Opens X) (A B : X.Presheaf AddCommGrpCat.{max u v}) (p q : ℕ) :
    (((rowCechFunctor 𝒰).obj A).X (p : ℤ) ⨯ ((rowCechFunctor 𝒰).obj B).X (q : ℤ)) ⟶
      ((rowCechFunctor 𝒰).obj (A ⨯ B)).X ((p + q : ℕ) : ℤ) :=
  prod.map
      (((cechComplexFunctor 𝒰).obj A).extendXIso embeddingUpNat rfl).hom
      (((cechComplexFunctor 𝒰).obj B).extendXIso embeddingUpNat rfl).hom ≫
    cechComplex_product_branch 𝒰 A B p q ≫
      (((cechComplexFunctor 𝒰).obj (A ⨯ B)).extendXIso embeddingUpNat rfl).inv

/-- Composing `rowCechProductBranch` with the target `extendXIso` forgets the target transport and
recovers the transported raw Čech branch. -/
@[reassoc]
theorem rowCechProductBranch_assoc
    (𝒰 : I → Opens X) (A B : X.Presheaf AddCommGrpCat.{max u v}) (p q : ℕ) :
    rowCechProductBranch 𝒰 A B p q ≫
        (((cechComplexFunctor 𝒰).obj (A ⨯ B)).extendXIso embeddingUpNat rfl).hom =
      prod.map
        (((cechComplexFunctor 𝒰).obj A).extendXIso embeddingUpNat rfl).hom
        (((cechComplexFunctor 𝒰).obj B).extendXIso embeddingUpNat rfl).hom ≫
        cechComplex_product_branch 𝒰 A B p q := by
  -- Proof comment: the target extension transport is an isomorphism, so the final
  -- `extendXIso.inv ≫ extendXIso.hom` cancels immediately.
  rw [rowCechProductBranch]
  have hcancel :
      prod.map
          (((cechComplexFunctor 𝒰).obj A).extendXIso embeddingUpNat rfl).hom
          (((cechComplexFunctor 𝒰).obj B).extendXIso embeddingUpNat rfl).hom ≫
          cechComplex_product_branch 𝒰 A B p q ≫
            ((((cechComplexFunctor 𝒰).obj (A ⨯ B)).extendXIso embeddingUpNat rfl).inv
              ≫
                (((cechComplexFunctor 𝒰).obj (A ⨯ B)).extendXIso
                  embeddingUpNat rfl).hom) =
        prod.map
            (((cechComplexFunctor 𝒰).obj A).extendXIso embeddingUpNat rfl).hom
            (((cechComplexFunctor 𝒰).obj B).extendXIso embeddingUpNat rfl).hom ≫
          cechComplex_product_branch 𝒰 A B p q ≫ 𝟙 _ := by
    exact congrArg
      (fun t ↦
        prod.map
            (((cechComplexFunctor 𝒰).obj A).extendXIso embeddingUpNat rfl).hom
            (((cechComplexFunctor 𝒰).obj B).extendXIso embeddingUpNat rfl).hom ≫
          cechComplex_product_branch 𝒰 A B p q ≫ t)
      (Iso.inv_hom_id
        (((cechComplexFunctor 𝒰).obj (A ⨯ B)).extendXIso embeddingUpNat rfl))
  calc
    prod.map
        (((cechComplexFunctor 𝒰).obj A).extendXIso embeddingUpNat rfl).hom
        (((cechComplexFunctor 𝒰).obj B).extendXIso embeddingUpNat rfl).hom ≫
        cechComplex_product_branch 𝒰 A B p q ≫
          (((cechComplexFunctor 𝒰).obj (A ⨯ B)).extendXIso embeddingUpNat rfl).inv ≫
            (((cechComplexFunctor 𝒰).obj (A ⨯ B)).extendXIso embeddingUpNat rfl).hom
      =
        prod.map
            (((cechComplexFunctor 𝒰).obj A).extendXIso embeddingUpNat rfl).hom
            (((cechComplexFunctor 𝒰).obj B).extendXIso embeddingUpNat rfl).hom ≫
          cechComplex_product_branch 𝒰 A B p q ≫
            ((((cechComplexFunctor 𝒰).obj (A ⨯ B)).extendXIso embeddingUpNat rfl).inv
              ≫
                (((cechComplexFunctor 𝒰).obj (A ⨯ B)).extendXIso
                  embeddingUpNat rfl).hom) := by
                simp
    _ =
        prod.map
            (((cechComplexFunctor 𝒰).obj A).extendXIso embeddingUpNat rfl).hom
            (((cechComplexFunctor 𝒰).obj B).extendXIso embeddingUpNat rfl).hom ≫
          cechComplex_product_branch 𝒰 A B p q ≫ 𝟙 _ := hcancel
    _ =
        prod.map
            (((cechComplexFunctor 𝒰).obj A).extendXIso embeddingUpNat rfl).hom
            (((cechComplexFunctor 𝒰).obj B).extendXIso embeddingUpNat rfl).hom ≫
          cechComplex_product_branch 𝒰 A B p q := by
            simp

/- The remaining declarations package the source-facing product branch `rowCechProductBranch`
into a tensor-level comparison once ambient tensor structures on presheaf complexes are fixed. -/
/-- Helper for 20.25.3.2: if `p = i + r` and `q = j + s`, then the Alexander-Whitney target
summand has total degree `n = (i + j) + (r + s)`. -/
private theorem cechTotalNaiveCupProduct_target_index
    {n p q i j : ℤ} {r s : ℕ} (h : p + q = n) (hp : i + (r : ℤ) = p)
    (hq : j + (s : ℤ) = q) :
    (i + j) + ((r + s : ℕ) : ℤ) = n := by
  omega

variable
    [MonoidalCategory AddCommGrpCat.{max u v}]
    [CategoryTheory.MonoidalPreadditive AddCommGrpCat.{max u v}]
    [MonoidalCategory (X.Presheaf AddCommGrpCat.{max u v})]
    [CategoryTheory.MonoidalPreadditive (X.Presheaf AddCommGrpCat.{max u v})]
    [∀ A : AddCommGrpCat.{max u v},
      PreservesFiniteCoproducts ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj A)]
    [∀ A : AddCommGrpCat.{max u v},
      PreservesFiniteCoproducts
        ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).flip.obj A)]
    [∀ F : X.Presheaf AddCommGrpCat.{max u v},
      PreservesFiniteCoproducts
        ((MonoidalCategory.curriedTensor (X.Presheaf AddCommGrpCat.{max u v})).obj F)]
    [∀ F : X.Presheaf AddCommGrpCat.{max u v},
      PreservesFiniteCoproducts
        ((MonoidalCategory.curriedTensor (X.Presheaf AddCommGrpCat.{max u v})).flip.obj F)]

/-- Helper for 20.25.3.2: on the source summand indexed by cochain degrees `i`, `j` and Čech
degrees `r`, `s`, the target naive cup-product branch is obtained by the rowwise
Alexander-Whitney morphism `rowCechProductBranch`, followed by the rowwise image of a chosen
degreewise coefficient map `τ i j : F.X i ⨯ G.X j ⟶ (HomologicalComplex.tensorObj F G).X (i + j)`
and the target total-complex inclusion. -/
noncomputable def cechTotalNaiveCupProductTargetSummand
    (𝒰 : I → Opens X) (F G : PresheafCochain) {n p q : ℤ} (h : p + q = n)
    (τ : ∀ i j, F.X i ⨯ G.X j ⟶ (HomologicalComplex.tensorObj F G).X (i + j))
    (i j : ℤ) (r s : ℕ) (hp : i + (r : ℤ) = p) (hq : j + (s : ℤ) = q) :
    ((((doubleCechFunctor 𝒰).obj F).X i).X (r : ℤ) ⨯
        (((doubleCechFunctor 𝒰).obj G).X j).X (s : ℤ)) ⟶
      ((totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)).X n :=
  rowCechProductBranch 𝒰 (F.X i) (G.X j) r s ≫
    ((rowCechFunctor 𝒰).map (τ i j)).f (((r + s : ℕ) : ℤ)) ≫
    ((doubleCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)).ιTotal (up ℤ) (i + j)
      (((r + s : ℕ) : ℤ)) n (cechTotalNaiveCupProduct_target_index h hp hq)

/-- A morphism `μ` is a naive Čech cup-product comparison if, on every tensor summand coming from
cochain degrees `i`, `j` and Čech degrees `r`, `s`, its degree-`n` component is exactly the
Alexander-Whitney branch `rowCechProductBranch 𝒰 (F.X i) (G.X j) r s`, followed by the rowwise
image of some degreewise coefficient map `τ i j : F.X i ⨯ G.X j ⟶ (HomologicalComplex.tensorObj F
G).X (i + j)` and the canonical target total inclusion. Equivalently, each degree component `μ.f n`
must be the descended source family `σ` on tensor degrees, together with a comparison map `ρ`
from the categorical product of the two degree-`p` and degree-`q` total Čech terms to their
ambient tensor object, and the composite `ρ ≫ σ` is constrained on every `(i,j,r,s)` summand by
the Alexander-Whitney branch data. This keeps the source-facing Alexander-Whitney construction
visible at the public API surface instead of only recording an abstract coproduct descender. -/
def IsCechTotalNaiveCupProduct (𝒰 : I → Opens X) (F G : PresheafCochain)
    (μ :
      HomologicalComplex.tensorObj ((totalCechFunctor 𝒰).obj F) ((totalCechFunctor 𝒰).obj G) ⟶
        (totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)) : Prop :=
  ∃ (σ :
      ∀ p q n (_ : p + q = n),
        ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj
          (((totalCechFunctor 𝒰).obj F).X p)).obj (((totalCechFunctor 𝒰).obj G).X q) ⟶
          ((totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)).X n)
    (ρ :
      ∀ p q n (_ : p + q = n),
        ((totalCechFunctor 𝒰).obj F).X p ⨯ ((totalCechFunctor 𝒰).obj G).X q ⟶
          ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj
            (((totalCechFunctor 𝒰).obj F).X p)).obj (((totalCechFunctor 𝒰).obj G).X q))
    (τ : ∀ i j, F.X i ⨯ G.X j ⟶ (HomologicalComplex.tensorObj F G).X (i + j)),
    (∀ n, μ.f n = HomologicalComplex.mapBifunctorDesc (fun p q h ↦ σ p q n h)) ∧
      ∀ {n p q : ℤ} (h : p + q = n) (i j : ℤ) (r s : ℕ) (hp : i + (r : ℤ) = p)
          (hq : j + (s : ℤ) = q),
        prod.map
            (((doubleCechFunctor 𝒰).obj F).ιTotal (up ℤ) i (r : ℤ) p hp)
            (((doubleCechFunctor 𝒰).obj G).ιTotal (up ℤ) j (s : ℤ) q hq) ≫
            ρ p q n h ≫ σ p q n h =
          cechTotalNaiveCupProductTargetSummand 𝒰 F G h τ i j r s hp hq

/-- 20.25.3.2: if a chosen tensor-degree family `σ` is compatible with the total differentials,
then descending `σ` through `HomologicalComplex.mapBifunctorDesc` in each total degree gives an
explicit naive Čech cup-product comparison. The Alexander-Whitney summand formula for a
particular choice of `σ` is recorded separately by `cechTotalNaiveCupProduct_spec`. -/
@[stacks 07MB]
noncomputable def cechTotalNaiveCupProduct
    (𝒰 : I → Opens X) (F G : PresheafCochain)
    (σ :
      ∀ p q n (_ : p + q = n),
        ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj
          (((totalCechFunctor 𝒰).obj F).X p)).obj (((totalCechFunctor 𝒰).obj G).X q) ⟶
          ((totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)).X n)
    (hσcomm :
      ∀ i j, i + 1 = j →
        HomologicalComplex.mapBifunctorDesc (fun p q h ↦ σ p q i h) ≫
            ((totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)).d i j =
          (HomologicalComplex.tensorObj ((totalCechFunctor 𝒰).obj F)
              ((totalCechFunctor 𝒰).obj G)).d i j ≫
            HomologicalComplex.mapBifunctorDesc (fun p q h ↦ σ p q j h)) :
    HomologicalComplex.tensorObj ((totalCechFunctor 𝒰).obj F) ((totalCechFunctor 𝒰).obj G) ⟶
      (totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G) :=
  HomologicalComplex.Hom.mk
    (fun n ↦ HomologicalComplex.mapBifunctorDesc (fun p q h ↦ σ p q n h))
    hσcomm

omit
  [∀ A : AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj A)]
  [∀ A : AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts
      ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).flip.obj A)]
  [∀ F : X.Presheaf AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts
      ((MonoidalCategory.curriedTensor (X.Presheaf AddCommGrpCat.{max u v})).obj F)]
  [∀ F : X.Presheaf AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts
      ((MonoidalCategory.curriedTensor (X.Presheaf AddCommGrpCat.{max u v})).flip.obj F)] in
/-- The degree-`n` component of `cechTotalNaiveCupProduct 𝒰 F G σ` is the descended tensor family
specified by `σ`. -/
@[simp]
theorem cechTotalNaiveCupProduct_f
    (𝒰 : I → Opens X) (F G : PresheafCochain)
    (σ :
      ∀ p q n (_ : p + q = n),
        ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj
          (((totalCechFunctor 𝒰).obj F).X p)).obj (((totalCechFunctor 𝒰).obj G).X q) ⟶
          ((totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)).X n)
    (hσcomm :
      ∀ i j, i + 1 = j →
        HomologicalComplex.mapBifunctorDesc (fun p q h ↦ σ p q i h) ≫
            ((totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)).d i j =
          (HomologicalComplex.tensorObj ((totalCechFunctor 𝒰).obj F)
              ((totalCechFunctor 𝒰).obj G)).d i j ≫
            HomologicalComplex.mapBifunctorDesc (fun p q h ↦ σ p q j h))
    (n : ℤ) :
    (cechTotalNaiveCupProduct 𝒰 F G σ hσcomm).f n =
      HomologicalComplex.mapBifunctorDesc (fun p q h ↦ σ p q n h) :=
  rfl

omit
  [∀ A : AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj A)]
  [∀ A : AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts
      ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).flip.obj A)]
  [∀ F : X.Presheaf AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts
      ((MonoidalCategory.curriedTensor (X.Presheaf AddCommGrpCat.{max u v})).obj F)]
  [∀ F : X.Presheaf AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts
      ((MonoidalCategory.curriedTensor (X.Presheaf AddCommGrpCat.{max u v})).flip.obj F)] in
/-- A source-facing naive Čech cup-product comparison comes with explicit degreewise coefficient
maps `τ`, tensor-degree descenders `σ`, and product-to-tensor comparison maps `ρ` satisfying the
Alexander-Whitney summand formula. This companion theorem exposes those witnesses without forcing
downstream code to unfold `IsCechTotalNaiveCupProduct`. -/
theorem IsCechTotalNaiveCupProduct.spec
    {𝒰 : I → Opens X} {F G : PresheafCochain}
    {μ :
      HomologicalComplex.tensorObj ((totalCechFunctor 𝒰).obj F) ((totalCechFunctor 𝒰).obj G) ⟶
        (totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)}
    (hμ : IsCechTotalNaiveCupProduct 𝒰 F G μ) :
    ∃ (σ :
        ∀ p q n (_ : p + q = n),
          ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj
            (((totalCechFunctor 𝒰).obj F).X p)).obj (((totalCechFunctor 𝒰).obj G).X q) ⟶
            ((totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)).X n)
      (ρ :
        ∀ p q n (_ : p + q = n),
          ((totalCechFunctor 𝒰).obj F).X p ⨯ ((totalCechFunctor 𝒰).obj G).X q ⟶
            ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj
              (((totalCechFunctor 𝒰).obj F).X p)).obj (((totalCechFunctor 𝒰).obj G).X q))
      (τ : ∀ i j, F.X i ⨯ G.X j ⟶ (HomologicalComplex.tensorObj F G).X (i + j)),
      (∀ n, μ.f n = HomologicalComplex.mapBifunctorDesc (fun p q h ↦ σ p q n h)) ∧
        ∀ {n p q : ℤ} (h : p + q = n) (i j : ℤ) (r s : ℕ) (hp : i + (r : ℤ) = p)
            (hq : j + (s : ℤ) = q),
          prod.map
              (((doubleCechFunctor 𝒰).obj F).ιTotal (up ℤ) i (r : ℤ) p hp)
              (((doubleCechFunctor 𝒰).obj G).ιTotal (up ℤ) j (s : ℤ) q hq) ≫
              ρ p q n h ≫ σ p q n h =
            cechTotalNaiveCupProductTargetSummand 𝒰 F G h τ i j r s hp hq :=
  hμ

omit
  [∀ A : AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj A)]
  [∀ A : AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts
      ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).flip.obj A)]
  [∀ F : X.Presheaf AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts
      ((MonoidalCategory.curriedTensor (X.Presheaf AddCommGrpCat.{max u v})).obj F)]
  [∀ F : X.Presheaf AddCommGrpCat.{max u v},
    PreservesFiniteCoproducts
      ((MonoidalCategory.curriedTensor (X.Presheaf AddCommGrpCat.{max u v})).flip.obj F)] in
/-- If the descended tensor-degree family `σ` is compatible with the total differentials, and if
`σ`, the product-to-tensor comparison `ρ`, and the degreewise coefficient maps `τ` satisfy the
Alexander-Whitney summand formula, then the resulting concrete comparison map is a naive Čech
cup-product comparison. -/
theorem cechTotalNaiveCupProduct_spec
    (𝒰 : I → Opens X) (F G : PresheafCochain)
    (σ :
      ∀ p q n (_ : p + q = n),
        ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj
          (((totalCechFunctor 𝒰).obj F).X p)).obj (((totalCechFunctor 𝒰).obj G).X q) ⟶
          ((totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)).X n)
    (hσcomm :
      ∀ i j, i + 1 = j →
        HomologicalComplex.mapBifunctorDesc (fun p q h ↦ σ p q i h) ≫
            ((totalCechFunctor 𝒰).obj (HomologicalComplex.tensorObj F G)).d i j =
          (HomologicalComplex.tensorObj ((totalCechFunctor 𝒰).obj F)
              ((totalCechFunctor 𝒰).obj G)).d i j ≫
            HomologicalComplex.mapBifunctorDesc (fun p q h ↦ σ p q j h))
    (ρ :
      ∀ p q n (_ : p + q = n),
        ((totalCechFunctor 𝒰).obj F).X p ⨯ ((totalCechFunctor 𝒰).obj G).X q ⟶
          ((MonoidalCategory.curriedTensor AddCommGrpCat.{max u v}).obj
            (((totalCechFunctor 𝒰).obj F).X p)).obj (((totalCechFunctor 𝒰).obj G).X q))
    (τ : ∀ i j, F.X i ⨯ G.X j ⟶ (HomologicalComplex.tensorObj F G).X (i + j))
    (hσ :
      ∀ {n p q : ℤ} (h : p + q = n) (i j : ℤ) (r s : ℕ) (hp : i + (r : ℤ) = p)
          (hq : j + (s : ℤ) = q),
        prod.map
            (((doubleCechFunctor 𝒰).obj F).ιTotal (up ℤ) i (r : ℤ) p hp)
            (((doubleCechFunctor 𝒰).obj G).ιTotal (up ℤ) j (s : ℤ) q hq) ≫
            ρ p q n h ≫ σ p q n h =
          cechTotalNaiveCupProductTargetSummand 𝒰 F G h τ i j r s hp hq) :
    IsCechTotalNaiveCupProduct 𝒰 F G (cechTotalNaiveCupProduct 𝒰 F G σ hσcomm) := by
  refine ⟨σ, ρ, τ, ?_, ?_⟩
  · intro n
    rfl
  · exact hσ

end NaiveCupProduct
