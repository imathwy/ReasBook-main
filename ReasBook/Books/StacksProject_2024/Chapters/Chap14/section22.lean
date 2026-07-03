import Mathlib
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_14_22_1 (from Chap14) -/
universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.22.1:
- primary domain: simplicial objects as a functor category over `SimplexCategoryᵒᵖ`;
- inspected owner declarations:
  `CategoryTheory.Abelian.functorCategoryAbelian`,
  `CategoryTheory.SimplicialObject`,
  `CategoryTheory.functorCategoryPreadditive`;
- best owner abstraction: the canonical abelian functor-category instance on `SimplicialObject A`;
- primitive data: only the ambient abelian structure on `A`;
- derived API: the induced abelian structure on simplicial objects;
- source/core/bridge triage: the numbered lemma is a `source-facing` recall of the canonical
  owner `Abelian (SimplicialObject A)`. -/

/- Owner recall: the abelian structure on simplicial objects is the canonical functor-category
instance specialized to `SimplexCategoryᵒᵖ ⥤ A`. -/
recall Abelian.functorCategoryAbelian

/- Lemma 14.22.1: simplicial objects in an abelian category form an abelian category. -/
#check (inferInstance : Abelian (SimplicialObject A))

end CategoryTheory

/-! ### Lemma_14_22_2 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open Simplicial
open SimplexCategory.Truncated.Hom
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 14.22.2:
- primary domain: the concentrated `k`-truncated simplicial object `single_degree_truncated A k`,
  together with the canonical left and right Kan extensions `i_{k!}` and `cosk_k`;
- sampled owner declarations:
  `single_degree_truncated`,
  `SimplicialObject.Truncated.sk`,
  `SimplicialObject.Truncated.cosk`,
  `skAdj`,
  `coskAdj`,
  `Functor.leftKanExtensionObjIsoColimit`,
  `Functor.ranObjObjIsoLimit`;
- best owner abstraction:
  `source-facing`: the concentrated object in degree `k`, the Hom-set formulas with the required
    top face/degeneracy vanishing conditions, and the degreewise biproduct decompositions of
    `i_{k!}` and `cosk_k`;
  `core/canonical`: the owner functors `Truncated.sk k` and `Truncated.cosk k`, together with the
    adjunctions `skAdj k` and `coskAdj k`;
  `bridge/view`: the explicit summand and projection maps below, obtained from the canonical
    colimit/limit owners for those Kan extensions.
- primitive data: only the object `A` and the source-facing owner `single_degree_truncated A k`;
- derived API: the Hom-set equivalences with their vanishing conditions, the degreewise
  surjection/injection biproduct decompositions, the induced simplicial structure-map formulas,
  and the coefficient formula for the comparison map from `i_{k!}` to `cosk_k`.

Source/core/bridge triage:
- `source-facing`: the concentrated object and the explicit formulas attached to it;
- `core/canonical`: `single_degree_truncated`, `sk`, `cosk`, `skAdj`, and `coskAdj`;
- `bridge/view`: the direct summand/projection maps and the chosen degreewise isomorphisms extracted
  from unique universal descriptions. -/

namespace SimplicialObject.Truncated

/-- Surjections `[n] ↠ [k]`, the index set for the degree-`n` summands of `i_{k!}` applied to the
concentrated `k`-truncated object. -/
abbrev topEpiIndex (k n : ℕ) := { θ : ⦋n⦌ ⟶ ⦋k⦌ // Epi θ }

instance topEpiIndex_fintype (k n : ℕ) : Fintype (topEpiIndex k n) :=
  Fintype.ofFinite _

/-- Injections `[k] ↪ [n]`, the index set for the degree-`n` summands of `cosk_k` applied to the
concentrated `k`-truncated object. -/
abbrev topMonoIndex (k n : ℕ) := { θ : ⦋k⦌ ⟶ ⦋n⦌ // Mono θ }

instance topMonoIndex_fintype (k n : ℕ) : Fintype (topMonoIndex k n) :=
  Fintype.ofFinite _

section ComparisonMap

variable {k : ℕ}
variable [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
  (SimplexCategory.Truncated.inclusion k).op.HasRightKanExtension F]
variable [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
  (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F]

/-- The canonical comparison morphism from `i_{k!} U` to `cosk_k U`, obtained as the adjoint
transpose of the inverse of the skeleton unit. -/
noncomputable abbrev skToCosk (U : SimplicialObject.Truncated A k) :
    (Truncated.sk k).obj U ⟶ (Truncated.cosk k).obj U :=
  ((coskAdj k).homEquiv ((Truncated.sk k).obj U) U)
    (((asIso (skAdj k).unit).app U).inv)

@[simp] theorem homEquiv_symm_skToCosk (U : SimplicialObject.Truncated A k) :
    (((coskAdj k).homEquiv ((Truncated.sk k).obj U) U).symm U.skToCosk) =
      ((asIso (skAdj k).unit).app U).inv := by
  simp only [skToCosk, Equiv.symm_apply_apply]

end ComparisonMap

section ComparisonBridge

variable [HasZeroObject A] [HasZeroMorphisms A]

section Concentrated

private abbrev topTruncatedSimplex (k : ℕ) : SimplexCategory.Truncated k :=
  ⦋k, le_rfl⦌ₖ

private abbrev singleDegreeTruncatedTopIso (B : A) (k : ℕ) :
    B ≅ (single_degree_truncated B k) _⦋k, le_rfl⦌ₖ :=
  CategoryTheory.eqToIso (single_degree_truncated_obj_top B k).symm

private abbrev topEpiCostructuredArrow {k n : ℕ} (α : topEpiIndex k n) :
    CostructuredArrow (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌) :=
  CostructuredArrow.mk
    (show (SimplexCategory.Truncated.inclusion k).op.obj (op (topTruncatedSimplex k)) ⟶ op ⦋n⦌
      from α.1.op)

private abbrev topMonoStructuredArrow {k n : ℕ} (β : topMonoIndex k n) :
    StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op :=
  StructuredArrow.mk
    (show op ⦋n⦌ ⟶ (SimplexCategory.Truncated.inclusion k).op.obj (op (topTruncatedSimplex k))
      from β.1.op)

/-- The canonical map from the `α`-indexed top summand `A` into degree `n` of
`i_{k!} (single_degree_truncated A k)`. -/
noncomputable def singleDegreeTruncatedSkι (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F]
    (α : topEpiIndex k n) :
    B ⟶ (((Truncated.sk k).obj (single_degree_truncated B k)) _⦋n⦌) :=
  (singleDegreeTruncatedTopIso B k).hom ≫
    colimit.ι
      (CostructuredArrow.proj (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌) ⋙
        single_degree_truncated B k)
      (topEpiCostructuredArrow α) ≫
    ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionObjIsoColimit
      (single_degree_truncated B k) (op ⦋n⦌)).inv

/-- The canonical projection from degree `n` of `cosk_k (single_degree_truncated A k)` to the
`β`-indexed copy of `A`. -/
noncomputable def singleDegreeTruncatedCoskπ (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    (β : topMonoIndex k n) :
    (((Truncated.cosk k).obj (single_degree_truncated B k)) _⦋n⦌) ⟶ B :=
  ((SimplexCategory.Truncated.inclusion k).op.ranObjObjIsoLimit
      (single_degree_truncated B k) (op ⦋n⦌)).hom ≫
    limit.π
      (StructuredArrow.proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op ⋙
        single_degree_truncated B k)
      (topMonoStructuredArrow β) ≫
    (singleDegreeTruncatedTopIso B k).inv

/-- The source-facing vanishing condition for the degree-`k` component of a map out of
`single_degree_truncated B k`. For `k = n + 1` this requires vanishing after all top face maps
`d_i^(n + 1)`. -/
def singleDegreeTruncatedFaceCondition {k : ℕ}
    (V : SimplicialObject.Truncated A k) {B : A}
    (f : B ⟶ V _⦋k,le_rfl⦌ₖ) : Prop :=
  match k with
  | 0 => True
  | n + 1 =>
      ∀ i : Fin (n + 2),
        f ≫ V.map (SimplexCategory.Truncated.δ (n + 1) i (by simp) (by simp)).op = 0

/-- The source-facing vanishing condition for the degree-`k` component of a map into
`single_degree_truncated B k`. For `k = n + 1` this requires vanishing after all top degeneracy
maps `s_i^n`. -/
def singleDegreeTruncatedDegeneracyCondition {k : ℕ}
    (V : SimplicialObject.Truncated A k) {B : A}
    (f : V _⦋k,le_rfl⦌ₖ ⟶ B) : Prop :=
  match k with
  | 0 => True
  | n + 1 =>
      ∀ i : Fin (n + 1),
        V.map (SimplexCategory.Truncated.σ (n + 1) i (by simp) (by simp)).op ≫ f = 0

-- Proof sketch: a natural transformation out of `single_degree_truncated A k` is determined by its
-- degree-`k` component, and naturality against the top cofaces forces the stated vanishing
-- conditions.
/-- Maps from the concentrated `k`-truncated simplicial object are canonically the same as maps
from `A` to the top degree satisfying the top face vanishing conditions. -/
private theorem existsUnique_singleDegreeTruncated_homEquiv
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k) :
    ∃! e : (single_degree_truncated B k ⟶ V) ≃
        { f : B ⟶ V _⦋k, le_rfl⦌ₖ // singleDegreeTruncatedFaceCondition V f },
      ∀ f : single_degree_truncated B k ⟶ V,
        (e f).1 = (singleDegreeTruncatedTopIso B k).hom ≫ f.app (op (topTruncatedSimplex k)) := by
  sorry

/-- The canonical Hom-set description for maps out of the concentrated `k`-truncated object. -/
noncomputable def singleDegreeTruncated_homEquiv
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k) :
    (single_degree_truncated B k ⟶ V) ≃
      { f : B ⟶ V _⦋k, le_rfl⦌ₖ // singleDegreeTruncatedFaceCondition V f } :=
  Classical.choose (existsUnique_singleDegreeTruncated_homEquiv B k V)

@[simp] theorem singleDegreeTruncated_homEquiv_apply
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (f : single_degree_truncated B k ⟶ V) :
    (singleDegreeTruncated_homEquiv B k V f).1 =
      (singleDegreeTruncatedTopIso B k).hom ≫ f.app (op (topTruncatedSimplex k)) := by
  rcases Classical.choose_spec (existsUnique_singleDegreeTruncated_homEquiv B k V) with
    ⟨happly, -⟩
  exact happly f

-- Proof sketch: dually, a natural transformation into `single_degree_truncated A k` is determined
-- by its degree-`k` component, and naturality against the top degeneracies forces the stated
-- vanishing conditions.
/-- Maps into the concentrated `k`-truncated simplicial object are canonically the same as maps
from the top degree to `A` satisfying the top degeneracy vanishing conditions. -/
private theorem existsUnique_hom_singleDegreeTruncatedEquiv
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k) :
    ∃! e : (V ⟶ single_degree_truncated B k) ≃
        { f : V _⦋k, le_rfl⦌ₖ ⟶ B // singleDegreeTruncatedDegeneracyCondition V f },
      ∀ f : V ⟶ single_degree_truncated B k,
        (e f).1 = f.app (op (topTruncatedSimplex k)) ≫ (singleDegreeTruncatedTopIso B k).inv := by
  sorry

/-- The canonical Hom-set description for maps into the concentrated `k`-truncated object. -/
noncomputable def hom_singleDegreeTruncatedEquiv
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k) :
    (V ⟶ single_degree_truncated B k) ≃
      { f : V _⦋k, le_rfl⦌ₖ ⟶ B // singleDegreeTruncatedDegeneracyCondition V f } :=
  Classical.choose (existsUnique_hom_singleDegreeTruncatedEquiv B k V)

@[simp] theorem hom_singleDegreeTruncatedEquiv_apply
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (f : V ⟶ single_degree_truncated B k) :
    (hom_singleDegreeTruncatedEquiv B k V f).1 =
      f.app (op (topTruncatedSimplex k)) ≫ (singleDegreeTruncatedTopIso B k).inv := by
  rcases Classical.choose_spec (existsUnique_hom_singleDegreeTruncatedEquiv B k V) with
    ⟨happly, -⟩
  exact happly f

-- Proof sketch: under the pointwise colimit formula for `Truncated.sk k`, only the top-degree
-- objects survive, and those surviving objects are indexed by the surjections `[n] ↠ [k]`.
/-- Degreewise description of `i_{k!}` on the concentrated `k`-truncated object. -/
private theorem existsUnique_singleDegreeTruncatedSkObjIso
    [HasFiniteBiproducts A] (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F] :
    ∃! e :
        (((Truncated.sk k).obj (single_degree_truncated B k)) _⦋n⦌) ≅
          ⨁ fun _ : topEpiIndex k n ↦ B,
      ∀ α : topEpiIndex k n,
        singleDegreeTruncatedSkι B k n α ≫ e.hom =
          biproduct.ι (fun _ : topEpiIndex k n ↦ B) α := by
  sorry

/-- The canonical degree-`n` biproduct decomposition of
`i_{k!} (single_degree_truncated A k)`. -/
noncomputable def singleDegreeTruncatedSkObjIso
    [HasFiniteBiproducts A] (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F] :
    (((Truncated.sk k).obj (single_degree_truncated B k)) _⦋n⦌) ≅
      ⨁ fun _ : topEpiIndex k n ↦ B :=
  Classical.choose (existsUnique_singleDegreeTruncatedSkObjIso B k n)

@[simp] theorem singleDegreeTruncatedSkObjIso_ι
    [HasFiniteBiproducts A] (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F]
    (α : topEpiIndex k n) :
    singleDegreeTruncatedSkι B k n α ≫ (singleDegreeTruncatedSkObjIso B k n).hom =
      biproduct.ι (fun _ : topEpiIndex k n ↦ B) α := by
  rcases Classical.choose_spec (existsUnique_singleDegreeTruncatedSkObjIso B k n) with
    ⟨hι, -⟩
  exact hι α

-- Proof sketch: the structure map on `i_{k!}` is induced by reindexing costructured arrows; on the
-- surviving top-degree summands this sends the `α`-summand to the `(φ ≫ α)`-summand when the
-- composite stays surjective, and otherwise to zero.
/-- The simplicial structure maps on `i_{k!} (single_degree_truncated A k)` act on surjection
summands by postcomposition. -/
theorem singleDegreeTruncatedSk_map_ι
    (B : A) (k n n' : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F]
    (φ : ⦋n⦌ ⟶ ⦋n'⦌) (α : topEpiIndex k n')
    (h : Epi (φ ≫ α.1)) :
    singleDegreeTruncatedSkι B k n' α ≫
        ((Truncated.sk k).obj (single_degree_truncated B k)).map φ.op =
      singleDegreeTruncatedSkι B k n ⟨φ ≫ α.1, h⟩ := by
  sorry

/-- If the postcomposition `φ ≫ α` is not surjective, then the corresponding summand map in
`i_{k!} (single_degree_truncated B k)` is zero. -/
theorem singleDegreeTruncatedSk_map_ι_of_not_epi
    (B : A) (k n n' : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F]
    (φ : ⦋n⦌ ⟶ ⦋n'⦌) (α : topEpiIndex k n')
    (h : ¬ Epi (φ ≫ α.1)) :
    singleDegreeTruncatedSkι B k n' α ≫
        ((Truncated.sk k).obj (single_degree_truncated B k)).map φ.op =
      0 := by
  sorry

-- Proof sketch: under the pointwise limit formula for `Truncated.cosk k`, only the top-degree
-- objects survive, and those surviving objects are indexed by the injections `[k] ↪ [n]`; the
-- assumed finite biproducts identify the resulting finite product with the corresponding biproduct.
/-- Degreewise description of `cosk_k` on the concentrated `k`-truncated object. -/
private theorem existsUnique_singleDegreeTruncatedCoskObjIso
    [HasFiniteBiproducts A] (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F] :
    ∃! e :
        (((Truncated.cosk k).obj (single_degree_truncated B k)) _⦋n⦌) ≅
          ⨁ fun _ : topMonoIndex k n ↦ B,
      ∀ β : topMonoIndex k n,
        e.hom ≫ biproduct.π (fun _ : topMonoIndex k n ↦ B) β =
          singleDegreeTruncatedCoskπ B k n β := by
  sorry

/-- The canonical degree-`n` biproduct decomposition of
`cosk_k (single_degree_truncated A k)`. -/
noncomputable def singleDegreeTruncatedCoskObjIso
    [HasFiniteBiproducts A] (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F] :
    (((Truncated.cosk k).obj (single_degree_truncated B k)) _⦋n⦌) ≅
      ⨁ fun _ : topMonoIndex k n ↦ B :=
  Classical.choose (existsUnique_singleDegreeTruncatedCoskObjIso B k n)

@[simp] theorem singleDegreeTruncatedCoskObjIso_π
    [HasFiniteBiproducts A] (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    (β : topMonoIndex k n) :
    (singleDegreeTruncatedCoskObjIso B k n).hom ≫
        biproduct.π (fun _ : topMonoIndex k n ↦ B) β =
      singleDegreeTruncatedCoskπ B k n β := by
  rcases Classical.choose_spec (existsUnique_singleDegreeTruncatedCoskObjIso B k n) with
    ⟨hπ, -⟩
  exact hπ β

-- Proof sketch: the structure map on `cosk_k` is induced by reindexing structured arrows; on the
-- surviving top-degree projections this sends the `β`-projection to the `(β ≫ φ)`-projection when the
-- composite stays injective, and otherwise to zero.
/-- The simplicial structure maps on `cosk_k (single_degree_truncated A k)` act on injection
summands, dually via the canonical biproduct projections, by precomposition. -/
theorem singleDegreeTruncatedCosk_map_π
    (B : A) (k n n' : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    (φ : ⦋n⦌ ⟶ ⦋n'⦌) (β : topMonoIndex k n)
    (h : Mono (β.1 ≫ φ)) :
    ((Truncated.cosk k).obj (single_degree_truncated B k)).map φ.op ≫
        singleDegreeTruncatedCoskπ B k n β =
      singleDegreeTruncatedCoskπ B k n' ⟨β.1 ≫ φ, h⟩ := by
  sorry

/-- If the precomposition `β ≫ φ` is not injective, then the corresponding projection in
`cosk_k (single_degree_truncated B k)` is zero. -/
theorem singleDegreeTruncatedCosk_map_π_of_not_mono
    (B : A) (k n n' : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    (φ : ⦋n⦌ ⟶ ⦋n'⦌) (β : topMonoIndex k n)
    (h : ¬ Mono (β.1 ≫ φ)) :
    ((Truncated.cosk k).obj (single_degree_truncated B k)).map φ.op ≫
        singleDegreeTruncatedCoskπ B k n β =
      0 := by
  sorry

-- Proof sketch: the comparison map is the adjoint transpose of the inverse unit. Under the
-- source-facing degreewise decompositions, its `(α, β)`-entry is `𝟙_A` exactly when `β` is a
-- section of `α`, and otherwise it is zero.
/-- In the source-facing degreewise formulas, the comparison
`i_{k!} (single_degree_truncated A k) ⟶ cosk_k (single_degree_truncated A k)` has the textbook
matrix coefficients. -/
theorem singleDegreeTruncated_skToCosk_ι_π
    (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F]
    (α : topEpiIndex k n) (β : topMonoIndex k n) :
    singleDegreeTruncatedSkι B k n α ≫
        (single_degree_truncated B k).skToCosk.app (op ⦋n⦌) ≫
        singleDegreeTruncatedCoskπ B k n β =
      if β.1 ≫ α.1 = 𝟙 (⦋k⦌) then 𝟙 B else 0 := by
  sorry

end Concentrated

end ComparisonBridge

end SimplicialObject.Truncated

section ComparisonMono

variable [HasZeroObject A] [HasZeroMorphisms A]

-- Proof sketch: the source-facing coefficient formula above shows that each degree component of
-- the comparison map for the concentrated object is monomorphic. The normalized-Moore criterion
-- from the previous chapter then upgrades this degreewise statement to a simplicial monomorphism.
/-- Lemma 14.22.2: for the concentrated `k`-truncated simplicial object with value `A`, the
canonical comparison map
`i_{k!} (single_degree_truncated A k) ⟶ cosk_k (single_degree_truncated A k)` is a
monomorphism. -/
theorem singleDegreeTruncated_skToCosk_mono
    (B : A) (k : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F] :
    Mono (single_degree_truncated B k).skToCosk := by
  sorry

end ComparisonMono

end CategoryTheory

/-! ### Definition_14_22_3 (from Chap14) -/
open CategoryTheory
open Abelian.DoldKan
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open HomologicalComplex
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory

section Concentrated

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜] [HasZeroMorphisms 𝒜]

/- Domain-style sampling for Definition 14.22.3:
- primary domain: truncated simplicial objects as functors on `(SimplexCategory.Truncated k)ᵒᵖ`,
  together with the simplicial operators on the top truncated simplex;
- sampled owner declarations:
  `SimplexCategory.Truncated`,
  `SimplexCategory.eq_σ_comp_of_not_injective`,
  `SimplexCategory.eq_id_of_mono`,
  `SimplicialObject.Truncated.sk`;
- best owner abstraction:
  `source-facing`: the `k`-truncated simplicial object concentrated in degree `k` with value `A`,
    whose non-identity endomorphisms of the top simplex act trivially because they factor through
    lower degrees;
  `core/canonical`: `SimplicialObject.Truncated 𝒜 k`;
  `bridge/view`: the skeleton extension `SimplicialObject.Truncated.sk k` and the Dold-Kan
    comparison at the end of the file.
- primitive data: only the object `A` and the degree `k`;
- derived API: the top-degree evaluation lemma, the skeleton extension
  `eilenberg_maclane_object A k`, and its comparison with `Γ.obj ((single ...).obj A)`.

Source/core/bridge triage:
- `source-facing`: `single_degree_truncated`;
- `core/canonical`: the functor-category owner `SimplicialObject.Truncated 𝒜 k`;
- `bridge/view`: the skeleton and Dold-Kan comparison. -/

/-- The object part of the `k`-truncated simplicial object concentrated in degree `k` with value
`A`. -/
private def single_degree_truncated_obj (A : 𝒜) (k : ℕ) : (SimplexCategory.Truncated k)ᵒᵖ → 𝒜 :=
  fun X ↦ if X.unop.1.len = k then A else ⊥_ 𝒜

-- Proof sketch: unfold `single_degree_truncated_obj`; the hypothesis forces the `if` to reduce to
-- the branch with value `A`.
/-- At the top degree `k`, the concentrated truncated simplicial object has value `A`. -/
private theorem single_degree_truncated_obj_eq_top
    (A : 𝒜) (k : ℕ) (X : (SimplexCategory.Truncated k)ᵒᵖ)
    (hX : X.unop.1.len = k) :
    single_degree_truncated_obj A k X = A := sorry

private theorem truncated_simplex_eq_top
    {k : ℕ} {X : (SimplexCategory.Truncated k)ᵒᵖ} (hX : X.unop.1.len = k) :
    X.unop.1 = ⦋k⦌ := by
  simpa [hX] using (SimplexCategory.mk_len X.unop.1).symm

/-- Transport a top-degree morphism of the truncated simplex category to an endomorphism of
`[k]`. -/
private def single_degree_truncated_top_endo {k : ℕ}
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y)
    (hX : X.unop.1.len = k) (hY : Y.unop.1.len = k) : ⦋k⦌ ⟶ ⦋k⦌ :=
  eqToHom (truncated_simplex_eq_top hY).symm ≫ f.unop.hom ≫
    eqToHom (truncated_simplex_eq_top hX)

/-- The morphism part of the `k`-truncated simplicial object concentrated in degree `k` with value
`A`. The canonical identity of the top simplex acts by `𝟙 A`, while every other top-degree
operator acts by `0` because it factors through lower degrees. -/
private def single_degree_truncated_map (A : 𝒜) (k : ℕ)
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y) :
    single_degree_truncated_obj A k X ⟶ single_degree_truncated_obj A k Y :=
  if hX : X.unop.1.len = k then
    if hY : Y.unop.1.len = k then
      if single_degree_truncated_top_endo f hX hY = 𝟙 ⦋k⦌ then
        eqToHom (single_degree_truncated_obj_eq_top A k X hX) ≫
          eqToHom (single_degree_truncated_obj_eq_top A k Y hY).symm
      else 0
    else 0
  else 0

-- Proof sketch: after transporting a top-degree morphism to an endomorphism of `⦋k⦌`, only the
-- canonical identity acts by `𝟙 A`; every other top-degree operator is sent to `0`, and outside
-- the top degree the functor is already zero.
/-- The concentrated degree-`k` map assignment preserves identities. -/
private theorem single_degree_truncated_map_id
    (A : 𝒜) (k : ℕ) (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    single_degree_truncated_map A k (𝟙 X) = 𝟙 (single_degree_truncated_obj A k X) := sorry

-- Proof sketch: check the cases according to whether each object is in degree `k`; away from the
-- top degree all maps are zero, and in top degree the transported endomorphism monoid acts by the
-- indicator of the canonical identity endomorphism.
/-- The concentrated degree-`k` map assignment preserves composition. -/
private theorem single_degree_truncated_map_comp
    (A : 𝒜) (k : ℕ) {X Y Z : (SimplexCategory.Truncated k)ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    single_degree_truncated_map A k (f ≫ g) =
      single_degree_truncated_map A k f ≫ single_degree_truncated_map A k g := sorry

/-- The `k`-truncated simplicial object concentrated in degree `k` with value `A`. -/
def single_degree_truncated (A : 𝒜) (k : ℕ) : SimplicialObject.Truncated 𝒜 k where
  obj := single_degree_truncated_obj A k
  map f := single_degree_truncated_map A k f
  map_id X := single_degree_truncated_map_id A k X
  map_comp f g := single_degree_truncated_map_comp A k f g

/-- The concentrated truncated simplicial object has value `A` in top degree. -/
@[simp] theorem single_degree_truncated_obj_top (A : 𝒜) (k : ℕ) :
    (single_degree_truncated A k).obj (Opposite.op ⦋k, le_rfl⦌ₖ) = A :=
  single_degree_truncated_obj_eq_top A k (Opposite.op ⦋k, le_rfl⦌ₖ) rfl

end Concentrated

section EilenbergMacLane

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜] [HasZeroMorphisms 𝒜]
variable [HasFiniteColimits 𝒜]

/-- Definition 14.22.3: the source defines the Eilenberg-MacLane object in an abelian category,
but the underlying skeleton construction already makes sense in any category with zero morphisms,
a zero object, and finite colimits. -/
noncomputable def eilenberg_maclane_object (A : 𝒜) (k : ℕ) : SimplicialObject 𝒜 :=
  (SimplicialObject.Truncated.sk k).obj (single_degree_truncated A k)

/-- Textbook notation for the Eilenberg-MacLane simplicial object. -/
scoped[Simplicial] notation:max "K(" A ", " k ")" => eilenberg_maclane_object A k

end EilenbergMacLane

section DoldKan

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The Eilenberg-MacLane object is the Dold-Kan image of the single complex concentrated in
degree `k`. -/
private theorem eilenberg_maclane_object_eq_gamma_single (A : 𝒜) (k : ℕ) :
    K(A, k) = Γ.obj ((single 𝒜 (ComplexShape.down ℕ) k).obj A) := by
  sorry

/-- The canonical isomorphism from the Eilenberg-MacLane object to the Dold-Kan image of the
single complex concentrated in degree `k`. -/
noncomputable abbrev eilenbergMacLaneObjectIsoDoldKanSingle (A : 𝒜) (k : ℕ) :
    K(A, k) ≅ Γ.obj ((single 𝒜 (ComplexShape.down ℕ) k).obj A) :=
  eqToIso (eilenberg_maclane_object_eq_gamma_single A k)

/-- The canonical comparison from the normalized Moore complex of `K(A, k)` to the single complex
concentrated in degree `k`. -/
noncomputable def eilenbergMacLaneObjectNormalizedMooreComplexIsoSingle
    (A : 𝒜) (k : ℕ) :
    (AlgebraicTopology.normalizedMooreComplex 𝒜).obj (K(A, k)) ≅
      (single 𝒜 (ComplexShape.down ℕ) k).obj A :=
  (AlgebraicTopology.normalizedMooreComplex 𝒜).mapIso
      (eilenbergMacLaneObjectIsoDoldKanSingle A k) ≪≫
    equivalence.counitIso.app ((single 𝒜 (ComplexShape.down ℕ) k).obj A)

end DoldKan

end CategoryTheory

/-! ### Lemma_14_22_4 (from Chap14) -/
/- Source/core/bridge triage for Lemma 14.22.4:
- primary domain: Dold-Kan images of two-term chain complexes and the induced short complexes of
  simplicial objects.
- inspected owner declarations:
  `eilenbergMacLaneObjectIsoDoldKanSingle`,
  `HomologicalComplex.double`,
  `ShortComplex.ShortExact`,
  `ShortComplex.Splitting.shortExact`.
- best owner abstraction: the source-facing short complex
  `eilenberg_maclane_object A k ⟶ E ⟶ eilenberg_maclane_object A (k + 1)`.
  The two-term `double (𝟙 A)` chain complex and its Dold-Kan image are bridge/model data for that
  owner, while `ShortComplex`, `ShortComplex.ShortExact`, and
  `ShortComplex.Splitting.shortExact` provide the core API.
- layer: `source-facing`; the lemma constructs the extension short complex itself, rather than
  merely recalling a pre-existing exactness theorem.
- primitive data: the two-term chain complex `double (𝟙 A) ...`, its inclusion/projection chain
  maps, the Dold-Kan image `E`, and the comparison theorem from `eilenberg_maclane_object` to
  the Dold-Kan model of the single complex.
- derived API: short exactness and canonical termwise splittings of the associated simplicial
  short complex.
-/

open CategoryTheory Category Limits ZeroObject Abelian.DoldKan HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

private instance gammaPreservesZeroMorphisms :
    (Γ : ChainComplex 𝒜 ℕ ⥤ SimplicialObject 𝒜).PreservesZeroMorphisms where
  map_zero K L := by
    ext Δ
    apply (AlgebraicTopology.DoldKan.Γ₀.splitting K).hom_ext'
    intro B
    calc
      (((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj B ≫
          (AlgebraicTopology.DoldKan.Γ₀.splitting K).desc Δ
            (fun A ↦
              (0 : K.X A.1.unop.len ⟶ L.X A.1.unop.len) ≫
                ((AlgebraicTopology.DoldKan.Γ₀.splitting L).cofan Δ).inj A)) =
          0 ≫ ((AlgebraicTopology.DoldKan.Γ₀.splitting L).cofan Δ).inj B := by
            simpa using
              (AlgebraicTopology.DoldKan.Γ₀.splitting K).ι_desc Δ
                (fun A ↦
                  (0 : K.X A.1.unop.len ⟶ L.X A.1.unop.len) ≫
                    ((AlgebraicTopology.DoldKan.Γ₀.splitting L).cofan Δ).inj A)
                B
      _ = 0 := by exact zero_comp
      _ = ((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj B ≫ 0 := by
            rw [comp_zero]

private abbrev eilenbergMacLaneExtensionRel (k : ℕ) : (ComplexShape.down ℕ).Rel (k + 1) k := rfl

/-- The two-term chain complex with `A` in degrees `k + 1` and `k`, and differential `𝟙 A`
from degree `k + 1` to degree `k`. -/
abbrev eilenbergMacLaneExtensionComplex (A : 𝒜) (k : ℕ) : ChainComplex 𝒜 ℕ :=
  double (𝟙 A) (eilenbergMacLaneExtensionRel k)

/-- The simplicial object `E` obtained from the two-term identity complex by the Dold-Kan
equivalence; degreewise this matches the textbook direct-sum construction. -/
abbrev eilenbergMacLaneExtension (A : 𝒜) (k : ℕ) : SimplicialObject 𝒜 :=
  Γ.obj (eilenbergMacLaneExtensionComplex A k)

private noncomputable def eilenbergMacLaneExtensionComplexDiffIso (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).X (k + 1) ≅
      (eilenbergMacLaneExtensionComplex A k).X k :=
  (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)) ≪≫ (Iso.refl A) ≪≫
    (doubleXIso₁ (𝟙 A) (eilenbergMacLaneExtensionRel k) (Nat.succ_ne_self k)).symm

private lemma eilenbergMacLaneExtensionComplex_d_eq
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).d (k + 1) k =
      (eilenbergMacLaneExtensionComplexDiffIso A k).hom := by
  simp [eilenbergMacLaneExtensionComplex, eilenbergMacLaneExtensionComplexDiffIso,
    HomologicalComplex.double_d]

private lemma eilenbergMacLaneExtensionComplex_left_g_eq_zero
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).d k ((ComplexShape.down ℕ).next k) = 0 := by
  cases k with
  | zero =>
      rw [ChainComplex.next_nat_zero]
      change (double (𝟙 A) (eilenbergMacLaneExtensionRel 0)).d 0 0 = 0
      exact HomologicalComplex.double_d_eq_zero₀
        (𝟙 A) (eilenbergMacLaneExtensionRel 0) 0 0 Nat.zero_ne_one
  | succ n =>
      rw [ChainComplex.next_nat_succ]
      simpa [eilenbergMacLaneExtensionComplex] using
        (HomologicalComplex.double_d_eq_zero₁
          (𝟙 A) (eilenbergMacLaneExtensionRel (n + 1)) (n + 1) n (by simp : n ≠ n + 1))

private lemma eilenbergMacLaneExtensionComplex_right_f_eq_zero
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).d (k + 2) (k + 1) = 0 := by
  simpa [eilenbergMacLaneExtensionComplex] using
    (HomologicalComplex.double_d_eq_zero₀
      (𝟙 A) (eilenbergMacLaneExtensionRel k) (k + 2) (k + 1) (by omega : k + 2 ≠ k + 1))

private lemma eilenbergMacLaneExtensionComplex_isZero_X
    (A : 𝒜) (k n : ℕ) (hk : n ≠ k) (hk1 : n ≠ k + 1) :
    IsZero ((eilenbergMacLaneExtensionComplex A k).X n) := by
  simpa [eilenbergMacLaneExtensionComplex] using
    (HomologicalComplex.isZero_double_X
      (𝟙 A) (eilenbergMacLaneExtensionRel k) n hk1 hk)

private lemma eilenbergMacLaneExtensionComplex_leftShortComplex_exact
    (A : 𝒜) (k : ℕ) :
    (ShortComplex.mk
      (eilenbergMacLaneExtensionComplexDiffIso A k).hom
      (0 : (eilenbergMacLaneExtensionComplex A k).X k ⟶
        (eilenbergMacLaneExtensionComplex A k).X ((ComplexShape.down ℕ).next k))
      (by simp)).Exact := by
  let w :
      (eilenbergMacLaneExtensionComplexDiffIso A k).hom ≫
        (0 : (eilenbergMacLaneExtensionComplex A k).X k ⟶
          (eilenbergMacLaneExtensionComplex A k).X ((ComplexShape.down ℕ).next k)) = 0 := by
    simp
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι'
    ((eilenbergMacLaneExtensionComplexDiffIso A k).hom) w
    (fun {Z} g hg ↦ ⟨g ≫ (eilenbergMacLaneExtensionComplexDiffIso A k).inv, by simp⟩)

private lemma eilenbergMacLaneExtensionComplex_rightShortComplex_exact
    (A : 𝒜) (k : ℕ) :
    (ShortComplex.mk
      (0 : (eilenbergMacLaneExtensionComplex A k).X (k + 2) ⟶
        (eilenbergMacLaneExtensionComplex A k).X (k + 1))
      (eilenbergMacLaneExtensionComplexDiffIso A k).hom
      (by simp)).Exact := by
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk
      (0 : (eilenbergMacLaneExtensionComplex A k).X (k + 2) ⟶
        (eilenbergMacLaneExtensionComplex A k).X (k + 1))
      (eilenbergMacLaneExtensionComplexDiffIso A k).hom
      (by simp)
  have hS : S.Splitting :=
    ShortComplex.Splitting.ofIsZeroOfIsIso S
      (eilenbergMacLaneExtensionComplex_isZero_X A k (k + 2) (by omega) (by omega))
      inferInstance
  exact
    hS.shortExact.exact

private lemma eilenbergMacLaneExtensionComplex_exactAt
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).ExactAt k := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 1) k ((ComplexShape.down ℕ).next k)]
  · refine (ShortComplex.exact_iff_of_iso ?_).1
      (eilenbergMacLaneExtensionComplex_leftShortComplex_exact A k)
    refine ShortComplex.isoMk
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · simpa using eilenbergMacLaneExtensionComplex_d_eq A k
    · simpa using
        eilenbergMacLaneExtensionComplex_left_g_eq_zero A k
  · simp [ChainComplex.prev]
  · rfl

private lemma eilenbergMacLaneExtensionComplex_exactAt_succ
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k]
  · refine (ShortComplex.exact_iff_of_iso ?_).1
      (eilenbergMacLaneExtensionComplex_rightShortComplex_exact A k)
    refine ShortComplex.isoMk
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · simpa using
        eilenbergMacLaneExtensionComplex_right_f_eq_zero A k
    · simpa using
        eilenbergMacLaneExtensionComplex_d_eq A k
  · simp [ChainComplex.prev]
  · exact ChainComplex.next_nat_succ k

-- Proof sketch: the model complex is the two-term identity complex `A --𝟙--> A` in degrees
-- `k + 1` and `k`; exactness at the two nonzero degrees comes from the differential being an
-- isomorphism, and all other degrees vanish.
/-- The two-term chain-complex model underlying `eilenbergMacLaneExtension A k` is acyclic. -/
theorem eilenbergMacLaneExtensionComplex_acyclic (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).Acyclic := by
  intro i
  by_cases hk : i = k
  · simpa [hk] using eilenbergMacLaneExtensionComplex_exactAt A k
  by_cases hk1 : i = k + 1
  · simpa [hk1] using eilenbergMacLaneExtensionComplex_exactAt_succ A k
  · rw [HomologicalComplex.exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ <| by
      exact eilenbergMacLaneExtensionComplex_isZero_X A k i hk hk1

-- Proof sketch: the double complex has only one nonzero differential, from degree `k + 1` to
-- degree `k`; every differential out of degree `k` is therefore zero.
/-- The degree-`k` component of the double complex gives a chain map from the single complex in
degree `k` into the two-term extension complex. -/
private theorem eilenbergMacLaneExtensionInclusionChainMap_comm (A : 𝒜) (k i : ℕ)
    (hi : (ComplexShape.down ℕ).Rel k i) :
    (doubleXIso₁ (𝟙 A) (eilenbergMacLaneExtensionRel k)
      (Nat.succ_ne_self k)).inv ≫
      (eilenbergMacLaneExtensionComplex A k).d k i = 0 := by
  have hi' : i ≠ k := by
    intro h
    subst h
    simp at hi
  simpa [eilenbergMacLaneExtensionComplex] using
    show
      (doubleXIso₁ (𝟙 A) (eilenbergMacLaneExtensionRel k) (Nat.succ_ne_self k)).inv ≫
        (double (𝟙 A) (eilenbergMacLaneExtensionRel k)).d k i = 0 by
      rw [HomologicalComplex.double_d_eq_zero₁ (𝟙 A) (eilenbergMacLaneExtensionRel k) k i hi']
      simp

/-- The chain map from the complex concentrated in degree `k` into the two-term extension
complex. -/
private noncomputable abbrev eilenbergMacLaneExtensionInclusionChainMap (A : 𝒜) (k : ℕ) :
    (single 𝒜 (ComplexShape.down ℕ) k).obj A ⟶
      eilenbergMacLaneExtensionComplex A k :=
  mkHomFromSingle
    ((doubleXIso₁ (𝟙 A) (eilenbergMacLaneExtensionRel k)
      (Nat.succ_ne_self k)).inv)
    (eilenbergMacLaneExtensionInclusionChainMap_comm A k)

-- Proof sketch: the only nonzero differential of the double complex ends in degree `k`, so every
-- differential landing in degree `k + 1` is zero.
/-- The degree-`k + 1` component of the double complex gives a chain map from the two-term
extension complex to the single complex in degree `k + 1`. -/
private theorem eilenbergMacLaneExtensionProjectionChainMap_comm (A : 𝒜) (k i : ℕ)
    (hi : (ComplexShape.down ℕ).Rel i (k + 1)) :
    (eilenbergMacLaneExtensionComplex A k).d i (k + 1) ≫
      (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).hom = 0 :=
  by
    have hi' : i ≠ k + 1 := by
      intro h
      subst h
      simp at hi
    simpa [eilenbergMacLaneExtensionComplex] using
      show
        (double (𝟙 A) (eilenbergMacLaneExtensionRel k)).d i (k + 1) ≫
          (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).hom = 0 by
        rw [HomologicalComplex.double_d_eq_zero₀ (𝟙 A) (eilenbergMacLaneExtensionRel k) i
          (k + 1) hi']
        simp

/-- The chain map from the two-term extension complex to the complex concentrated in degree
`k + 1`. -/
private noncomputable abbrev eilenbergMacLaneExtensionProjectionChainMap (A : 𝒜) (k : ℕ) :
    eilenbergMacLaneExtensionComplex A k ⟶
      (single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A :=
  mkHomToSingle
    ((doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).hom)
    (eilenbergMacLaneExtensionProjectionChainMap_comm A k)

private lemma eilenbergMacLaneExtensionProjectionChainMap_f_eq_zero
    (A : 𝒜) (k n : ℕ) (hk1 : n ≠ k + 1) :
    (eilenbergMacLaneExtensionProjectionChainMap A k).f n = 0 := by
  dsimp [eilenbergMacLaneExtensionProjectionChainMap, HomologicalComplex.mkHomToSingle]
  simp [hk1]

private lemma eilenbergMacLaneExtensionInclusionChainMap_component_isIso
    (A : 𝒜) (k n : ℕ) (h : n = k) :
    IsIso ((eilenbergMacLaneExtensionInclusionChainMap A k).f n) := by
  subst n
  dsimp [eilenbergMacLaneExtensionInclusionChainMap, HomologicalComplex.mkHomFromSingle]
  split_ifs with hi
  · infer_instance
  · exact (hi rfl).elim

private lemma eilenbergMacLaneExtensionProjectionChainMap_component_isIso
    (A : 𝒜) (k n : ℕ) (h : n = k + 1) :
    IsIso ((eilenbergMacLaneExtensionProjectionChainMap A k).f n) := by
  subst n
  dsimp [eilenbergMacLaneExtensionProjectionChainMap, HomologicalComplex.mkHomToSingle]
  split_ifs with hi
  · infer_instance
  · exact (hi rfl).elim

-- Proof sketch: in the two-term model, the projection kills the `k`-summand and the inclusion
-- lands entirely in that summand.
/-- The inclusion and projection chain maps for the two-term model compose to zero. -/
private theorem eilenbergMacLaneExtensionModel_comp_zero (A : 𝒜) (k : ℕ) :
    eilenbergMacLaneExtensionInclusionChainMap A k ≫
      eilenbergMacLaneExtensionProjectionChainMap A k = 0 := by
  refine HomologicalComplex.from_single_hom_ext ?_
  dsimp [eilenbergMacLaneExtensionInclusionChainMap,
    eilenbergMacLaneExtensionProjectionChainMap, HomologicalComplex.mkHomFromSingle,
    HomologicalComplex.mkHomToSingle]
  simp

/-- The short complex on chain complexes whose Dold-Kan image gives the extension sequence. -/
private noncomputable abbrev eilenbergMacLaneExtensionModelShortComplex
    (A : 𝒜) (k : ℕ) : ShortComplex (ChainComplex 𝒜 ℕ) :=
  ShortComplex.mk
    (eilenbergMacLaneExtensionInclusionChainMap A k)
    (eilenbergMacLaneExtensionProjectionChainMap A k)
    (eilenbergMacLaneExtensionModel_comp_zero A k)

private noncomputable def gammaSplitting (K : ChainComplex 𝒜 ℕ) :
    SimplicialObject.Splitting (Γ.obj K) := by
  simpa [Abelian.DoldKan.Γ, Idempotents.DoldKan.Γ, AlgebraicTopology.DoldKan.Γ₀] using
    (AlgebraicTopology.DoldKan.Γ₀.splitting K)

private lemma gammaCofanInj_comp_app {K L : ChainComplex 𝒜 ℕ} (f : K ⟶ L)
    (Δ : SimplexCategoryᵒᵖ) (B : SimplicialObject.Splitting.IndexSet Δ) :
    ((gammaSplitting K).cofan Δ).inj B ≫ (Γ.map f).app Δ =
      f.f B.1.unop.len ≫ ((gammaSplitting L).cofan Δ).inj B := by
  simpa [gammaSplitting, Abelian.DoldKan.Γ, Idempotents.DoldKan.Γ, AlgebraicTopology.DoldKan.Γ₀]
    using
      (AlgebraicTopology.DoldKan.Γ₀.splitting K).ι_desc Δ
        (fun A ↦ f.f A.1.unop.len ≫ ((AlgebraicTopology.DoldKan.Γ₀.splitting L).cofan Δ).inj A)
        B

private lemma gammaSingleCofanInj_eq_zero
    (A : 𝒜) (k : ℕ) {Δ : SimplexCategoryᵒᵖ}
    (B : SimplicialObject.Splitting.IndexSet Δ) (h : B.1.unop.len ≠ k) :
    ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) k).obj A)).cofan Δ).inj B = 0 := by
  let hzero :=
    isZero_single_obj_X (ComplexShape.down ℕ) k A B.1.unop.len h
  exact hzero.eq_of_src _ _

private lemma gammaExtensionCofanInj_eq_zero
    (A : 𝒜) (k : ℕ) {Δ : SimplexCategoryᵒᵖ}
    (B : SimplicialObject.Splitting.IndexSet Δ)
    (hk : B.1.unop.len ≠ k) (hk1 : B.1.unop.len ≠ k + 1) :
    ((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B = 0 := by
  let hzero := eilenbergMacLaneExtensionComplex_isZero_X A k B.1.unop.len hk hk1
  exact hzero.eq_of_src _ _

/-- The short complex `K(A, k) ⟶ E ⟶ K(A, k + 1)` attached to the Eilenberg-MacLane extension. -/
abbrev eilenbergMacLaneExtensionShortComplex (A : 𝒜) (k : ℕ) :
    ShortComplex (SimplicialObject 𝒜) :=
  let e₁ := eilenbergMacLaneObjectIsoDoldKanSingle A k
  let e₃ := eilenbergMacLaneObjectIsoDoldKanSingle A (k + 1)
  { X₁ := K(A, k)
    X₂ := eilenbergMacLaneExtension A k
    X₃ := K(A, k + 1)
    f := e₁.hom ≫ ((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).f
    g := ((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).g ≫ e₃.inv
    zero := by
      let S := (eilenbergMacLaneExtensionModelShortComplex A k).map Γ
      have h :
          e₁.hom ≫ (S.f ≫ S.g) ≫ e₃.inv = e₁.hom ≫ 0 ≫ e₃.inv := by
        exact congrArg (fun t ↦ e₁.hom ≫ t ≫ e₃.inv) S.zero
      have h' : e₁.hom ≫ 0 ≫ e₃.inv = 0 := by simp
      exact (by simpa [Category.assoc] using h.trans h') }

private noncomputable def eilenbergMacLaneExtensionModelShortComplexGammaIso
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionModelShortComplex A k).map Γ ≅
      eilenbergMacLaneExtensionShortComplex A k :=
  ShortComplex.isoMk
    (eilenbergMacLaneObjectIsoDoldKanSingle A k).symm
    (Iso.refl _)
    (eilenbergMacLaneObjectIsoDoldKanSingle A (k + 1)).symm
    (by
      simp [eilenbergMacLaneExtensionShortComplex, eilenbergMacLaneExtensionModelShortComplex])
    (by
      simp [eilenbergMacLaneExtensionShortComplex, eilenbergMacLaneExtensionModelShortComplex])

-- Proof sketch: after evaluating the chain-level model at any degree, one gets one of the three
-- canonical split shapes `A ⟶ A ⟶ 0`, `0 ⟶ A ⟶ A`, or `0 ⟶ 0 ⟶ 0`, so the splitting is obtained
-- from the owner constructors `ShortComplex.Splitting.ofIsIsoOfIsZero` and
-- `ShortComplex.Splitting.ofIsZeroOfIsIso`.
/-- The degree-`n` evaluation of the chain-level short complex modeling the extension carries a
canonical splitting. -/
private noncomputable def eilenbergMacLaneExtensionModelShortComplex_degreewiseSplitting
    (A : 𝒜) (k n : ℕ) :
    ((eilenbergMacLaneExtensionModelShortComplex A k).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) n)).Splitting := by
  by_cases hk : n = k
  · subst n
    let S : ShortComplex 𝒜 :=
      (eilenbergMacLaneExtensionModelShortComplex A k).map
        (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) k)
    change S.Splitting
    have hf : IsIso S.f := by
      dsimp [S]
      simpa [eilenbergMacLaneExtensionModelShortComplex,
        eilenbergMacLaneExtensionInclusionChainMap,
        HomologicalComplex.mkHomFromSingle_f] using
        (show IsIso
          ((singleObjXSelf (ComplexShape.down ℕ) k A).hom ≫
            (doubleXIso₁ (𝟙 A) (eilenbergMacLaneExtensionRel k)
              (Nat.succ_ne_self k)).inv) from inferInstance)
    exact ShortComplex.Splitting.ofIsIsoOfIsZero S
      hf
      (by
        simpa [eilenbergMacLaneExtensionModelShortComplex] using
          (isZero_single_obj_X (ComplexShape.down ℕ) (k + 1) A k (by omega)))
  · by_cases hk1 : n = k + 1
    · subst n
      let S : ShortComplex 𝒜 :=
        (eilenbergMacLaneExtensionModelShortComplex A k).map
          (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) (k + 1))
      change S.Splitting
      have hg : IsIso S.g := by
        dsimp [S]
        simpa [eilenbergMacLaneExtensionModelShortComplex,
          eilenbergMacLaneExtensionProjectionChainMap,
          HomologicalComplex.mkHomToSingle_f] using
          (show IsIso
            ((doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).hom ≫
              (singleObjXSelf (ComplexShape.down ℕ) (k + 1) A).inv) from inferInstance)
      exact ShortComplex.Splitting.ofIsZeroOfIsIso S
        (by
          simpa [eilenbergMacLaneExtensionModelShortComplex] using
            (isZero_single_obj_X (ComplexShape.down ℕ) k A (k + 1) (Nat.succ_ne_self k)))
        hg
    · let S : ShortComplex 𝒜 :=
        (eilenbergMacLaneExtensionModelShortComplex A k).map
          (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) n)
      change S.Splitting
      have hg : IsIso S.g := by
        dsimp [S]
        have hX₂ :
            IsZero ((eilenbergMacLaneExtensionComplex A k).X n) := by
          exact eilenbergMacLaneExtensionComplex_isZero_X A k n hk hk1
        have hX₃ :
            IsZero (((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).X n) := by
          simpa [eilenbergMacLaneExtensionModelShortComplex] using
            (isZero_single_obj_X (ComplexShape.down ℕ) (k + 1) A n hk1)
        simpa [eilenbergMacLaneExtensionModelShortComplex,
          eilenbergMacLaneExtensionProjectionChainMap_f_eq_zero A k n hk1] using
          (show IsIso
            (0 : (eilenbergMacLaneExtensionComplex A k).X n ⟶
              ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).X n) from
            hX₂.isIso hX₃ 0)
      exact ShortComplex.Splitting.ofIsZeroOfIsIso S
        (by
          simpa [eilenbergMacLaneExtensionModelShortComplex] using
            (isZero_single_obj_X (ComplexShape.down ℕ) k A n hk))
        hg

-- Proof sketch: apply `HomologicalComplex.shortExact_of_degreewise_shortExact` to the chain-level
-- model, using the degreewise splittings and the owner lemma `ShortComplex.Splitting.shortExact`.
/-- The chain-level short complex modeling the extension is short exact. -/
private theorem eilenbergMacLaneExtensionModelShortComplex_shortExact
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionModelShortComplex A k).ShortExact := by
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n ↦
      (eilenbergMacLaneExtensionModelShortComplex_degreewiseSplitting A k n).shortExact)

-- Proof sketch: identify `eilenbergMacLaneExtension A k` with the Dold-Kan image of the two-term
-- complex `A --𝟙--> A` in degrees `k + 1` and `k`; transport the chain-level short exact model
-- along `Γ` and the endpoint identifications with `K(A, k)` and `K(A, k + 1)`.
/-- The extension short complex `K(A, k) ⟶ E ⟶ K(A, k + 1)` is short exact. -/
theorem eilenbergMacLaneExtensionShortComplex_shortExact (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionShortComplex A k).ShortExact := by
  letI : PreservesFiniteLimits (Γ : ChainComplex 𝒜 ℕ ⥤ SimplicialObject 𝒜) := by
    simpa [Abelian.DoldKan.equivalence_inverse] using
      (inferInstance :
        PreservesFiniteLimits
          ((Abelian.DoldKan.equivalence : SimplicialObject 𝒜 ≌ ChainComplex 𝒜 ℕ).inverse))
  letI : PreservesFiniteColimits (Γ : ChainComplex 𝒜 ℕ ⥤ SimplicialObject 𝒜) := by
    simpa [Abelian.DoldKan.equivalence_inverse] using
      (inferInstance :
        PreservesFiniteColimits
          ((Abelian.DoldKan.equivalence : SimplicialObject 𝒜 ≌ ChainComplex 𝒜 ℕ).inverse))
  exact ShortComplex.shortExact_of_iso
    (eilenbergMacLaneExtensionModelShortComplexGammaIso A k)
    (by
      simpa using
        (eilenbergMacLaneExtensionModelShortComplex_shortExact A k).map_of_exact Γ)

private theorem eilenbergMacLaneExtensionModelShortComplex_termwiseShortExact
    (A : 𝒜) (k : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    (((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
      ((evaluation _ _).obj Δ)).ShortExact := by
  letI : PreservesFiniteLimits (Γ : ChainComplex 𝒜 ℕ ⥤ SimplicialObject 𝒜) := by
    simpa [Abelian.DoldKan.equivalence_inverse] using
      (inferInstance :
        PreservesFiniteLimits
          ((Abelian.DoldKan.equivalence : SimplicialObject 𝒜 ≌ ChainComplex 𝒜 ℕ).inverse))
  letI : PreservesFiniteColimits (Γ : ChainComplex 𝒜 ℕ ⥤ SimplicialObject 𝒜) := by
    simpa [Abelian.DoldKan.equivalence_inverse] using
      (inferInstance :
        PreservesFiniteColimits
          ((Abelian.DoldKan.equivalence : SimplicialObject 𝒜 ≌ ChainComplex 𝒜 ℕ).inverse))
  simpa [ShortComplex.map_comp] using
    (eilenbergMacLaneExtensionModelShortComplex_shortExact A k).map_of_exact
      (Γ ⋙ (evaluation _ _).obj Δ)

private noncomputable def eilenbergMacLaneExtensionModelShortComplex_termwiseSection
    (A : 𝒜) (k : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    ((((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
      ((evaluation _ _).obj Δ))).X₃ ⟶
        ((((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
          ((evaluation _ _).obj Δ))).X₂ := by
  let S := (((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
    ((evaluation _ _).obj Δ))
  change S.X₃ ⟶ S.X₂
  exact
    (gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).desc Δ
      (fun B ↦
        if h : B.1.unop.len = k + 1 then
          ((((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).XIsoOfEq h).hom) ≫
            (singleObjXSelf (ComplexShape.down ℕ) (k + 1) A).hom ≫
            (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).inv ≫
            ((eilenbergMacLaneExtensionComplex A k).XIsoOfEq h).inv ≫
            ((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B
        else 0)

private lemma eilenbergMacLaneExtensionModelShortComplex_termwiseSection_s_g
    (A : 𝒜) (k : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ ≫
      ((((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
        ((evaluation _ _).obj Δ))).g =
      𝟙 _ := by
  let F : ∀ B : SimplicialObject.Splitting.IndexSet Δ,
      (((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).X B.1.unop.len) ⟶
        ((((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
          ((evaluation _ _).obj Δ))).X₂ :=
    fun B ↦
      if h : B.1.unop.len = k + 1 then
        ((((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).XIsoOfEq h).hom) ≫
          (singleObjXSelf (ComplexShape.down ℕ) (k + 1) A).hom ≫
          (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).inv ≫
          ((eilenbergMacLaneExtensionComplex A k).XIsoOfEq h).inv ≫
          ((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B
      else 0
  let S := (((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
    ((evaluation _ _).obj Δ))
  change
    eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ ≫ S.g = 𝟙 S.X₃
  apply (gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).hom_ext'
  intro B
  have hdesc :
      ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B ≫
        eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ =
      F B := by
    dsimp [eilenbergMacLaneExtensionModelShortComplex_termwiseSection, F]
    simpa using
      (gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).ι_desc Δ F B
  have hcomp :
      (((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B ≫
          eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ) ≫
        S.g =
      F B ≫ S.g := congrArg (fun t ↦ t ≫ S.g) hdesc
  have hFg :
      F B ≫ S.g =
        ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B := by
    by_cases hB : B.1.unop.len = k + 1
    · dsimp [F]
      rw [dif_pos hB]
      let p :
          (((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).X B.1.unop.len) ⟶
            (eilenbergMacLaneExtensionComplex A k).X B.1.unop.len :=
        (((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).XIsoOfEq hB).hom ≫
          (singleObjXSelf (ComplexShape.down ℕ) (k + 1) A).hom ≫
            (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).inv ≫
              ((eilenbergMacLaneExtensionComplex A k).XIsoOfEq hB).inv
      have hgamma :
          ((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B ≫ S.g =
            (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len ≫
              ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                B := by
        simpa [S, eilenbergMacLaneExtensionModelShortComplex] using
          (gammaCofanInj_comp_app
            (eilenbergMacLaneExtensionProjectionChainMap A k) Δ B)
      have hgamma' : p ≫
          (((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B ≫ S.g) =
            p ≫
              ((eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len ≫
                ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                  B) := by
        exact congrArg (fun t ↦ p ≫ t) hgamma
      have hnat :
          ((eilenbergMacLaneExtensionComplex A k).XIsoOfEq hB).inv ≫
              (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len =
            (eilenbergMacLaneExtensionProjectionChainMap A k).f (k + 1) ≫
              (((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).XIsoOfEq hB).inv := by
        simpa using
          (HomologicalComplex.XIsoOfEq_inv_naturality
            (eilenbergMacLaneExtensionProjectionChainMap A k) hB).symm
      have hgamma'' :
          p ≫ ((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B ≫ S.g =
            p ≫
              (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len ≫
                ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                  B := by
        simpa [Category.assoc] using hgamma'
      have hstep :
          p ≫
              (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len ≫
                ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                  B =
            ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B := by
        have hp :
            p ≫ (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len = 𝟙 _ := by
          dsimp [p]
          repeat rw [Category.assoc]
          rw [hnat]
          simp [eilenbergMacLaneExtensionProjectionChainMap, Category.assoc]
        calc
          p ≫
              (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len ≫
                ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                  B =
            (p ≫ (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len) ≫
              ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                B := by simp [Category.assoc]
          _ = 𝟙 (SimplicialObject.Splitting.summand
                (gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).N Δ B) ≫
              ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                B := by
                  rw [hp]
                  simp [SimplicialObject.Splitting.summand]
          _ = ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                B := by
                  simp
      simpa [p, Category.assoc] using hgamma''.trans hstep
    · dsimp [F]
      rw [dif_neg hB]
      rw [gammaSingleCofanInj_eq_zero A (k + 1) B hB]
      exact zero_comp
  have hfinal :
      (((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B ≫
          eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ) ≫
        S.g =
      ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B := by
    exact hcomp.trans hFg
  have hfinal' :
      (((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B ≫
          eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ) ≫
        S.g =
      ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B ≫
        𝟙 S.X₃ := by
    exact hfinal.trans
      ((comp_id
        (((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
          B)).symm)
  simpa [Category.assoc] using hfinal'

-- Proof sketch: evaluate the Dold-Kan model of the extension at a simplicial degree; the
-- resulting object is a direct sum of copies of `A`, and the distinguished two-term summands
-- provide the retraction and section.
/-- After evaluating at any simplicial degree, the extension short complex carries a canonical
splitting. -/
noncomputable def eilenbergMacLaneExtensionShortComplex_termwiseSplit
    (A : 𝒜) (k : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    ((eilenbergMacLaneExtensionShortComplex A k).map ((evaluation _ _).obj Δ)).Splitting := by
  let e :=
    (((evaluation _ _).obj Δ).mapShortComplex).mapIso
      (eilenbergMacLaneExtensionModelShortComplexGammaIso A k)
  let S := (((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
    ((evaluation _ _).obj Δ))
  have h : S.Splitting := by
    exact ShortComplex.Splitting.ofExactOfSection S
      (eilenbergMacLaneExtensionModelShortComplex_termwiseShortExact A k Δ).exact
      (eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ)
      (eilenbergMacLaneExtensionModelShortComplex_termwiseSection_s_g A k Δ)
      (eilenbergMacLaneExtensionModelShortComplex_termwiseShortExact A k Δ).mono_f
  exact ShortComplex.Splitting.ofIso h e

-- Proof sketch: use the constructed short complex, combine its short exactness theorem with the
-- degreewise splitting API, and package both source-facing conclusions into one textbook entry.
/-- Lemma 14.22.4: for an object `A` of an abelian category and `k ≥ 0`, the simplicial object
`eilenbergMacLaneExtension A k` fits into a short exact sequence
`0 ⟶ K(A, k) ⟶ E ⟶ K(A, k + 1) ⟶ 0`, and this sequence is term by term split exact. -/
theorem eilenbergMacLaneExtension_shortExact_and_termwiseSplit
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionShortComplex A k).ShortExact ∧
      ∀ Δ : SimplexCategoryᵒᵖ,
        Nonempty
          (((eilenbergMacLaneExtensionShortComplex A k).map ((evaluation _ _).obj Δ)).Splitting) := by
  constructor
  · exact eilenbergMacLaneExtensionShortComplex_shortExact A k
  · intro Δ
    exact ⟨eilenbergMacLaneExtensionShortComplex_termwiseSplit A k Δ⟩

end CategoryTheory

/-! ### Lemma_14_22_5 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A]

section

variable [HasFiniteColimits A]

/- Domain-style sampling for Lemma 14.22.5:
- primary domain: simplicial-object skeletons in a category with finite colimits, organized into the canonical
  sequential diagram whose colimit recovers the original simplicial object;
- sampled owner declarations:
  `sk`,
  `skAdj`,
  `Functor.ofSequence`,
  `evaluationJointlyReflectsColimits`,
  `Functor.IsEventuallyConstantFrom.isColimitOfIsIso`;
- best owner abstraction:
  `source-facing`: the sequence `n ↦ (sk n).obj V` together with its canonical cocone into `V`;
  `core/canonical`: the skeleton endofunctors `sk n`, the counits `(skAdj n).counit.app V`, and
    the sequence/cocone owners `Functor.ofSequence`, `NatTrans.ofSequence`, and
    `evaluationJointlyReflectsColimits`;
  `bridge/view`: the successor map from `(sk n).obj V` to `(sk (n + 1)).obj V`, obtained by
    transporting the unit of `skAdj (n + 1)` across truncation, together with the degreewise
    eventual-constancy bridge to `Functor.IsEventuallyConstantFrom.isColimitOfIsIso`.
- primitive data: the simplicial object `V` and the canonical counit maps from each skeleton to
  `V`;
- derived API: the sequential diagram of skeletons, its cocone into `V`, the monomorphism
  property of transition maps, and the colimit witness.

Source/core/bridge triage:
- `source-facing`: `skeletonSequence V` and `skeletonSequenceCocone V`;
- `core/canonical`: `sk`, `skAdj`, `Functor.ofSequence`, and `NatTrans.ofSequence`;
- `bridge/view`: the local successor-map construction below. -/

/-- The canonical map from the `n`-skeleton of a simplicial object to its `(n + 1)`-skeleton. -/
private noncomputable def skeletonSuccMap (V : SimplicialObject A) (n : ℕ) :
    (sk n).obj V ⟶ (sk (n + 1)).obj V :=
  ((skAdj n).homEquiv ((truncation n).obj V) ((sk (n + 1)).obj V)).symm
    (((truncationCompTrunc (Nat.le_succ n)).app V).inv ≫
      (Truncated.trunc A (n + 1) n).map
        ((skAdj (n + 1)).unit.app ((truncation (n + 1)).obj V)) ≫
      ((truncationCompTrunc (Nat.le_succ n)).app
        ((sk (n + 1)).obj V)).hom)

/-- The sequential diagram of the simplicial skeletons of `V`. -/
noncomputable def skeletonSequence (V : SimplicialObject A) : ℕ ⥤ SimplicialObject A :=
  Functor.ofSequence (skeletonSuccMap V)

-- Proof sketch: `skeletonSuccMap V n` is defined by adjunction from the truncation comparison
-- induced by the unit of `skAdj (n + 1)`. Unwinding that adjunction and the triangle identities
-- shows that composing with the counit to `V` recovers the counit from the `n`-skeleton.
/-- The maps in the skeleton sequence are compatible with the canonical inclusions into `V`. -/
private theorem skeletonSuccMap_comp_counit (V : SimplicialObject A) (n : ℕ) :
    skeletonSuccMap V n ≫ (skAdj (n + 1)).counit.app V = (skAdj n).counit.app V := sorry

/-- The canonical cocone from the sequence of skeletons of `V` to `V`. -/
noncomputable def skeletonSequenceCocone (V : SimplicialObject A) :
    Cocone (skeletonSequence V) where
  pt := V
  ι := NatTrans.ofSequence
    (fun n ↦ (skAdj n).counit.app V)
    (fun n ↦ by
      simpa [skeletonSequence, skeletonSuccMap_comp_counit] using
        skeletonSuccMap_comp_counit V n)

private theorem skeletonSequenceEvaluation_isEventuallyConstantFrom
    (V : SimplicialObject A) (m : ℕ) :
    Functor.IsEventuallyConstantFrom
      (skeletonSequence V ⋙ (evaluation _ A).obj (op (SimplexCategory.mk m))) m := by
  let ev : SimplicialObject A ⥤ A := (evaluation _ A).obj (op (SimplexCategory.mk m))
  intro j f
  let ε :
      ∀ n : ℕ,
        ((skeletonSequence V ⋙ ev).obj n ⟶ V.obj (op (SimplexCategory.mk m))) :=
    fun n ↦ ((skeletonSequenceCocone V).ι.app n).app (op (SimplexCategory.mk m))
  haveI : IsIso (ε m) := by
    simpa [ε, skeletonSequenceCocone] using
      truncatedSkeleton_counit_app_isIso_of_le m V (le_rfl : m ≤ m)
  haveI : IsIso (ε j) := by
    simpa [ε, skeletonSequenceCocone] using
      truncatedSkeleton_counit_app_isIso_of_le j V (leOfHom f)
  have hε :
      (skeletonSequence V ⋙ ev).map f ≫ ε j = ε m := by
    simpa [ε] using
      (ev.mapCocone (skeletonSequenceCocone V)).w f
  have hmap :
      (skeletonSequence V ⋙ ev).map f = ε m ≫ (asIso (ε j)).inv := by
    apply (cancel_mono (ε j)).1
    calc
      (skeletonSequence V ⋙ ev).map f ≫ ε j = ε m :=
        hε
      _ = (ε m ≫ (asIso (ε j)).inv) ≫ ε j := by simp [Category.assoc]
  rw [hmap]
  infer_instance

private noncomputable def skeletonSequenceEvaluation_isColimit
    (V : SimplicialObject A) (m : ℕ) :
    IsColimit
      (((evaluation _ A).obj (op (SimplexCategory.mk m))).mapCocone
        (skeletonSequenceCocone V)) := by
  let ev : SimplicialObject A ⥤ A := (evaluation _ A).obj (op (SimplexCategory.mk m))
  let h :
      Functor.IsEventuallyConstantFrom
        (skeletonSequence V ⋙ ev) m :=
    skeletonSequenceEvaluation_isEventuallyConstantFrom V m
  haveI :
      IsIso ((ev.mapCocone (skeletonSequenceCocone V)).ι.app m) := by
    simpa [skeletonSequenceCocone] using
      truncatedSkeleton_counit_app_isIso_of_le m V (le_rfl : m ≤ m)
  exact h.isColimitOfIsIso (ev.mapCocone (skeletonSequenceCocone V))

-- Proof sketch: evaluation at degree `m` preserves colimits in the functor category of simplicial
-- objects, and for every `m` the evaluated sequence is eventually constant because
-- `((sk n).obj V).obj (op ⦋m⦌) = V.obj (op ⦋m⦌)` once `n ≥ m`. Thus the canonical cocone
-- `skeletonSequenceCocone V` is degreewise colimiting, hence colimiting in `SimplicialObject A`.
/-- Lemma 14.22.5: for a simplicial object `V` in a category with finite colimits, the canonical sequential
diagram of skeletons
`(sk 0).obj V ⟶ (sk 1).obj V ⟶ (sk 2).obj V ⟶ ⋯`
has colimit cocone `skeletonSequenceCocone V`, so `V` is the colimit of its skeletons. The
companion theorem `skeletonSequence_map_mono` records under abelian hypotheses that all transition
maps are monomorphisms.
-/
noncomputable def skeletonSequence_isColimit (V : SimplicialObject A) :
    IsColimit (skeletonSequenceCocone V) :=
  evaluationJointlyReflectsColimits (skeletonSequenceCocone V) fun Δ ↦ by
    cases Δ with
    | op Δ =>
        cases Δ with
        | mk m =>
            simpa using skeletonSequenceEvaluation_isColimit V m

end

section

variable [Abelian A]

-- Proof sketch: the cocone identity for `skeletonSequenceCocone V` gives
-- `(skeletonSequence V).map (homOfLE h) ≫ (skAdj j).counit.app V = (skAdj i).counit.app V`.
-- Both counits are mono by Lemma 14.21.10, so the left factor is mono by cancellation.
/-- Every transition morphism in the skeleton sequence of `V` is monomorphic. -/
theorem skeletonSequence_map_mono (V : SimplicialObject A) {i j : ℕ} (h : i ≤ j) :
    Mono ((skeletonSequence V).map (homOfLE h)) := by
  haveI : Mono ((skAdj i).counit.app V) := truncatedSkeleton_counit_mono i V
  let fac :
      (skeletonSequence V).map (homOfLE h) ≫ (skAdj j).counit.app V = (skAdj i).counit.app V := by
    simpa [skeletonSequenceCocone] using (skeletonSequenceCocone V).w (homOfLE h)
  refine ⟨?_⟩
  intro Z f g hfg
  apply (cancel_mono ((skAdj i).counit.app V)).1
  calc
    f ≫ (skAdj i).counit.app V
        = (f ≫ (skeletonSequence V).map (homOfLE h)) ≫ (skAdj j).counit.app V := by
            rw [Category.assoc, fac]
    _ = (g ≫ (skeletonSequence V).map (homOfLE h)) ≫ (skAdj j).counit.app V := by
          rw [hfg]
    _ = g ≫ (skAdj i).counit.app V := by
          rw [Category.assoc, fac]

end

end CategoryTheory
