import Mathlib
import StacksProject_2024.Chap14.Definition_14_22_3
import StacksProject_2024.Chap14.Lemma_14_19_2
import StacksProject_2024.Chap14.Lemma_14_21_3

-- Declarations for this item will be appended below by the statement pipeline.

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
