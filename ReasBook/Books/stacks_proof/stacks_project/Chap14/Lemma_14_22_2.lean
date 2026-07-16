import Mathlib
import stacks_proof.stacks_project.Chap14.Definition_14_22_3
import stacks_proof.stacks_project.Chap14.Lemma_14_19_2
import stacks_proof.stacks_project.Chap14.Lemma_14_21_3

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

/-- Helper for Lemma 14.22.2: the `α`-indexed summand map into the left Kan extension is the
canonical top-degree unit leg followed by the simplicial operator `α`. -/
theorem singleDegreeTruncatedSkι_eq_unit_map
    (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F]
    (α : topEpiIndex k n) :
    singleDegreeTruncatedSkι B k n α =
      (singleDegreeTruncatedTopIso B k).hom ≫
        ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionUnit
            (single_degree_truncated B k)).app (op (topTruncatedSimplex k)) ≫
          ((Truncated.sk k).obj (single_degree_truncated B k)).map α.1.op := by
  let h :=
    ((SimplexCategory.Truncated.inclusion k).op.ι_leftKanExtensionObjIsoColimit_inv
      (single_degree_truncated B k) (op ⦋n⦌) (topEpiCostructuredArrow α))
  -- Postcompose the canonical leg formula with the fixed top-degree inclusion.
  simpa [singleDegreeTruncatedSkι, topEpiCostructuredArrow, topTruncatedSimplex, Category.assoc] using
    congrArg (fun t ↦ (singleDegreeTruncatedTopIso B k).hom ≫ t) h

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

/-- Helper for Lemma 14.22.2: the `β`-indexed projection from the right Kan extension is the
canonical top-degree counit leg preceded by the simplicial operator `β`. -/
theorem singleDegreeTruncatedCoskπ_eq_map_counit
    (B : A) (k n : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    (β : topMonoIndex k n) :
    singleDegreeTruncatedCoskπ B k n β =
      ((Truncated.cosk k).obj (single_degree_truncated B k)).map β.1.op ≫
        ((SimplexCategory.Truncated.inclusion k).op.ranCounit.app
            (single_degree_truncated B k)).app (op (topTruncatedSimplex k)) ≫
          (singleDegreeTruncatedTopIso B k).inv := by
  let h :=
    ((SimplexCategory.Truncated.inclusion k).op.ranObjObjIsoLimit_hom_π
      (single_degree_truncated B k) (op ⦋n⦌) (topMonoStructuredArrow β))
  -- Precompose the canonical projection formula with the fixed top-degree identification.
  simpa [singleDegreeTruncatedCoskπ, topMonoStructuredArrow, topTruncatedSimplex, Category.assoc] using
    congrArg (fun t ↦ t ≫ (singleDegreeTruncatedTopIso B k).inv) h

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

/-- Helper for Lemma 14.22.2: an epimorphic endomorphism of the top truncated simplex is the
identity. -/
private theorem topTruncatedSimplex_hom_eq_id_of_epi
    {k : ℕ} (θ : topTruncatedSimplex k ⟶ topTruncatedSimplex k) [Epi θ.hom] :
    θ = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  exact SimplexCategory.eq_id_of_epi θ.hom

/-- Helper for Lemma 14.22.2: a monomorphic endomorphism of the top truncated simplex is the
identity. -/
private theorem topTruncatedSimplex_hom_eq_id_of_mono
    {k : ℕ} (θ : topTruncatedSimplex k ⟶ topTruncatedSimplex k) [Mono θ.hom] :
    θ = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  exact SimplexCategory.eq_id_of_mono θ.hom

/-- Helper for Lemma 14.22.2: the face-vanishing condition at the top degree propagates along any
non-epimorphic map into the top simplex. -/
private theorem singleDegreeTruncatedFaceCondition.comp_eq_zero_of_not_epi
    {k : ℕ} {V : SimplicialObject.Truncated A k} {B : A}
    {f : B ⟶ V _⦋k, le_rfl⦌ₖ} (hf : singleDegreeTruncatedFaceCondition V f)
    {X : SimplexCategory.Truncated k} (θ : X ⟶ topTruncatedSimplex k) (hθ : ¬ Epi θ.hom) :
    f ≫ V.map θ.op = 0 := by
  cases k with
  | zero =>
      exfalso
      apply hθ
      rw [SimplexCategory.epi_iff_surjective]
      intro x
      refine ⟨0, ?_⟩
      fin_cases x
      apply Fin.ext
      simp
  | succ n =>
      have hsurj : ¬ Function.Surjective θ.hom.toOrderHom := by
        rw [← SimplexCategory.epi_iff_surjective]
        exact hθ
      obtain ⟨i, θ', hθ'⟩ := SimplexCategory.eq_comp_δ_of_not_surjective θ.hom hsurj
      have hθtr :
          θ =
            SimplexCategory.Truncated.Hom.tr θ' X.property (by simp) ≫
              SimplexCategory.Truncated.δ (n + 1) i (by simp) (by simp) := by
        apply ObjectProperty.hom_ext
        simpa using hθ'
      -- Factor the non-epimorphic map through one top face and then apply the given vanishing
      -- condition at that face.
      calc
        f ≫ V.map θ.op =
        f ≫
            V.map
              (SimplexCategory.Truncated.δ (n + 1) i (by simp) (by simp)).op ≫
            V.map (SimplexCategory.Truncated.Hom.tr θ' X.property (by simp)).op := by
            rw [hθtr, op_comp, Functor.map_comp]
        _ = (f ≫ V.map (SimplexCategory.Truncated.δ (n + 1) i (by simp) (by simp)).op) ≫
              V.map (SimplexCategory.Truncated.Hom.tr θ' X.property (by simp)).op := by
          simp [Category.assoc]
        _ = 0 := by
          simp [hf i]

/-- Helper for Lemma 14.22.2: the degeneracy-vanishing condition at the top degree propagates
along any non-monomorphic map out of the top simplex. -/
private theorem singleDegreeTruncatedDegeneracyCondition.comp_eq_zero_of_not_mono
    {k : ℕ} {V : SimplicialObject.Truncated A k} {B : A}
    {f : V _⦋k, le_rfl⦌ₖ ⟶ B} (hf : singleDegreeTruncatedDegeneracyCondition V f)
    {X : SimplexCategory.Truncated k} (θ : topTruncatedSimplex k ⟶ X) (hθ : ¬ Mono θ.hom) :
    V.map θ.op ≫ f = 0 := by
  cases k with
  | zero =>
      exfalso
      apply hθ
      rw [SimplexCategory.mono_iff_injective]
      intro x y _
      fin_cases x
      fin_cases y
      rfl
  | succ n =>
      have hinj : ¬ Function.Injective θ.hom.toOrderHom := by
        rw [← SimplexCategory.mono_iff_injective]
        exact hθ
      obtain ⟨i, θ', hθ'⟩ := SimplexCategory.eq_σ_comp_of_not_injective θ.hom hinj
      have hθtr :
          θ =
            SimplexCategory.Truncated.σ (n + 1) i (by simp) (by simp) ≫
              SimplexCategory.Truncated.Hom.tr θ' (by simp) X.property := by
        apply ObjectProperty.hom_ext
        simpa using hθ'
      -- Dually, factor the non-monomorphic map through one top degeneracy and then use the
      -- prescribed vanishing along that degeneracy.
      calc
        V.map θ.op ≫ f =
          V.map (SimplexCategory.Truncated.Hom.tr θ' (by simp) X.property).op ≫
            V.map
              (SimplexCategory.Truncated.σ (n + 1) i (by simp) (by simp)).op ≫
            f := by
            rw [hθtr, op_comp, Functor.map_comp]
            simp [Category.assoc]
        _ = V.map (SimplexCategory.Truncated.Hom.tr θ' (by simp) X.property).op ≫
              (V.map
                  (SimplexCategory.Truncated.σ (n + 1) i (by simp) (by simp)).op ≫
                f) := by
          simp [Category.assoc]
        _ = 0 := by
          simp [hf i]

/-- Helper for Lemma 14.22.2: below the top degree, the concentrated truncated object is the zero
object. -/
private theorem singleDegreeTruncated_obj_eq_zero_of_lt
    (B : A) {k n : ℕ} (h : n < k) :
    (single_degree_truncated B k).obj (op ⦋n, Nat.le_of_lt h⦌ₖ) = ⊥_ A := by
  change (if n = k then B else ⊥_ A) = ⊥_ A
  simp [h.ne]

/-- Helper for Lemma 14.22.2: in a category with a zero object, the chosen initial object is
itself a zero object. -/
private theorem isZero_bot_of_hasZeroObject : IsZero (⊥_ A) := by
  rcases HasZeroObject.zero (C := A) with ⟨Z, hZ⟩
  -- Compare the chosen initial object with any zero object supplied by `HasZeroObject`.
  exact IsZero.of_iso hZ (initialIsInitial.uniqueUpToIso hZ.isInitial)

/-- Helper for Lemma 14.22.2: the top-degree map of the concentrated object followed by any top
face lands in a lower degree, hence is zero. -/
private theorem singleDegreeTruncated_top_comp_map_δ_eq_zero
    (B : A) (n : ℕ) (i : Fin (n + 2)) :
    (singleDegreeTruncatedTopIso B (n + 1)).hom ≫
      (single_degree_truncated B (n + 1)).map
        (SimplexCategory.Truncated.δ (n + 1) i (by simp) (by simp)).op =
      0 := by
  let X : SimplexCategory.Truncated (n + 1) := ⟨⦋n⦌, by simp⟩
  let e :
      (single_degree_truncated B (n + 1)).obj (op X) ≅ ⊥_ A :=
    CategoryTheory.eqToIso
      (singleDegreeTruncated_obj_eq_zero_of_lt B (k := n + 1) (n := n) (by simp))
  let hzero :
      IsZero ((single_degree_truncated B (n + 1)).obj (op X)) :=
    IsZero.of_iso isZero_bot_of_hasZeroObject e
  -- Route correction: the top face lands in a lower degree, and the concentrated object is already
  -- zero there, so uniqueness of maps into the zero object closes the composite.
  have h :
      (show B ⟶ (single_degree_truncated B (n + 1)).obj (op X) from
        (singleDegreeTruncatedTopIso B (n + 1)).hom ≫
          (single_degree_truncated B (n + 1)).map
            (SimplexCategory.Truncated.δ (n + 1) i (by simp) (by simp)).op) =
        0 := by
    exact hzero.eq_of_tgt _ _
  simpa [X] using h

/-- Helper for Lemma 14.22.2: any top degeneracy starts in a lower degree of the concentrated
object, so the resulting map into the top copy of `B` is zero. -/
private theorem singleDegreeTruncated_map_σ_comp_top_eq_zero
    (B : A) (n : ℕ) (i : Fin (n + 1)) :
    (single_degree_truncated B (n + 1)).map
        (SimplexCategory.Truncated.σ (n + 1) i (by simp) (by simp)).op ≫
      (singleDegreeTruncatedTopIso B (n + 1)).inv =
      0 := by
  let X : SimplexCategory.Truncated (n + 1) := ⟨⦋n⦌, by simp⟩
  let e :
      (single_degree_truncated B (n + 1)).obj (op X) ≅ ⊥_ A :=
    CategoryTheory.eqToIso
      (singleDegreeTruncated_obj_eq_zero_of_lt B (k := n + 1) (n := n) (by simp))
  let hzero :
      IsZero ((single_degree_truncated B (n + 1)).obj (op X)) :=
    IsZero.of_iso isZero_bot_of_hasZeroObject e
  -- Dually, every top degeneracy starts in a lower degree of the concentrated object, so the
  -- source is already zero and there is only one outgoing morphism.
  have h :
      (show (single_degree_truncated B (n + 1)).obj (op X) ⟶ B from
        (single_degree_truncated B (n + 1)).map
            (SimplexCategory.Truncated.σ (n + 1) i (by simp) (by simp)).op ≫
          (singleDegreeTruncatedTopIso B (n + 1)).inv) =
        0 := by
    exact hzero.eq_of_src _ _
  simpa [X] using h

/-- Helper for Lemma 14.22.2: a truncated simplex of length `k` is the top simplex. -/
private theorem truncatedSimplex_eq_top
    {k : ℕ} (X : SimplexCategory.Truncated k) (hX : X.1.len = k) :
    X = topTruncatedSimplex k := by
  cases X with
  | mk obj property =>
      have hobj : obj = SimplexCategory.mk k := by
        exact SimplexCategory.ext hX
      cases hobj
      simp [topTruncatedSimplex]

/-- Helper for Lemma 14.22.2: a non-top truncated simplex has degree strictly less than `k`. -/
private theorem truncatedSimplex_len_lt_of_ne_top
    {k : ℕ} (X : SimplexCategory.Truncated k) (hX : X ≠ topTruncatedSimplex k) :
    X.1.len < k := by
  by_contra hlt
  have hle : k ≤ X.1.len := by
    exact Nat.not_lt.mp hlt
  have hlen : X.1.len = k := Nat.le_antisymm X.property hle
  exact hX (truncatedSimplex_eq_top X hlen)

/-- Helper for Lemma 14.22.2: away from the top simplex, the concentrated object is zero. -/
private theorem singleDegreeTruncated_obj_isZero_of_ne_top
    (B : A) {k : ℕ} (X : SimplexCategory.Truncated k) (hX : X ≠ topTruncatedSimplex k) :
    IsZero ((single_degree_truncated B k).obj (op X)) := by
  let e :
      (single_degree_truncated B k).obj (op X) ≅ ⊥_ A :=
    CategoryTheory.eqToIso
      (singleDegreeTruncated_obj_eq_zero_of_lt B
        (k := k) (n := X.1.len) (truncatedSimplex_len_lt_of_ne_top X hX))
  exact IsZero.of_iso isZero_bot_of_hasZeroObject e

/-- Helper for Lemma 14.22.2: a map from a non-top simplex to the top simplex is not epic. -/
private theorem not_epi_to_top_of_ne_top
    {k : ℕ} (X : SimplexCategory.Truncated k) (hX : X ≠ topTruncatedSimplex k)
    (θ : X ⟶ topTruncatedSimplex k) :
    ¬ Epi θ.hom := by
  intro hθ
  have hlen : X.1.len = k := by
    exact Nat.le_antisymm X.property (SimplexCategory.len_le_of_epi θ.hom)
  exact hX (truncatedSimplex_eq_top X hlen)

/-- Helper for Lemma 14.22.2: a map from the top simplex to a non-top simplex is not monic. -/
private theorem not_mono_from_top_of_ne_top
    {k : ℕ} (X : SimplexCategory.Truncated k) (hX : X ≠ topTruncatedSimplex k)
    (θ : topTruncatedSimplex k ⟶ X) :
    ¬ Mono θ.hom := by
  intro hθ
  have hlen : X.1.len = k := by
    exact Nat.le_antisymm X.property (SimplexCategory.len_le_of_mono θ.hom)
  exact hX (truncatedSimplex_eq_top X hlen)

/-- Helper for Lemma 14.22.2: the distinguished top-degree map of the concentrated object satisfies
the face-vanishing condition. -/
private theorem singleDegreeTruncated_top_faceCondition
    (B : A) (k : ℕ) :
    singleDegreeTruncatedFaceCondition (single_degree_truncated B k)
      (singleDegreeTruncatedTopIso B k).hom := by
  cases k with
  | zero =>
      trivial
  | succ n =>
      intro i
      simpa using singleDegreeTruncated_top_comp_map_δ_eq_zero B n i

/-- Helper for Lemma 14.22.2: the distinguished top-degree map of the concentrated object satisfies
the degeneracy-vanishing condition. -/
private theorem singleDegreeTruncated_top_degeneracyCondition
    (B : A) (k : ℕ) :
    singleDegreeTruncatedDegeneracyCondition (single_degree_truncated B k)
      (singleDegreeTruncatedTopIso B k).inv := by
  cases k with
  | zero =>
      trivial
  | succ n =>
      intro i
      simpa using singleDegreeTruncated_map_σ_comp_top_eq_zero B n i

/-- Helper for Lemma 14.22.2: the concentrated-object map on a top endomorphism is the identity
exactly for the identity endomorphism, and otherwise it is zero. -/
private theorem single_degree_truncated_top_endomorphism_map_eq_ite
    (B : A) (k : ℕ) (θ : topTruncatedSimplex k ⟶ topTruncatedSimplex k) :
    (singleDegreeTruncatedTopIso B k).hom ≫
        (single_degree_truncated B k).map θ.op ≫
        (singleDegreeTruncatedTopIso B k).inv =
      if θ = 𝟙 _ then 𝟙 B else 0 := by
  by_cases hθ : θ = 𝟙 _
  · subst hθ
    simp [Category.assoc]
  · have hnotepi : ¬ Epi θ.hom := by
      intro hEpi
      exact hθ (topTruncatedSimplex_hom_eq_id_of_epi θ)
    have hzero :
        (singleDegreeTruncatedTopIso B k).hom ≫
            (single_degree_truncated B k).map θ.op =
          0 :=
      singleDegreeTruncatedFaceCondition.comp_eq_zero_of_not_epi
        (V := single_degree_truncated B k)
        (f := (singleDegreeTruncatedTopIso B k).hom)
        (singleDegreeTruncated_top_faceCondition B k) θ hnotepi
    calc
      (singleDegreeTruncatedTopIso B k).hom ≫
          (single_degree_truncated B k).map θ.op ≫
          (singleDegreeTruncatedTopIso B k).inv =
        ((singleDegreeTruncatedTopIso B k).hom ≫
            (single_degree_truncated B k).map θ.op) ≫
          (singleDegreeTruncatedTopIso B k).inv := by
          simp [Category.assoc]
      _ = 0 := by
          rw [hzero, zero_comp]
      _ = if θ = 𝟙 _ then 𝟙 B else 0 := by
          simp [hθ]

/-- Helper for Lemma 14.22.2: the concentrated-object top map followed by any non-epimorphic map
into the top simplex is zero. -/
private theorem single_degree_truncated_top_comp_map_eq_zero_of_not_epi
    (B : A) {k : ℕ} {X : SimplexCategory.Truncated k}
    (θ : X ⟶ topTruncatedSimplex k) (hθ : ¬ Epi θ.hom) :
    (singleDegreeTruncatedTopIso B k).hom ≫
        (single_degree_truncated B k).map θ.op =
      0 :=
  singleDegreeTruncatedFaceCondition.comp_eq_zero_of_not_epi
    (V := single_degree_truncated B k)
    (f := (singleDegreeTruncatedTopIso B k).hom)
    (singleDegreeTruncated_top_faceCondition B k) θ hθ

/-- Helper for Lemma 14.22.2: any non-monomorphic map out of the top simplex annihilates the
distinguished top-degree projection of the concentrated object. -/
private theorem single_degree_truncated_map_comp_top_eq_zero_of_not_mono
    (B : A) {k : ℕ} {X : SimplexCategory.Truncated k}
    (θ : topTruncatedSimplex k ⟶ X) (hθ : ¬ Mono θ.hom) :
    (single_degree_truncated B k).map θ.op ≫
        (singleDegreeTruncatedTopIso B k).inv =
      0 :=
  singleDegreeTruncatedDegeneracyCondition.comp_eq_zero_of_not_mono
    (V := single_degree_truncated B k)
    (f := (singleDegreeTruncatedTopIso B k).inv)
    (singleDegreeTruncated_top_degeneracyCondition B k) θ hθ

/-- Helper for Lemma 14.22.2: a top-degree truncated simplex in the opposite category is the
distinguished opposite top simplex. -/
private theorem op_truncatedSimplex_eq_top
    {k : ℕ} (X : (SimplexCategory.Truncated k)ᵒᵖ) (hX : X.unop.1.len = k) :
    X = op (topTruncatedSimplex k) := by
  apply unop_injective
  simpa using truncatedSimplex_eq_top X.unop hX

/-- Helper for Lemma 14.22.2: when the source simplex is in top degree, the inverse component for
maps out of the concentrated object is the chosen top map transported along the degree equality. -/
private def singleDegreeTruncatedHomEquivInvAppTop
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : B ⟶ V _⦋k, le_rfl⦌ₖ // singleDegreeTruncatedFaceCondition V f })
    (X : (SimplexCategory.Truncated k)ᵒᵖ) (hX : X.unop.1.len = k) :
    (single_degree_truncated B k).obj X ⟶ V.obj X :=
  eqToHom (congrArg ((single_degree_truncated B k).obj) (op_truncatedSimplex_eq_top X hX)) ≫
    (singleDegreeTruncatedTopIso B k).inv ≫ g.1 ≫
      eqToHom (congrArg V.obj (op_truncatedSimplex_eq_top X hX).symm)

/-- Helper for Lemma 14.22.2: the inverse map in the outgoing Hom equivalence is supported only in
top degree. -/
private def singleDegreeTruncatedHomEquivInvApp
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : B ⟶ V _⦋k, le_rfl⦌ₖ // singleDegreeTruncatedFaceCondition V f })
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    (single_degree_truncated B k).obj X ⟶ V.obj X :=
  if hX : X.unop.1.len = k then
    singleDegreeTruncatedHomEquivInvAppTop B k V g X hX
  else
    0

/-- Helper for Lemma 14.22.2: at the distinguished top simplex, the outgoing inverse component is
exactly the chosen top map. -/
private theorem singleDegreeTruncatedHomEquivInvApp_top
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : B ⟶ V _⦋k, le_rfl⦌ₖ // singleDegreeTruncatedFaceCondition V f }) :
    singleDegreeTruncatedHomEquivInvApp B k V g (op (topTruncatedSimplex k)) =
      (singleDegreeTruncatedTopIso B k).inv ≫ g.1 := by
  -- At the top simplex all transports are identities, so the component collapses to the chosen
  -- degree-`k` map.
  simp [singleDegreeTruncatedHomEquivInvApp, singleDegreeTruncatedHomEquivInvAppTop,
    topTruncatedSimplex, Category.assoc]

/-- Helper for Lemma 14.22.2: the outgoing inverse component is given by the transported top map in
top degree and vanishes away from top degree. -/
private theorem singleDegreeTruncatedHomEquivInvApp_cases
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : B ⟶ V _⦋k, le_rfl⦌ₖ // singleDegreeTruncatedFaceCondition V f })
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    (∀ hX : X.unop.1.len = k,
        singleDegreeTruncatedHomEquivInvApp B k V g X =
          singleDegreeTruncatedHomEquivInvAppTop B k V g X hX) ∧
      (∀ hX : X.unop.1.len ≠ k,
        singleDegreeTruncatedHomEquivInvApp B k V g X = 0) := by
  constructor
  · intro hX
    -- In top degree the definition takes the transported top branch by construction.
    simp [singleDegreeTruncatedHomEquivInvApp, hX]
  · intro hX
    -- Away from top degree the component is definitionally zero.
    simp [singleDegreeTruncatedHomEquivInvApp, hX]

/-- Helper for Lemma 14.22.2: the top-supported components above are natural. -/
private theorem singleDegreeTruncatedHomEquivInvNaturality
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : B ⟶ V _⦋k, le_rfl⦌ₖ // singleDegreeTruncatedFaceCondition V f }) :
    ∀ {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (θ : X ⟶ Y),
      (single_degree_truncated B k).map θ ≫
          singleDegreeTruncatedHomEquivInvApp B k V g Y =
        singleDegreeTruncatedHomEquivInvApp B k V g X ≫ V.map θ :=
  by
    intro X Y θ
    by_cases hX : X.unop.1.len = k
    · by_cases hY : Y.unop.1.len = k
      · have hXtop : X = op (topTruncatedSimplex k) := op_truncatedSimplex_eq_top X hX
        have hYtop : Y = op (topTruncatedSimplex k) := op_truncatedSimplex_eq_top Y hY
        subst X
        subst Y
        -- Route correction: once both objects are top degree, only the identity endomorphism
        -- survives on the concentrated object; the non-identity case is killed by the top-face
        -- vanishing condition.
        by_cases hθ : θ.unop = 𝟙 (topTruncatedSimplex k)
        · have hθop : θ = 𝟙 (op (topTruncatedSimplex k)) := by
            apply Quiver.Hom.unop_inj
            simpa using hθ
          subst θ
          simp [singleDegreeTruncatedHomEquivInvApp_top]
        · have hnotepi : ¬ Epi θ.unop.hom := by
            intro hEpi
            letI := hEpi
            exact hθ (topTruncatedSimplex_hom_eq_id_of_epi θ.unop)
          have hmapzero' :
              (singleDegreeTruncatedTopIso B k).hom ≫
                  (single_degree_truncated B k).map θ =
                0 := by
            simpa using
              single_degree_truncated_top_comp_map_eq_zero_of_not_epi B θ.unop hnotepi
          have hmapzero :
              (single_degree_truncated B k).map θ = 0 := by
            refine (cancel_epi (singleDegreeTruncatedTopIso B k).hom).1 ?_
            simpa using hmapzero'
          have hrightzero :
              g.1 ≫ V.map θ = 0 := by
            simpa using
              singleDegreeTruncatedFaceCondition.comp_eq_zero_of_not_epi
                (V := V) (f := g.1) g.2 θ.unop hnotepi
          calc
            (single_degree_truncated B k).map θ ≫
                singleDegreeTruncatedHomEquivInvApp B k V g (op (topTruncatedSimplex k)) =
              0 := by
                rw [singleDegreeTruncatedHomEquivInvApp_top, hmapzero]
                simp [Category.assoc]
            _ =
              singleDegreeTruncatedHomEquivInvApp B k V g (op (topTruncatedSimplex k)) ≫
                V.map θ := by
                  symm
                  rw [singleDegreeTruncatedHomEquivInvApp_top]
                  simp [Category.assoc, hrightzero]
      · have hYzero :=
          (singleDegreeTruncatedHomEquivInvApp_cases B k V g Y).2 hY
        have hYneTop : Y.unop ≠ topTruncatedSimplex k := by
          intro hEq
          exact hY (by simpa [hEq])
        have hXtop : X = op (topTruncatedSimplex k) := op_truncatedSimplex_eq_top X hX
        subst X
        have hnotepi : ¬ Epi θ.unop.hom :=
          not_epi_to_top_of_ne_top Y.unop hYneTop θ.unop
        have hrightzero :
            g.1 ≫ V.map θ = 0 := by
          simpa using
            singleDegreeTruncatedFaceCondition.comp_eq_zero_of_not_epi
              (V := V) (f := g.1) g.2 θ.unop hnotepi
        -- With top source and lower target, the chosen top map vanishes after the non-epimorphic
        -- simplicial operator, while the target component is already zero.
        have hrightzero' :
            (singleDegreeTruncatedTopIso B k).inv ≫ (g.1 ≫ V.map θ) = 0 := by
          simpa [hrightzero] using
            congrArg (fun t ↦ (singleDegreeTruncatedTopIso B k).inv ≫ t) hrightzero
        calc
          (single_degree_truncated B k).map θ ≫
              singleDegreeTruncatedHomEquivInvApp B k V g Y =
            (single_degree_truncated B k).map θ ≫ 0 := by
              rw [hYzero]
          _ = 0 := by simp
          _ =
            singleDegreeTruncatedHomEquivInvApp B k V g (op (topTruncatedSimplex k)) ≫
              V.map θ := by
                symm
                rw [singleDegreeTruncatedHomEquivInvApp_top]
                simpa [Category.assoc] using hrightzero'
    · by_cases hY : Y.unop.1.len = k
      · have hXzero :=
          (singleDegreeTruncatedHomEquivInvApp_cases B k V g X).2 hX
        have hXneTop : X.unop ≠ topTruncatedSimplex k := by
          intro hEq
          exact hX (by simpa [hEq])
        have hYtop : Y = op (topTruncatedSimplex k) := op_truncatedSimplex_eq_top Y hY
        subst Y
        have hnotmono : ¬ Mono θ.unop.hom :=
          not_mono_from_top_of_ne_top X.unop hXneTop θ.unop
        have hleftzero :
            (single_degree_truncated B k).map θ ≫
                (singleDegreeTruncatedTopIso B k).inv =
              0 := by
          simpa using
            single_degree_truncated_map_comp_top_eq_zero_of_not_mono B θ.unop hnotmono
        -- With lower source and top target, the concentrated map into the top copy of `B` already
        -- vanishes, while the source inverse component is definitionally zero.
        calc
          (single_degree_truncated B k).map θ ≫
              singleDegreeTruncatedHomEquivInvApp B k V g (op (topTruncatedSimplex k)) =
            ((single_degree_truncated B k).map θ ≫
                (singleDegreeTruncatedTopIso B k).inv) ≫ g.1 := by
              rw [singleDegreeTruncatedHomEquivInvApp_top]
              simp [Category.assoc]
          _ = 0 := by
              rw [hleftzero, zero_comp]
          _ = singleDegreeTruncatedHomEquivInvApp B k V g X ≫ V.map θ := by
              rw [hXzero]
              simp
      · have hXzero :=
          (singleDegreeTruncatedHomEquivInvApp_cases B k V g X).2 hX
        have hYzero :=
          (singleDegreeTruncatedHomEquivInvApp_cases B k V g Y).2 hY
        -- Away from top degree both inverse components are definitionally zero.
        rw [hXzero, hYzero]
        simp

/-- Helper for Lemma 14.22.2: when the target simplex is in top degree, the inverse component for
maps into the concentrated object is the chosen top map transported along the degree equality. -/
private def homSingleDegreeTruncatedEquivInvAppTop
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : V _⦋k, le_rfl⦌ₖ ⟶ B // singleDegreeTruncatedDegeneracyCondition V f })
    (X : (SimplexCategory.Truncated k)ᵒᵖ) (hX : X.unop.1.len = k) :
    V.obj X ⟶ (single_degree_truncated B k).obj X :=
  eqToHom (congrArg V.obj (op_truncatedSimplex_eq_top X hX)) ≫
    g.1 ≫ (singleDegreeTruncatedTopIso B k).hom ≫
      eqToHom (congrArg ((single_degree_truncated B k).obj) (op_truncatedSimplex_eq_top X hX).symm)

/-- Helper for Lemma 14.22.2: the inverse map in the incoming Hom equivalence is supported only in
top degree. -/
private def homSingleDegreeTruncatedEquivInvApp
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : V _⦋k, le_rfl⦌ₖ ⟶ B // singleDegreeTruncatedDegeneracyCondition V f })
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    V.obj X ⟶ (single_degree_truncated B k).obj X :=
  if hX : X.unop.1.len = k then
    homSingleDegreeTruncatedEquivInvAppTop B k V g X hX
  else
    0

/-- Helper for Lemma 14.22.2: at the distinguished top simplex, the incoming inverse component is
exactly the chosen top map. -/
private theorem homSingleDegreeTruncatedEquivInvApp_top
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : V _⦋k, le_rfl⦌ₖ ⟶ B // singleDegreeTruncatedDegeneracyCondition V f }) :
    homSingleDegreeTruncatedEquivInvApp B k V g (op (topTruncatedSimplex k)) =
      g.1 ≫ (singleDegreeTruncatedTopIso B k).hom := by
  -- At the top simplex the incoming component is just the chosen degree-`k` morphism.
  simp [homSingleDegreeTruncatedEquivInvApp, homSingleDegreeTruncatedEquivInvAppTop,
    topTruncatedSimplex, Category.assoc]

/-- Helper for Lemma 14.22.2: the incoming inverse component is given by the transported top map in
top degree and vanishes away from top degree. -/
private theorem homSingleDegreeTruncatedEquivInvApp_cases
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : V _⦋k, le_rfl⦌ₖ ⟶ B // singleDegreeTruncatedDegeneracyCondition V f })
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    (∀ hX : X.unop.1.len = k,
        homSingleDegreeTruncatedEquivInvApp B k V g X =
          homSingleDegreeTruncatedEquivInvAppTop B k V g X hX) ∧
      (∀ hX : X.unop.1.len ≠ k,
        homSingleDegreeTruncatedEquivInvApp B k V g X = 0) := by
  constructor
  · intro hX
    -- In top degree the definition selects the transported top branch.
    simp [homSingleDegreeTruncatedEquivInvApp, hX]
  · intro hX
    -- Away from top degree the component is definitionally zero.
    simp [homSingleDegreeTruncatedEquivInvApp, hX]

/-- Helper for Lemma 14.22.2: the dual top-supported components above are natural. -/
private theorem homSingleDegreeTruncatedEquivInvNaturality
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : V _⦋k, le_rfl⦌ₖ ⟶ B // singleDegreeTruncatedDegeneracyCondition V f }) :
    ∀ {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (θ : X ⟶ Y),
      V.map θ ≫ homSingleDegreeTruncatedEquivInvApp B k V g Y =
        homSingleDegreeTruncatedEquivInvApp B k V g X ≫
          (single_degree_truncated B k).map θ :=
  by
    intro X Y θ
    by_cases hX : X.unop.1.len = k
    · by_cases hY : Y.unop.1.len = k
      · have hXtop : X = op (topTruncatedSimplex k) := op_truncatedSimplex_eq_top X hX
        have hYtop : Y = op (topTruncatedSimplex k) := op_truncatedSimplex_eq_top Y hY
        subst X
        subst Y
        -- Route correction: in the top-top branch only the identity endomorphism survives; the
        -- non-identity case is killed by the top-degeneracy and top-face vanishing lemmas.
        by_cases hθ : θ.unop = 𝟙 (topTruncatedSimplex k)
        · have hθop : θ = 𝟙 (op (topTruncatedSimplex k)) := by
            apply Quiver.Hom.unop_inj
            simpa using hθ
          subst θ
          simp [homSingleDegreeTruncatedEquivInvApp_top]
        · have hnotmono : ¬ Mono θ.unop.hom := by
            intro hMono
            letI := hMono
            exact hθ (topTruncatedSimplex_hom_eq_id_of_mono θ.unop)
          have hnotepi : ¬ Epi θ.unop.hom := by
            intro hEpi
            letI := hEpi
            exact hθ (topTruncatedSimplex_hom_eq_id_of_epi θ.unop)
          have hleftzero :
              V.map θ ≫ g.1 = 0 := by
            simpa using
              singleDegreeTruncatedDegeneracyCondition.comp_eq_zero_of_not_mono
                (V := V) (f := g.1) g.2 θ.unop hnotmono
          have hrightzero :
              (singleDegreeTruncatedTopIso B k).hom ≫
                  (single_degree_truncated B k).map θ =
                0 := by
            simpa using
              single_degree_truncated_top_comp_map_eq_zero_of_not_epi B θ.unop hnotepi
          calc
            V.map θ ≫
                homSingleDegreeTruncatedEquivInvApp B k V g (op (topTruncatedSimplex k)) =
              (V.map θ ≫ g.1) ≫ (singleDegreeTruncatedTopIso B k).hom := by
                rw [homSingleDegreeTruncatedEquivInvApp_top]
                simp [Category.assoc]
            _ = 0 := by
                rw [hleftzero, zero_comp]
            _ =
              homSingleDegreeTruncatedEquivInvApp B k V g (op (topTruncatedSimplex k)) ≫
                (single_degree_truncated B k).map θ := by
                  have hrightzero' :
                      g.1 ≫
                          ((singleDegreeTruncatedTopIso B k).hom ≫
                            (single_degree_truncated B k).map θ) =
                        0 := by
                    simpa [hrightzero] using congrArg (fun t ↦ g.1 ≫ t) hrightzero
                  symm
                  rw [homSingleDegreeTruncatedEquivInvApp_top]
                  simpa [Category.assoc] using hrightzero'
      · have hYzero :=
          (homSingleDegreeTruncatedEquivInvApp_cases B k V g Y).2 hY
        have hYneTop : Y.unop ≠ topTruncatedSimplex k := by
          intro hEq
          exact hY (by simpa [hEq])
        have hXtop : X = op (topTruncatedSimplex k) := op_truncatedSimplex_eq_top X hX
        subst X
        have hnotepi : ¬ Epi θ.unop.hom :=
          not_epi_to_top_of_ne_top Y.unop hYneTop θ.unop
        have hrightzero :
            (singleDegreeTruncatedTopIso B k).hom ≫
                (single_degree_truncated B k).map θ =
              0 := by
          simpa using
            single_degree_truncated_top_comp_map_eq_zero_of_not_epi B θ.unop hnotepi
        -- With top source and lower target, the incoming target component is zero and the
        -- concentrated top copy kills the non-epimorphic map on the right.
        have hrightzero' :
            g.1 ≫
                ((singleDegreeTruncatedTopIso B k).hom ≫
                  (single_degree_truncated B k).map θ) =
              0 := by
          simpa [hrightzero] using congrArg (fun t ↦ g.1 ≫ t) hrightzero
        calc
          V.map θ ≫ homSingleDegreeTruncatedEquivInvApp B k V g Y =
            V.map θ ≫ 0 := by
              rw [hYzero]
          _ = 0 := by simp
          _ =
            homSingleDegreeTruncatedEquivInvApp B k V g (op (topTruncatedSimplex k)) ≫
              (single_degree_truncated B k).map θ := by
                symm
                rw [homSingleDegreeTruncatedEquivInvApp_top]
                simpa [Category.assoc] using hrightzero'
    · by_cases hY : Y.unop.1.len = k
      · have hXzero :=
          (homSingleDegreeTruncatedEquivInvApp_cases B k V g X).2 hX
        have hXneTop : X.unop ≠ topTruncatedSimplex k := by
          intro hEq
          exact hX (by simpa [hEq])
        have hYtop : Y = op (topTruncatedSimplex k) := op_truncatedSimplex_eq_top Y hY
        subst Y
        have hnotmono : ¬ Mono θ.unop.hom :=
          not_mono_from_top_of_ne_top X.unop hXneTop θ.unop
        have hleftzero :
            V.map θ ≫ g.1 = 0 := by
          simpa using
            singleDegreeTruncatedDegeneracyCondition.comp_eq_zero_of_not_mono
              (V := V) (f := g.1) g.2 θ.unop hnotmono
        -- With lower source and top target, the chosen top map vanishes after the non-monomorphic
        -- simplicial operator, while the source component is already zero.
        calc
          V.map θ ≫ homSingleDegreeTruncatedEquivInvApp B k V g (op (topTruncatedSimplex k)) =
            (V.map θ ≫ g.1) ≫ (singleDegreeTruncatedTopIso B k).hom := by
              rw [homSingleDegreeTruncatedEquivInvApp_top]
              simp [Category.assoc]
          _ = 0 := by
              rw [hleftzero, zero_comp]
          _ =
            homSingleDegreeTruncatedEquivInvApp B k V g X ≫
              (single_degree_truncated B k).map θ := by
                rw [hXzero]
                simp
      · have hXzero :=
          (homSingleDegreeTruncatedEquivInvApp_cases B k V g X).2 hX
        have hYzero :=
          (homSingleDegreeTruncatedEquivInvApp_cases B k V g Y).2 hY
        -- Away from top degree both inverse components are definitionally zero.
        rw [hXzero, hYzero]
        simp

/-- Helper for Lemma 14.22.2: the top component of a morphism out of the concentrated object
satisfies the required face-vanishing condition. -/
private theorem singleDegreeTruncated_homEquiv_forward_faceCondition
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (f : single_degree_truncated B k ⟶ V) :
    singleDegreeTruncatedFaceCondition V
      ((singleDegreeTruncatedTopIso B k).hom ≫ f.app (op (topTruncatedSimplex k))) := by
  cases k with
  | zero =>
      trivial
  | succ n =>
      intro i
      let X : SimplexCategory.Truncated (n + 1) := ⟨⦋n⦌, by simp⟩
      let δ := SimplexCategory.Truncated.δ (n + 1) i (by simp) (by simp)
      have hnat :=
        congrArg (fun t ↦ (singleDegreeTruncatedTopIso B (n + 1)).hom ≫ t)
          (f.naturality δ.op).symm
      -- Move the top component across the top face by naturality, then kill the concentrated
      -- top face with the dedicated zero lemma.
      calc
        ((singleDegreeTruncatedTopIso B (n + 1)).hom ≫
            f.app (op (topTruncatedSimplex (n + 1)))) ≫
            V.map δ.op =
          ((singleDegreeTruncatedTopIso B (n + 1)).hom ≫
              (single_degree_truncated B (n + 1)).map δ.op) ≫
            f.app (op X) := by
              simpa [X, δ, Category.assoc] using hnat
        _ = 0 := by
          rw [singleDegreeTruncated_top_comp_map_δ_eq_zero, zero_comp]

/-- Helper for Lemma 14.22.2: the top component of a morphism into the concentrated object
satisfies the required degeneracy-vanishing condition. -/
private theorem hom_singleDegreeTruncatedEquiv_forward_degeneracyCondition
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (f : V ⟶ single_degree_truncated B k) :
    singleDegreeTruncatedDegeneracyCondition V
      (f.app (op (topTruncatedSimplex k)) ≫ (singleDegreeTruncatedTopIso B k).inv) := by
  cases k with
  | zero =>
      trivial
  | succ n =>
      intro i
      let X : SimplexCategory.Truncated (n + 1) := ⟨⦋n⦌, by simp⟩
      let σ := SimplexCategory.Truncated.σ (n + 1) i (by simp) (by simp)
      have hnat :=
        congrArg (fun t ↦ t ≫ (singleDegreeTruncatedTopIso B (n + 1)).inv)
          (f.naturality σ.op)
      -- Move the top component across the top degeneracy by naturality, then kill the
      -- concentrated top degeneracy with the dedicated zero lemma.
      calc
        V.map σ.op ≫ f.app (op (topTruncatedSimplex (n + 1))) ≫
            (singleDegreeTruncatedTopIso B (n + 1)).inv =
          f.app (op X) ≫
            ((single_degree_truncated B (n + 1)).map σ.op ≫
              (singleDegreeTruncatedTopIso B (n + 1)).inv) := by
              simpa [X, σ, Category.assoc] using hnat
        _ = 0 := by
          rw [singleDegreeTruncated_map_σ_comp_top_eq_zero, comp_zero]

/-- Helper for Lemma 14.22.2: a morphism out of the concentrated object is determined by its
degree-`k` component. -/
private theorem singleDegreeTruncated_hom_ext_of_top
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    {f g : single_degree_truncated B k ⟶ V}
    (hfg :
      (singleDegreeTruncatedTopIso B k).hom ≫ f.app (op (topTruncatedSimplex k)) =
        (singleDegreeTruncatedTopIso B k).hom ≫ g.app (op (topTruncatedSimplex k))) :
    f = g := by
  ext X
  by_cases hX : X.unop.1.len = k
  · have hXtop : X = op (topTruncatedSimplex k) := op_truncatedSimplex_eq_top X hX
    subst X
    exact (cancel_epi (singleDegreeTruncatedTopIso B k).hom).1 hfg
  · have hXneTop : X.unop ≠ topTruncatedSimplex k := by
      intro hEq
      exact hX (by simpa [hEq])
    let hzero := singleDegreeTruncated_obj_isZero_of_ne_top B X.unop hXneTop
    -- Away from the top simplex the source object is zero, so every component is unique.
    exact hzero.eq_of_src _ _

/-- Helper for Lemma 14.22.2: a morphism into the concentrated object is determined by its
degree-`k` component. -/
private theorem hom_singleDegreeTruncated_ext_of_top
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    {f g : V ⟶ single_degree_truncated B k}
    (hfg :
      f.app (op (topTruncatedSimplex k)) ≫ (singleDegreeTruncatedTopIso B k).inv =
        g.app (op (topTruncatedSimplex k)) ≫ (singleDegreeTruncatedTopIso B k).inv) :
    f = g := by
  ext X
  by_cases hX : X.unop.1.len = k
  · have hXtop : X = op (topTruncatedSimplex k) := op_truncatedSimplex_eq_top X hX
    subst X
    exact (cancel_mono (singleDegreeTruncatedTopIso B k).inv).1 hfg
  · have hXneTop : X.unop ≠ topTruncatedSimplex k := by
      intro hEq
      exact hX (by simpa [hEq])
    let hzero := singleDegreeTruncated_obj_isZero_of_ne_top B X.unop hXneTop
    -- Away from the top simplex the target object is zero, so every component is unique.
    exact hzero.eq_of_tgt _ _

/-- Helper for Lemma 14.22.2: evaluate a map out of the concentrated object at the top simplex to
obtain the source-facing top component. -/
private noncomputable def singleDegreeTruncated_homEquiv_forward
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (f : single_degree_truncated B k ⟶ V) :
    { g : B ⟶ V _⦋k, le_rfl⦌ₖ // singleDegreeTruncatedFaceCondition V g } :=
  ⟨(singleDegreeTruncatedTopIso B k).hom ≫ f.app (op (topTruncatedSimplex k)),
    singleDegreeTruncated_homEquiv_forward_faceCondition B k V f⟩

/-- Helper for Lemma 14.22.2: the outgoing inverse-component formulas assemble into a natural
transformation. -/
private noncomputable def singleDegreeTruncated_homEquiv_inverse
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : B ⟶ V _⦋k, le_rfl⦌ₖ // singleDegreeTruncatedFaceCondition V f }) :
    single_degree_truncated B k ⟶ V where
  app X := singleDegreeTruncatedHomEquivInvApp B k V g X
  naturality := fun {_ _} θ ↦ singleDegreeTruncatedHomEquivInvNaturality B k V g θ

/-- Helper for Lemma 14.22.2: the packaged outgoing inverse recovers the original natural
transformation. -/
private theorem singleDegreeTruncated_homEquiv_left_inv
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k) :
    Function.LeftInverse
      (singleDegreeTruncated_homEquiv_inverse B k V)
      (singleDegreeTruncated_homEquiv_forward B k V) := by
  intro f
  apply singleDegreeTruncated_hom_ext_of_top B k V
  -- At the top simplex the inverse app is exactly the transported top map, so the iso cancels.
  change (singleDegreeTruncatedTopIso B k).hom ≫
      singleDegreeTruncatedHomEquivInvApp B k V
        (singleDegreeTruncated_homEquiv_forward B k V f) (op (topTruncatedSimplex k)) =
    (singleDegreeTruncatedTopIso B k).hom ≫ f.app (op (topTruncatedSimplex k))
  rw [singleDegreeTruncatedHomEquivInvApp_top]
  simp [singleDegreeTruncated_homEquiv_forward, Category.assoc]

/-- Helper for Lemma 14.22.2: the outgoing forward map recovers the original top component. -/
private theorem singleDegreeTruncated_homEquiv_right_inv
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k) :
    Function.RightInverse
      (singleDegreeTruncated_homEquiv_inverse B k V)
      (singleDegreeTruncated_homEquiv_forward B k V) := by
  intro g
  apply Subtype.ext
  -- Evaluating the inverse at the top simplex returns the chosen top component.
  change (singleDegreeTruncatedTopIso B k).hom ≫
      singleDegreeTruncatedHomEquivInvApp B k V g (op (topTruncatedSimplex k)) =
    g.1
  rw [singleDegreeTruncatedHomEquivInvApp_top]
  simp [singleDegreeTruncated_homEquiv_forward, Category.assoc]

/-- Helper for Lemma 14.22.2: evaluate a map into the concentrated object at the top simplex to
obtain the source-facing top component. -/
private noncomputable def hom_singleDegreeTruncatedEquiv_forward
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (f : V ⟶ single_degree_truncated B k) :
    { g : V _⦋k, le_rfl⦌ₖ ⟶ B // singleDegreeTruncatedDegeneracyCondition V g } :=
  ⟨f.app (op (topTruncatedSimplex k)) ≫ (singleDegreeTruncatedTopIso B k).inv,
    hom_singleDegreeTruncatedEquiv_forward_degeneracyCondition B k V f⟩

/-- Helper for Lemma 14.22.2: the incoming inverse-component formulas assemble into a natural
transformation. -/
private noncomputable def hom_singleDegreeTruncatedEquiv_inverse
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k)
    (g : { f : V _⦋k, le_rfl⦌ₖ ⟶ B // singleDegreeTruncatedDegeneracyCondition V f }) :
    V ⟶ single_degree_truncated B k where
  app X := homSingleDegreeTruncatedEquivInvApp B k V g X
  naturality := fun {_ _} θ ↦ homSingleDegreeTruncatedEquivInvNaturality B k V g θ

/-- Helper for Lemma 14.22.2: the packaged incoming inverse recovers the original natural
transformation. -/
private theorem hom_singleDegreeTruncatedEquiv_left_inv
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k) :
    Function.LeftInverse
      (hom_singleDegreeTruncatedEquiv_inverse B k V)
      (hom_singleDegreeTruncatedEquiv_forward B k V) := by
  intro f
  apply hom_singleDegreeTruncated_ext_of_top B k V
  -- At the top simplex the inverse app is exactly the transported top map, so the iso cancels.
  change homSingleDegreeTruncatedEquivInvApp B k V
      (hom_singleDegreeTruncatedEquiv_forward B k V f) (op (topTruncatedSimplex k)) ≫
        (singleDegreeTruncatedTopIso B k).inv =
      f.app (op (topTruncatedSimplex k)) ≫ (singleDegreeTruncatedTopIso B k).inv
  rw [homSingleDegreeTruncatedEquivInvApp_top]
  simp [hom_singleDegreeTruncatedEquiv_forward, Category.assoc]

/-- Helper for Lemma 14.22.2: the incoming forward map recovers the original top component. -/
private theorem hom_singleDegreeTruncatedEquiv_right_inv
    (B : A) (k : ℕ) (V : SimplicialObject.Truncated A k) :
    Function.RightInverse
      (hom_singleDegreeTruncatedEquiv_inverse B k V)
      (hom_singleDegreeTruncatedEquiv_forward B k V) := by
  intro g
  apply Subtype.ext
  -- Evaluating the inverse at the top simplex returns the chosen top component.
  change homSingleDegreeTruncatedEquivInvApp B k V g (op (topTruncatedSimplex k)) ≫
      (singleDegreeTruncatedTopIso B k).inv =
    g.1
  rw [homSingleDegreeTruncatedEquivInvApp_top]
  simp [hom_singleDegreeTruncatedEquiv_forward, Category.assoc]

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
  let e :
      (single_degree_truncated B k ⟶ V) ≃
        { f : B ⟶ V _⦋k, le_rfl⦌ₖ // singleDegreeTruncatedFaceCondition V f } :=
    { toFun := singleDegreeTruncated_homEquiv_forward B k V
      invFun := singleDegreeTruncated_homEquiv_inverse B k V
      left_inv := singleDegreeTruncated_homEquiv_left_inv B k V
      right_inv := singleDegreeTruncated_homEquiv_right_inv B k V }
  refine ⟨e, ?_, ?_⟩
  · intro f
    rfl
  · intro e' he'
    apply Equiv.ext
    intro f
    apply Subtype.ext
    simpa [e, singleDegreeTruncated_homEquiv_forward] using he' f

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
  let e :
      (V ⟶ single_degree_truncated B k) ≃
        { f : V _⦋k, le_rfl⦌ₖ ⟶ B // singleDegreeTruncatedDegeneracyCondition V f } :=
    { toFun := hom_singleDegreeTruncatedEquiv_forward B k V
      invFun := hom_singleDegreeTruncatedEquiv_inverse B k V
      left_inv := hom_singleDegreeTruncatedEquiv_left_inv B k V
      right_inv := hom_singleDegreeTruncatedEquiv_right_inv B k V }
  refine ⟨e, ?_, ?_⟩
  · intro f
    rfl
  · intro e' he'
    apply Equiv.ext
    intro f
    apply Subtype.ext
    simpa [e, hom_singleDegreeTruncatedEquiv_forward] using he' f

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
  -- TODO: identify the pointwise colimit with the finite biproduct over surviving top-degree
  -- costructured-arrow objects, using the Hom equivalence above to discard non-surjective legs.
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
  -- Route correction: the left Kan-extension unit leg is already normalized by
  -- `singleDegreeTruncatedSkι_eq_unit_map`, so only the functorial head needs rewriting.
  rw [singleDegreeTruncatedSkι_eq_unit_map, singleDegreeTruncatedSkι_eq_unit_map]
  let p :
      B ⟶ (((Truncated.sk k).obj (single_degree_truncated B k)) _⦋k⦌) :=
    (singleDegreeTruncatedTopIso B k).hom ≫
      ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionUnit
        (single_degree_truncated B k)).app (op (topTruncatedSimplex k))
  have htail :
      ((Truncated.sk k).obj (single_degree_truncated B k)).map α.1.op ≫
          ((Truncated.sk k).obj (single_degree_truncated B k)).map φ.op =
        ((Truncated.sk k).obj (single_degree_truncated B k)).map
          (⟨φ ≫ α.1, h⟩ : topEpiIndex k n).1.op := by
    rw [← ((Truncated.sk k).obj (single_degree_truncated B k)).map_comp]
    rfl
  -- Postcompose the tail identity with the fixed unit leg `p`.
  simpa only [p, Category.assoc] using congrArg (fun t ↦ p ≫ t) htail

/-- Helper for Lemma 14.22.2: naturality of the left-Kan-extension unit moves the top unit leg
across an ordinary face map, after which the concentrated-object top face is already zero. -/
private theorem singleDegreeTruncated_unit_top_comp_sk_map_δ_eq_zero
    (B : A) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion (n + 1)).op.HasPointwiseLeftKanExtension F]
    (i : Fin (n + 2)) :
    (singleDegreeTruncatedTopIso B (n + 1)).hom ≫
        ((SimplexCategory.Truncated.inclusion (n + 1)).op.leftKanExtensionUnit
            (single_degree_truncated B (n + 1))).app (op (topTruncatedSimplex (n + 1))) ≫
        ((Truncated.sk (n + 1)).obj (single_degree_truncated B (n + 1))).map
          (SimplexCategory.δ i).op =
      0 := by
  let η := ((SimplexCategory.Truncated.inclusion (n + 1)).op.leftKanExtensionUnit
    (single_degree_truncated B (n + 1)))
  have hnat :=
    congrArg (fun t ↦ (singleDegreeTruncatedTopIso B (n + 1)).hom ≫ t)
      (η.naturality (SimplexCategory.Truncated.δ (n + 1) i (by simp) (by simp)).op)
  -- Move the unit leg across the top face by naturality, then use the concentrated-object
  -- vanishing of the top face map.
  calc
    (singleDegreeTruncatedTopIso B (n + 1)).hom ≫ η.app (op (topTruncatedSimplex (n + 1))) ≫
        ((Truncated.sk (n + 1)).obj (single_degree_truncated B (n + 1))).map
          (SimplexCategory.δ i).op =
      ((singleDegreeTruncatedTopIso B (n + 1)).hom ≫
          (single_degree_truncated B (n + 1)).map
            (SimplexCategory.Truncated.δ (n + 1) i (by simp) (by simp)).op) ≫
        η.app (op (show SimplexCategory.Truncated (n + 1) from ⟨⦋n⦌, by simp⟩)) := by
      simpa [η, Category.assoc] using hnat.symm
    _ = 0 := by
      rw [singleDegreeTruncated_top_comp_map_δ_eq_zero, zero_comp]

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
  cases k with
  | zero =>
      exfalso
      apply h
      rw [SimplexCategory.epi_iff_surjective]
      intro x
      refine ⟨0, ?_⟩
      fin_cases x
      apply Fin.ext
      simp
  | succ k =>
      have hsurj :
          ¬ Function.Surjective (φ ≫ α.1).toOrderHom := by
        rw [← SimplexCategory.epi_iff_surjective]
        exact h
      obtain ⟨i, θ, hφα⟩ :=
        SimplexCategory.eq_comp_δ_of_not_surjective (φ ≫ α.1) hsurj
      rw [singleDegreeTruncatedSkι_eq_unit_map]
      let p :
          B ⟶ (((Truncated.sk (k + 1)).obj (single_degree_truncated B (k + 1))) _⦋k + 1⦌) :=
        (singleDegreeTruncatedTopIso B (k + 1)).hom ≫
          ((SimplexCategory.Truncated.inclusion (k + 1)).op.leftKanExtensionUnit
              (single_degree_truncated B (k + 1))).app (op (topTruncatedSimplex (k + 1)))
      let F : SimplicialObject A := (Truncated.sk (k + 1)).obj (single_degree_truncated B (k + 1))
      have hcomp :
          F.map α.1.op ≫ F.map φ.op = F.map ((φ ≫ α.1).op) := by
        rw [← F.map_comp]
        rfl
      have hfactor :
          F.map ((φ ≫ α.1).op) = F.map (SimplexCategory.δ i).op ≫ F.map θ.op := by
        rw [hφα, op_comp, Functor.map_comp]
      have hzero : p ≫ F.map (SimplexCategory.δ i).op = 0 := by
        simpa [p, F] using singleDegreeTruncated_unit_top_comp_sk_map_δ_eq_zero B k i
      -- Route correction: factor the non-surjective composite through a top face, then apply the
      -- dedicated unit adapter lemma so only the concentrated top-face vanishing remains.
      suffices hmain : ((p ≫ F.map α.1.op) ≫ F.map φ.op) = 0 by
        simpa [p, F, Category.assoc] using hmain
      calc
        (p ≫ F.map α.1.op) ≫ F.map φ.op =
          p ≫ F.map ((φ ≫ α.1).op) := by
          simpa [p, Category.assoc] using congrArg (fun t ↦ p ≫ t) hcomp
        _ = (p ≫ F.map (SimplexCategory.δ i).op) ≫ F.map θ.op := by
          simpa [p, Category.assoc] using congrArg (fun t ↦ p ≫ t) hfactor
        _ = 0 := by
          rw [hzero, zero_comp]

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
  -- TODO: identify the pointwise limit with the finite biproduct over surviving top-degree
  -- structured-arrow objects, using the dual Hom equivalence to kill non-injective projections.
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

/-- Helper for Lemma 14.22.2: composing one simplicial map before the top projection of `cosk_k`
merges the two maps inside the right-Kan-extension functoriality. -/
private theorem singleDegreeTruncatedCosk_map_comp_counit_leg
    (B : A) (k n n' : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    (φ : ⦋n⦌ ⟶ ⦋n'⦌) (β : topMonoIndex k n) :
    ((Truncated.cosk k).obj (single_degree_truncated B k)).map φ.op ≫
        (((Truncated.cosk k).obj (single_degree_truncated B k)).map β.1.op ≫
          ((SimplexCategory.Truncated.inclusion k).op.ranCounit.app
              (single_degree_truncated B k)).app (op (topTruncatedSimplex k)) ≫
            (singleDegreeTruncatedTopIso B k).inv) =
      ((Truncated.cosk k).obj (single_degree_truncated B k)).map ((β.1 ≫ φ).op) ≫
        ((SimplexCategory.Truncated.inclusion k).op.ranCounit.app
            (single_degree_truncated B k)).app (op (topTruncatedSimplex k)) ≫
          (singleDegreeTruncatedTopIso B k).inv := by
  let F : SimplicialObject A := (Truncated.cosk k).obj (single_degree_truncated B k)
  let q :
      F.obj (op ⦋k⦌) ⟶ B :=
    ((SimplexCategory.Truncated.inclusion k).op.ranCounit.app
        (single_degree_truncated B k)).app (op (topTruncatedSimplex k)) ≫
      (singleDegreeTruncatedTopIso B k).inv
  -- Keep the fixed counit leg `q` unchanged and rewrite only the functorial head.
  calc
    F.map φ.op ≫
        (F.map β.1.op ≫
          ((SimplexCategory.Truncated.inclusion k).op.ranCounit.app
              (single_degree_truncated B k)).app (op (topTruncatedSimplex k)) ≫
            (singleDegreeTruncatedTopIso B k).inv) =
      F.map φ.op ≫ (F.map β.1.op ≫ q) := by
      simpa [q]
    _ = (F.map φ.op ≫ F.map β.1.op) ≫ q := by
      simp [Category.assoc]
    _ = F.map ((β.1 ≫ φ).op) ≫ q := by
      rw [← F.map_comp]
      rfl
    _ = F.map ((β.1 ≫ φ).op) ≫
          ((SimplexCategory.Truncated.inclusion k).op.ranCounit.app
              (single_degree_truncated B k)).app (op (topTruncatedSimplex k)) ≫
            (singleDegreeTruncatedTopIso B k).inv := by
      simp [q, Category.assoc]

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
  -- Route correction: the previous obstruction was only the reassociation around the counit leg,
  -- so we normalize that composite first and then rewrite both sides by the explicit projection formula.
  rw [singleDegreeTruncatedCoskπ_eq_map_counit, singleDegreeTruncatedCoskπ_eq_map_counit]
  -- The adapter lemma packages the exact functoriality normalization for this degreewise formula.
  simpa using singleDegreeTruncatedCosk_map_comp_counit_leg B k n n' φ β

/-- Helper for Lemma 14.22.2: naturality of the right-Kan-extension counit moves the top counit
leg across an ordinary degeneracy map, after which the concentrated-object top degeneracy is
already zero. -/
private theorem singleDegreeTruncated_cosk_map_σ_comp_top_counit_eq_zero
    (B : A) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion (n + 1)).op.HasPointwiseRightKanExtension F]
    (i : Fin (n + 1)) :
    ((Truncated.cosk (n + 1)).obj (single_degree_truncated B (n + 1))).map
        (SimplexCategory.σ i).op ≫
      ((SimplexCategory.Truncated.inclusion (n + 1)).op.ranCounit.app
          (single_degree_truncated B (n + 1))).app (op (topTruncatedSimplex (n + 1))) ≫
      (singleDegreeTruncatedTopIso B (n + 1)).inv =
      0 := by
  let ε := ((SimplexCategory.Truncated.inclusion (n + 1)).op.ranCounit.app
    (single_degree_truncated B (n + 1)))
  have hnat :=
    congrArg (fun t ↦ t ≫ (singleDegreeTruncatedTopIso B (n + 1)).inv)
      (ε.naturality (SimplexCategory.Truncated.σ (n + 1) i (by simp) (by simp)).op)
  -- Move the counit leg across the top degeneracy by naturality, then use the concentrated-object
  -- vanishing of the top degeneracy map.
  calc
    ((Truncated.cosk (n + 1)).obj (single_degree_truncated B (n + 1))).map
        (SimplexCategory.σ i).op ≫
        ε.app (op (topTruncatedSimplex (n + 1))) ≫
        (singleDegreeTruncatedTopIso B (n + 1)).inv =
      ε.app (op (show SimplexCategory.Truncated (n + 1) from ⟨⦋n⦌, by simp⟩)) ≫
        ((single_degree_truncated B (n + 1)).map
            (SimplexCategory.Truncated.σ (n + 1) i (by simp) (by simp)).op ≫
          (singleDegreeTruncatedTopIso B (n + 1)).inv) := by
      simpa [ε, Category.assoc] using hnat
    _ = 0 := by
      have hzero :
          (single_degree_truncated B (n + 1)).map
              (SimplexCategory.Truncated.σ (n + 1) i (by simp) (by simp)).op ≫
            (singleDegreeTruncatedTopIso B (n + 1)).inv =
          0 :=
        singleDegreeTruncated_map_σ_comp_top_eq_zero B n i
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            ε.app (op (show SimplexCategory.Truncated (n + 1) from ⟨⦋n⦌, by simp⟩)) ≫ t)
          hzero

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
  cases k with
  | zero =>
      exfalso
      apply h
      rw [SimplexCategory.mono_iff_injective]
      intro x y _
      fin_cases x
      fin_cases y
      rfl
  | succ k =>
      have hinj :
          ¬ Function.Injective (β.1 ≫ φ).toOrderHom := by
        rw [← SimplexCategory.mono_iff_injective]
        exact h
      obtain ⟨i, θ, hβφ⟩ :=
        SimplexCategory.eq_σ_comp_of_not_injective (β.1 ≫ φ) hinj
      rw [singleDegreeTruncatedCoskπ_eq_map_counit]
      -- Route correction: factor the non-injective composite through a top degeneracy, then apply
      -- the dedicated counit adapter lemma so only the concentrated top-degeneracy vanishing remains.
      calc
        ((Truncated.cosk (k + 1)).obj (single_degree_truncated B (k + 1))).map φ.op ≫
            (((Truncated.cosk (k + 1)).obj (single_degree_truncated B (k + 1))).map β.1.op ≫
              ((SimplexCategory.Truncated.inclusion (k + 1)).op.ranCounit.app
                  (single_degree_truncated B (k + 1))).app
                (op (topTruncatedSimplex (k + 1))) ≫
              (singleDegreeTruncatedTopIso B (k + 1)).inv) =
          ((Truncated.cosk (k + 1)).obj (single_degree_truncated B (k + 1))).map
              ((β.1 ≫ φ).op) ≫
            ((SimplexCategory.Truncated.inclusion (k + 1)).op.ranCounit.app
                (single_degree_truncated B (k + 1))).app
              (op (topTruncatedSimplex (k + 1))) ≫
            (singleDegreeTruncatedTopIso B (k + 1)).inv := by
          simpa using singleDegreeTruncatedCosk_map_comp_counit_leg B (k + 1) n n' φ β
        _ =
          ((Truncated.cosk (k + 1)).obj (single_degree_truncated B (k + 1))).map θ.op ≫
            (((Truncated.cosk (k + 1)).obj (single_degree_truncated B (k + 1))).map
                (SimplexCategory.σ i).op ≫
              ((SimplexCategory.Truncated.inclusion (k + 1)).op.ranCounit.app
                  (single_degree_truncated B (k + 1))).app
                (op (topTruncatedSimplex (k + 1))) ≫
              (singleDegreeTruncatedTopIso B (k + 1)).inv) := by
          rw [hβφ, op_comp, Functor.map_comp]
          simp [Category.assoc]
        _ = 0 := by
          rw [singleDegreeTruncated_cosk_map_σ_comp_top_counit_eq_zero, comp_zero]

-- Proof sketch: the comparison map is the adjoint transpose of the inverse unit. Under the
-- source-facing degreewise decompositions, its `(α, β)`-entry is `𝟙_A` exactly when `β` is a
-- section of `α`, and otherwise it is zero.
/-- Helper for Lemma 14.22.2: truncation evaluates a simplicial natural transformation at the top
truncated simplex by taking its ordinary degree-`k` component. -/
private theorem truncation_map_app_top
    {X Y : SimplicialObject A} (k : ℕ) (f : X ⟶ Y) :
    ((truncation k).map f).app (op (topTruncatedSimplex k)) = f.app (op ⦋k⦌) :=
  rfl

/-- Helper for Lemma 14.22.2: at the top simplex, the comparison `skToCosk` followed by the
coskeleton counit is exactly the inverse of the skeleton unit. -/
private theorem singleDegreeTruncated_skToCosk_app_top_comp_counit
    (B : A) (k : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F] :
    (single_degree_truncated B k).skToCosk.app (op ⦋k⦌) ≫
      ((SimplexCategory.Truncated.inclusion k).op.ranCounit.app
          (single_degree_truncated B k)).app (op (topTruncatedSimplex k)) =
      (((asIso (skAdj k).unit).app (single_degree_truncated B k)).inv.app
        (op (topTruncatedSimplex k))) := by
  let U : SimplicialObject.Truncated A k := single_degree_truncated B k
  have h := homEquiv_symm_skToCosk U
  rw [Adjunction.homEquiv_symm_apply] at h
  -- Evaluate the adjunction identity at the top simplex, where `truncation` is just evaluation.
  simpa [U, truncation_map_app_top, Category.assoc] using
    congrArg (fun η ↦ η.app (op (topTruncatedSimplex k))) h

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
      if β.1 ≫ α.1 = 𝟙 (⦋k⦌) then 𝟙 B else 0 :=
by
  -- TODO: use the new top-component helper `singleDegreeTruncated_skToCosk_app_top_comp_counit`
  -- together with naturality of `skToCosk`, naturality of the counit on the top endomorphism
  -- `SimplexCategory.Truncated.Hom.tr (β.1 ≫ α.1)`, and
  -- `single_degree_truncated_top_endomorphism_map_eq_ite`.
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
@[stacks 0190]
theorem singleDegreeTruncated_skToCosk_mono
    (B : A) (k : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ A,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseLeftKanExtension F] :
    Mono (single_degree_truncated B k).skToCosk := by
  -- TODO: apply `NatTrans.mono_iff_mono_app` and use the coefficient formula above together with
  -- chosen monotone sections of surjections `[n] ↠ [k]` to detect each source summand.
  sorry

end ComparisonMono

end CategoryTheory
