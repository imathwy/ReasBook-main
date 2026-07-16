import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_72_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_72_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_73_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ExactPairing
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape
open HomologicalComplex

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
local notation "BoundedCpx" => CochainComplex.bounded (ModuleCat R)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

private abbrev TermwiseFiniteProjective (M : CpxR) : Prop :=
  ∀ n : ℤ, Module.Finite R (M.X n) ∧ Module.Projective R (M.X n)

/- Domain-style sampling:
- primary domain: rigid duality for cochain complexes of `R`-modules, together with the chapter
  owner for module-valued internal-Hom complexes and the boundedness owner from Chapter `13`;
- sampled owner declarations:
  `ExactPairing`,
  `CochainComplex.bounded`,
  `ihom`,
  `rightDualIso`;
- best owner abstraction: the explicit dual complex attached to `M^•` should use the canonical
  closed-category owner `(ihom M).obj (𝟙_ CpxR)`, written source-facing as `M^∨` with the ambient
  closed structure implicit in instances, rather than a second entrywise reimplementation of its
  objects, differential, shape, and `d ∘ d = 0` proof;
- primitive vs. derived:
  the primitive data here are the complex `M`, the exact pairing `ExactPairing M N`, and the
  canonical internal-Hom owner `ihom`; the textbook signed-transpose dual complex is
  derived API over that owner, while boundedness remains owned by `CochainComplex.bounded`.

Source/core/bridge triage:
- `source-facing`: the textbook dual complex `n ↦ Hom_R(M^{-n}, R)` and the duality statements of
  Lemma `15.73.2`;
- `core/canonical`: `ExactPairing`, `CochainComplex.bounded`, and the internal-Hom owner `ihom`;
- `bridge/view`: the internal-Hom-to-unit specialization `(ihom M).obj (𝟙_ CpxR)`, written
  source-facing as `M^∨`.
-/

variable {M N : CochainComplex (ModuleCat R) ℤ}
variable [ExactPairing M N]

private abbrev tensorSummand (M N : CpxR) (p q : ℤ) : ModuleCat R :=
  ((curriedTensor (ModuleCat R)).obj (M.X p)).obj (N.X q)

/-- Helper for Lemma 15.73.2: the diagonal tensor summand `(n,-n)` sits in total degree `0`. -/
private theorem exactPairing_diag_total_degree_zero (n : ℤ) :
    (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, -n) = 0 := by
  simpa using (show n + -n = 0 by simp)

/-- Helper for Lemma 15.73.2: the swapped diagonal tensor summand `(-n,n)` also sits in total
degree `0`. -/
private theorem exactPairing_swapped_diag_total_degree_zero (n : ℤ) :
    (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-n, n) = 0 := by
  simpa [add_comm] using exactPairing_diag_total_degree_zero n

private noncomputable def exactPairing_degreewise_projection (n : ℤ) :
    ((M ⊗ N : CpxR).X 0) ⟶ tensorSummand M N n (-n) :=
  HomologicalComplex.mapBifunctorDesc fun p q _ ↦
    if hp : p = n then
      if hq : q = -n then
        show tensorSummand M N p q ⟶ tensorSummand M N n (-n) from
          eqToHom (by subst p; subst q; rfl)
      else
        show tensorSummand M N p q ⟶ tensorSummand M N n (-n) from
          0
    else
      show tensorSummand M N p q ⟶ tensorSummand M N n (-n) from
        0

/-- Helper for Lemma 15.73.2: postcomposing a descended tensor-totalization map can be checked on
each `(p,q)` summand. -/
@[reassoc]
private theorem iTensorObj_mapBifunctorDesc_assoc
    {K L : CpxR} (n : ℤ) {A B : ModuleCat R}
    (f : ∀ p q
      (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat R)).obj (K.X p)).obj (L.X q) ⟶ A)
    (u : A ⟶ B) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R))
          (c := ComplexShape.up ℤ) (A := A) (j := n) f ≫ u =
      f p q h ≫ u := by
  -- Cross the `tensorObj` abbreviation once and use the owner formula
  -- `HomologicalComplex.ι_mapBifunctorDesc`.
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) (A := A) (j := n) (f := f) p q h)

/-- Helper for Lemma 15.73.2: the degree-`(n,-n)` projection kills every off-diagonal summand and
is stable under arbitrary postcomposition. -/
@[reassoc]
private theorem exactPairing_degreewise_projection_assoc
    {K L : CpxR} (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 0)
    {Z : ModuleCat R} (u : tensorSummand K L n (-n) ⟶ Z) :
    HomologicalComplex.ιTensorObj K L p q 0 h ≫
        exactPairing_degreewise_projection (M := K) (N := L) n ≫ u =
      (if hp : p = n then
        if hq : q = -n then
          (show tensorSummand K L p q ⟶ tensorSummand K L n (-n) from
            eqToHom (by subst p; subst q; rfl))
        else
          (show tensorSummand K L p q ⟶ tensorSummand K L n (-n) from 0)
      else
        (show tensorSummand K L p q ⟶ tensorSummand K L n (-n) from 0)) ≫ u := by
  let f : ∀ p' q'
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = 0),
      tensorSummand K L p' q' ⟶ tensorSummand K L n (-n) :=
    fun p' q' _ ↦ by
      by_cases hp : p' = n
      · by_cases hq : q' = -n
        · exact eqToHom (by subst p'; subst q'; rfl)
        · exact 0
      · exact 0
  -- Route correction: evaluate `mapBifunctorDesc` once, then normalize only the diagonal branch
  -- of the defining `if`-expression.
  simpa [exactPairing_degreewise_projection, f] using
    (iTensorObj_mapBifunctorDesc_assoc
      (R := R) (K := K) (L := L) (n := 0)
      (A := tensorSummand K L n (-n)) (B := Z) f u p q h)

/-- Helper for Lemma 15.73.2: on the unique diagonal summand `(n,-n)`, the degreewise projection
is the identity. -/
@[reassoc]
private theorem exactPairing_degreewise_projection_diag
    {K L : CpxR} (n : ℤ) :
    HomologicalComplex.ιTensorObj K L n (-n) 0
        (exactPairing_diag_total_degree_zero n) ≫
        exactPairing_degreewise_projection (M := K) (N := L) n =
      𝟙 (tensorSummand K L n (-n)) := by
  -- The descended projection keeps exactly the diagonal branch of its defining family.
  simpa using
    (exactPairing_degreewise_projection_assoc (K := K) (L := L) (n := n)
      (p := n) (q := -n) (h := exactPairing_diag_total_degree_zero n) (u := 𝟙 _))

/-- Helper for Lemma 15.73.2: away from the diagonal `(n,-n)`, the degreewise projection
vanishes. -/
@[reassoc]
private theorem exactPairing_degreewise_projection_off_diagonal
    {K L : CpxR} (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 0)
    (hdiag : p ≠ n ∨ q ≠ -n) :
    HomologicalComplex.ιTensorObj K L p q 0 h ≫
        exactPairing_degreewise_projection (M := K) (N := L) n =
      0 := by
  -- Once the summand is not the diagonal one, the relevant branch of the defining family is zero.
  rcases hdiag with hp | hq
  · simpa [hp] using
      (exactPairing_degreewise_projection_assoc (K := K) (L := L) (n := n)
        (p := p) (q := q) (h := h) (u := 𝟙 _))
  · by_cases hp : p = n
    · subst hp
      have hproj :
          HomologicalComplex.ιTensorObj K L p q 0 h ≫
              exactPairing_degreewise_projection (M := K) (N := L) p =
            0 := by
          simpa [hq] using
            (exactPairing_degreewise_projection_assoc (K := K) (L := L) (n := p)
              (p := p) (q := q) (h := h) (u := 𝟙 _))
      simpa [hq] using
        hproj
    · simpa [hp] using
        (exactPairing_degreewise_projection_assoc (K := K) (L := L) (n := n)
          (p := p) (q := q) (h := h) (u := 𝟙 _))

/-- Helper for Lemma 15.73.2: project the total degree `p + q` tensor term onto the chosen
`(p,q)` summand. -/
private noncomputable def exactPairing_bidegree_projection
    (K L : CpxR) (p q : ℤ) :
    ((K ⊗ L : CpxR).X (p + q)) ⟶ tensorSummand K L p q :=
  HomologicalComplex.mapBifunctorDesc fun p' q' _ ↦
    if hp : p' = p then
      if hq : q' = q then
        show tensorSummand K L p' q' ⟶ tensorSummand K L p q from
          eqToHom (by subst p'; subst q'; rfl)
      else
        show tensorSummand K L p' q' ⟶ tensorSummand K L p q from 0
    else
      show tensorSummand K L p' q' ⟶ tensorSummand K L p q from 0

/-- Helper for Lemma 15.73.2: postcomposing a bidegree projection is computed by evaluating the
underlying descended family on the chosen tensor summand. -/
@[reassoc]
private theorem exactPairing_bidegree_projection_assoc
    {K L : CpxR} (p q p' q' : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = p + q)
    {Z : ModuleCat R} (u : tensorSummand K L p q ⟶ Z) :
    HomologicalComplex.ιTensorObj K L p' q' (p + q) h ≫
        exactPairing_bidegree_projection (K := K) (L := L) p q ≫ u =
      (if hp : p' = p then
        if hq : q' = q then
          (show tensorSummand K L p' q' ⟶ tensorSummand K L p q from
            eqToHom (by subst p'; subst q'; rfl))
        else
          (show tensorSummand K L p' q' ⟶ tensorSummand K L p q from 0)
      else
        (show tensorSummand K L p' q' ⟶ tensorSummand K L p q from 0)) ≫ u := by
  let f : ∀ a b
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = p + q),
      tensorSummand K L a b ⟶ tensorSummand K L p q :=
    fun a b _ ↦ by
      by_cases hp : a = p
      · by_cases hq : b = q
        · exact eqToHom (by subst a; subst b; rfl)
        · exact 0
      · exact 0
  -- Route correction: evaluate the descended family on the chosen `(p',q')` summand before
  -- simplifying the diagonal and off-diagonal branches.
  simpa [exactPairing_bidegree_projection, f] using
    (iTensorObj_mapBifunctorDesc_assoc
      (R := R) (K := K) (L := L) (n := p + q)
      (A := tensorSummand K L p q) (B := Z) f u p' q' h)

/-- Helper for Lemma 15.73.2: the chosen `(p,q)` summand survives its own bidegree projection as
the identity. -/
@[reassoc]
private theorem exactPairing_bidegree_projection_diag
    {K L : CpxR} (p q : ℤ) :
    HomologicalComplex.ιTensorObj K L p q (p + q) (by simp) ≫
        exactPairing_bidegree_projection (K := K) (L := L) p q =
      𝟙 (tensorSummand K L p q) := by
  -- The projection keeps exactly the diagonal branch of its defining family.
  simpa using
    (exactPairing_bidegree_projection_assoc (K := K) (L := L) (p := p) (q := q)
      (p' := p) (q' := q) (h := by simp) (u := 𝟙 _))

/-- Helper for Lemma 15.73.2: every tensor summand other than `(p,q)` is killed by the
corresponding bidegree projection. -/
@[reassoc]
private theorem exactPairing_bidegree_projection_off_diagonal
    {K L : CpxR} (p q p' q' : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = p + q)
    (hdiag : p' ≠ p ∨ q' ≠ q) :
    HomologicalComplex.ιTensorObj K L p' q' (p + q) h ≫
        exactPairing_bidegree_projection (K := K) (L := L) p q =
      0 := by
  -- Once the summand differs from `(p,q)`, the selected branch of the descended family is zero.
  rcases hdiag with hp | hq
  · simpa [hp] using
      (exactPairing_bidegree_projection_assoc (K := K) (L := L) (p := p) (q := q)
        (p' := p') (q' := q') (h := h) (u := 𝟙 _))
  · by_cases hp : p' = p
    · subst hp
      have hproj :
          HomologicalComplex.ιTensorObj K L p' q' (p + q) h ≫
              exactPairing_bidegree_projection (K := K) (L := L) p q =
            0 := by
          simpa [hq] using
            (exactPairing_bidegree_projection_assoc (K := K) (L := L) (p := p) (q := q)
              (p' := p) (q' := q') (h := h) (u := 𝟙 _))
      simpa [hq] using hproj
    · simpa [hp] using
        (exactPairing_bidegree_projection_assoc (K := K) (L := L) (p := p) (q := q)
          (p' := p') (q' := q') (h := h) (u := 𝟙 _))

/-- Helper for Lemma 15.73.2: on the swapped diagonal summand `(-n,n)` in `N ⊗ M`, the
corresponding degreewise projection is the identity. -/
private theorem exactPairing_swapped_degreewise_projection_diag
    (n : ℤ) :
    HomologicalComplex.ιTensorObj N M (-n) (-(-n)) 0
        (exactPairing_diag_total_degree_zero (-n)) ≫
        exactPairing_degreewise_projection (M := N) (N := M) (-n) =
      𝟙 (tensorSummand N M (-n) (-(-n))) := by
  -- This is exactly the diagonal projection formula, specialized to the index `-n`.
  simpa using
    (exactPairing_degreewise_projection_diag (K := N) (L := M) (-n))

/-- Helper for Lemma 15.73.2: away from the swapped diagonal `(-n,n)` in `N ⊗ M`, the
corresponding degreewise projection vanishes. -/
private theorem exactPairing_swapped_degreewise_projection_off_diagonal
    (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 0)
    (hdiag : p ≠ -n ∨ q ≠ n) :
    HomologicalComplex.ιTensorObj N M p q 0 h ≫
        exactPairing_degreewise_projection (M := N) (N := M) (-n) =
      0 := by
  -- Reuse the unswapped off-diagonal formula after rewriting the index `-(-n)` to `n`.
  have hdiag' : p ≠ -n ∨ q ≠ -(-n) := by
    simpa [neg_neg] using hdiag
  simpa [neg_neg] using
    (exactPairing_degreewise_projection_off_diagonal
      (K := N) (L := M) (n := -n) (p := p) (q := q) (h := h) hdiag')

/-- The degree-`(n,-n)` coevaluation map extracted from the coevaluation of an exact pairing of
cochain complexes. -/
noncomputable def exactPairing_degreewise_coevaluation (n : ℤ) :
    𝟙_ (ModuleCat R) ⟶ ((M.X n) ⊗ (N.X (-n)) : ModuleCat R) :=
  (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
    ((inferInstance : ExactPairing M N).coevaluation').f 0 ≫
    exactPairing_degreewise_projection n

/-- The degree-`(-n,n)` evaluation map extracted from the evaluation of an exact pairing of
cochain complexes. -/
noncomputable def exactPairing_degreewise_evaluation (n : ℤ) :
    ((N.X (-n)) ⊗ (M.X n) : ModuleCat R) ⟶ 𝟙_ (ModuleCat R) :=
  ιTensorObj N M (-n) n 0 (exactPairing_swapped_diag_total_degree_zero n) ≫
    ((inferInstance : ExactPairing M N).evaluation').f 0 ≫
    (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).hom

/-- Helper for Lemma 15.73.2: the complex-level first triangle identity, when projected to the
diagonal degree `(-n, n)`, becomes the first triangle identity for the degreewise pairing
between `M^n` and `N^{-n}`. -/
private theorem exactPairing_degreewise_coevaluation_evaluation_projection
    (n : ℤ) :
    (N.X (-n) : ModuleCat R) ◁ exactPairing_degreewise_coevaluation (M := M) (N := N) n ≫
        (α_ (N.X (-n) : ModuleCat R) (M.X n : ModuleCat R) (N.X (-n) : ModuleCat R)).inv ≫
        exactPairing_degreewise_evaluation (M := M) (N := N) n ▷ (N.X (-n) : ModuleCat R) =
      (ρ_ (N.X (-n) : ModuleCat R)).hom ≫
        (λ_ (N.X (-n) : ModuleCat R)).inv := by
  -- Start from the complex-level triangle identity before projecting to the diagonal summand.
  have htriangle :
      N ◁ (η_ M N) ≫ (α_ N M N).inv ≫ ε_ M N ▷ N =
        (ρ_ N).hom ≫ (λ_ N).inv := by
    simpa using (ExactPairing.coevaluation_evaluation (X := M) (Y := N))
  have hcomponent :
      (N ◁ (η_ M N) ≫ (α_ N M N).inv ≫ ε_ M N ▷ N).f (-n) =
        ((ρ_ N).hom ≫ (λ_ N).inv).f (-n) := by
    -- Project the complex-level triangle identity to degree `-n`.
    simpa using congrArg (fun f ↦ f.f (-n)) htriangle
  -- The degree `-n` component is exactly the diagonal tensor/evaluation composite.
  simpa [exactPairing_degreewise_coevaluation, exactPairing_degreewise_evaluation, Category.assoc]
    using hcomponent

/-- Helper for Lemma 15.73.2: the complex-level second triangle identity, when projected to the
diagonal degree `(n, -n)`, becomes the second triangle identity for the degreewise pairing
between `M^n` and `N^{-n}`. -/
private theorem exactPairing_degreewise_evaluation_coevaluation_projection
    (n : ℤ) :
    exactPairing_degreewise_coevaluation (M := M) (N := N) n ▷ (M.X n : ModuleCat R) ≫
        (α_ (M.X n : ModuleCat R) (N.X (-n) : ModuleCat R) (M.X n : ModuleCat R)).hom ≫
        (M.X n : ModuleCat R) ◁ exactPairing_degreewise_evaluation (M := M) (N := N) n =
      (λ_ (M.X n : ModuleCat R)).hom ≫
        (ρ_ (M.X n : ModuleCat R)).inv := by
  -- Start from the complex-level triangle identity before isolating the `(n,-n)` tensor summand.
  have htriangle :
      (η_ M N) ▷ M ≫ (α_ M N M).hom ≫ M ◁ ε_ M N =
        (λ_ M).hom ≫ (ρ_ M).inv := by
    simpa using (ExactPairing.evaluation_coevaluation (X := M) (Y := N))
  have hcomponent :
      ((η_ M N) ▷ M ≫ (α_ M N M).hom ≫ M ◁ ε_ M N).f n =
        ((λ_ M).hom ≫ (ρ_ M).inv).f n := by
    -- Project the complex-level triangle identity to degree `n`.
    simpa using congrArg (fun f ↦ f.f n) htriangle
  -- The degree `n` component is exactly the diagonal coevaluation/evaluation composite.
  simpa [exactPairing_degreewise_coevaluation, exactPairing_degreewise_evaluation, Category.assoc]
    using hcomponent

/-- Helper for Lemma 15.73.2: restricting the complex-level coevaluation and evaluation to the
diagonal degree `(n,-n)` yields an exact pairing between `M^n` and `N^{-n}`. -/
@[implicit_reducible]
private noncomputable def exactPairing_degreewise_left_dual_aux (n : ℤ) :
    ExactPairing (M.X n : ModuleCat R) (N.X (-n) : ModuleCat R) where
  coevaluation' := exactPairing_degreewise_coevaluation n
  evaluation' := exactPairing_degreewise_evaluation n
  coevaluation_evaluation' := by
    -- Use the dedicated projection lemma so the degreewise duality proof does not depend on a
    -- fragile `congrArg` simplification step inside the structure field.
    simpa using
      exactPairing_degreewise_coevaluation_evaluation_projection (M := M) (N := N) n
  evaluation_coevaluation' := by
    -- The second triangle identity is handled by the symmetric projection lemma.
    simpa using
      exactPairing_degreewise_evaluation_coevaluation_projection (M := M) (N := N) n

/-- Helper for Lemma 15.73.2: if the diagonal coevaluation component in degree `n` vanishes, then
both participating degreewise terms are zero objects. -/
private theorem exactPairing_degreewise_zero_coevaluation_implies_terms_zero
    (n : ℤ)
    (hcoevaluation : exactPairing_degreewise_coevaluation (M := M) (N := N) n = 0) :
    CategoryTheory.Limits.IsZero (M.X n : ModuleCat R) ∧
      CategoryTheory.Limits.IsZero (N.X (-n) : ModuleCat R) := by
  -- Substitute the vanishing coevaluation into the two degreewise triangle identities. Each
  -- identity first collapses one unitor inverse to zero; composing with the inverse isomorphism
  -- then gives `𝟙 = 0` on the corresponding degreewise term.
  have hMInv :
      (ρ_ (M.X n : ModuleCat R)).inv = 0 := by
    simpa [hcoevaluation, Category.assoc] using
      (exactPairing_degreewise_evaluation_coevaluation_projection (M := M) (N := N) n).symm
  have hNInv :
      (λ_ (N.X (-n) : ModuleCat R)).inv = 0 := by
    simpa [hcoevaluation, Category.assoc] using
      (exactPairing_degreewise_coevaluation_evaluation_projection (M := M) (N := N) n).symm
  have hMId :
      𝟙 (M.X n : ModuleCat R) = 0 := by
    calc
      𝟙 (M.X n : ModuleCat R) =
        (ρ_ (M.X n : ModuleCat R)).inv ≫ (ρ_ (M.X n : ModuleCat R)).hom := by simp
      _ = 0 := by simp [hMInv]
  have hNId :
      𝟙 (N.X (-n) : ModuleCat R) = 0 := by
    calc
      𝟙 (N.X (-n) : ModuleCat R) =
        (λ_ (N.X (-n) : ModuleCat R)).inv ≫ (λ_ (N.X (-n) : ModuleCat R)).hom := by simp
      _ = 0 := by simp [hNInv]
  exact
    ⟨(CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2 hMId,
      (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2 hNId⟩

/-- Helper for Lemma 15.73.2: the pair indices contributing to total tensor degree `n`. -/
private abbrev exactPairing_tensor_degree_preimage (n : ℤ) : Type :=
  { pq : ℤ × ℤ //
      (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) pq = n }

/-- Helper for Lemma 15.73.2: the discrete diagram indexing the total-degree tensor summands. -/
private abbrev exactPairing_tensor_degree_preimage_discrete (n : ℤ) :=
  Discrete (exactPairing_tensor_degree_preimage n)

/-- Helper for Lemma 15.73.2: a pair `(p,q)` with total degree `n` lies in the corresponding
tensor-degree fiber. -/
private theorem exactPairing_tensor_degree_pair_mem
    (p q n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (p, q) ∈ ((ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⁻¹'
      ({n} : Set ℤ)) := by
  simpa using h

/-- Helper for Lemma 15.73.2: the pair `(p,q)` regarded as an index of the total-degree tensor
fiber over `n`. -/
private def exactPairing_tensor_degree_index
    (p q n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    exactPairing_tensor_degree_preimage n :=
  ⟨(p, q), exactPairing_tensor_degree_pair_mem p q n h⟩

/-- Helper for Lemma 15.73.2: the pair-indexed tensor summands contributing to total degree `n`.
-/
private abbrev exactPairing_tensor_degree_summands
    (K L : CpxR) (n : ℤ) :
    exactPairing_tensor_degree_preimage n → ModuleCat R :=
  fun s ↦ tensorSummand K L s.1.1 s.1.2

/-- Helper for Lemma 15.73.2: the underlying module family of the pair-indexed tensor summands in
total degree `n`. -/
private abbrev exactPairing_tensor_degree_summands_type
    (K L : CpxR) (n : ℤ) :
    exactPairing_tensor_degree_preimage n → Type u :=
  fun s ↦ (exactPairing_tensor_degree_summands K L n s : Type u)

/-- Helper for Lemma 15.73.2: the concrete direct-sum module attached to tensor degree `n`. -/
private abbrev exactPairing_tensor_degree_directSum_module
    (K L : CpxR) (n : ℤ) : Type u :=
  DirectSum (exactPairing_tensor_degree_preimage n)
    (exactPairing_tensor_degree_summands_type K L n)

/-- Helper for Lemma 15.73.2: the pair-indexed summand diagram whose colimit is the degree-`n`
term of the tensor totalization. -/
private noncomputable def exactPairing_tensor_degree_diagram
    (K L : CpxR) (n : ℤ) :
    exactPairing_tensor_degree_preimage_discrete n ⥤ ModuleCat R :=
  Discrete.functor fun s ↦ exactPairing_tensor_degree_summands K L n s

/-- Helper for Lemma 15.73.2: the tautological cocone from the pair-indexed tensor summands to
the actual degree-`n` tensor term. -/
private noncomputable def exactPairing_tensor_degree_cocone
    (K L : CpxR) (n : ℤ) :
    Cocone (exactPairing_tensor_degree_diagram K L n) where
  pt := (HomologicalComplex.tensorObj K L).X n
  ι := Discrete.natTrans fun s ↦
    HomologicalComplex.ιTensorObj K L s.as.1.1 s.as.1.2 n s.as.2

/-- Helper for Lemma 15.73.2: the tautological tensor-degree cocone is colimiting by the
universal property of `mapBifunctorDesc`. -/
private noncomputable def exactPairing_tensor_degree_cocone_isColimit
    (K L : CpxR) (n : ℤ) :
    IsColimit (exactPairing_tensor_degree_cocone K L n) :=
  IsColimit.mk
    (fun s ↦
      HomologicalComplex.mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
        (fun p q h ↦ s.ι.app ⟨exactPairing_tensor_degree_index p q n (by simpa using h)⟩))
    (fun s t ↦ by
      -- Restrict the descended map to one summand to recover the specified cocone leg.
      simpa [exactPairing_tensor_degree_cocone] using
        (HomologicalComplex.ι_mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R))
          (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
          (f := fun p q h ↦ s.ι.app ⟨exactPairing_tensor_degree_index p q n (by simpa using h)⟩)
          t.as.1.1 t.as.1.2 t.as.2))
    (fun s m hm ↦ by
      -- Two maps from the tensor degree agree once they agree on every `(p,q)` summand.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      let t : exactPairing_tensor_degree_preimage_discrete n :=
        ⟨exactPairing_tensor_degree_index p q n (by simpa using h)⟩
      have hleg :
          HomologicalComplex.ιTensorObj K L p q n h ≫ m = s.ι.app t := by
        simpa [t, exactPairing_tensor_degree_cocone] using hm t
      have hdesc :
          HomologicalComplex.ιTensorObj K L p q n h ≫
              HomologicalComplex.mapBifunctorDesc
                (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R))
                (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
                (fun p q h ↦ s.ι.app ⟨exactPairing_tensor_degree_index p q n (by simpa using h)⟩) =
            s.ι.app t := by
        simpa [t, exactPairing_tensor_degree_cocone] using
          (HomologicalComplex.ι_mapBifunctorDesc
            (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R))
            (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
            (f := fun p q h ↦ s.ι.app ⟨exactPairing_tensor_degree_index p q n (by simpa using h)⟩)
            p q h)
      exact hleg.trans hdesc.symm)

/-- Helper for Lemma 15.73.2: every tensor degree is canonically the direct sum of its pair-indexed
summands. -/
private noncomputable def exactPairing_tensor_degree_iso_directSum
    (K L : CpxR) (n : ℤ) :
    (HomologicalComplex.tensorObj K L).X n ≅
      ModuleCat.of R (exactPairing_tensor_degree_directSum_module K L n) := by
  let Z := exactPairing_tensor_degree_summands K L n
  let e :
      (HomologicalComplex.tensorObj K L).X n ≅
        colimit (exactPairing_tensor_degree_diagram K L n) :=
    (exactPairing_tensor_degree_cocone_isColimit K L n).coconePointUniqueUpToIso
      (colimit.isColimit (exactPairing_tensor_degree_diagram K L n))
  exact e ≪≫ (Sigma.isoColimit (exactPairing_tensor_degree_diagram K L n)).symm ≪≫
    ModuleCat.coprodIsoDirectSum (R := R) Z

/-- Helper for Lemma 15.73.2: the diagonal index `(n,-n)` viewed inside the total-degree-zero
direct sum. -/
private abbrev exactPairing_diagonalTensorIndex (n : ℤ) :
    exactPairing_tensor_degree_preimage 0 :=
  exactPairing_tensor_degree_index n (-n) 0 (by simp)

/-- Helper for Lemma 15.73.2: under the direct-sum model of the degree-`0` tensor piece, the
canonical summand inclusion becomes the corresponding `DirectSum.lof`. -/
@[reassoc]
private theorem ιTensorObj_exactPairing_tensor_degree_iso_directSum_hom
    (K L : CpxR) (p q : ℤ) (h : p + q = 0) :
    HomologicalComplex.ιTensorObj K L p q 0 (by simpa using h) ≫
        (exactPairing_tensor_degree_iso_directSum K L 0).hom =
      ModuleCat.ofHom
        (DirectSum.lof R (exactPairing_tensor_degree_preimage 0)
          (exactPairing_tensor_degree_summands_type K L 0)
          (exactPairing_tensor_degree_index p q 0 (by simpa using h))) := by
  let Z := exactPairing_tensor_degree_summands K L 0
  let s : exactPairing_tensor_degree_preimage_discrete 0 :=
    ⟨exactPairing_tensor_degree_index p q 0 (by simpa using h)⟩
  let e :
      (HomologicalComplex.tensorObj K L).X 0 ≅ colimit (exactPairing_tensor_degree_diagram K L 0) :=
    (exactPairing_tensor_degree_cocone_isColimit K L 0).coconePointUniqueUpToIso
      (colimit.isColimit (exactPairing_tensor_degree_diagram K L 0))
  have hcolim :
      HomologicalComplex.ιTensorObj K L p q 0 (by simpa using h) ≫ e.hom =
        colimit.ι (exactPairing_tensor_degree_diagram K L 0) s := by
    simpa [s, e, exactPairing_tensor_degree_cocone] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (exactPairing_tensor_degree_cocone_isColimit K L 0)
        (colimit.isColimit (exactPairing_tensor_degree_diagram K L 0)) s
  have hsigma :
      colimit.ι (exactPairing_tensor_degree_diagram K L 0) s ≫
          (Sigma.isoColimit (exactPairing_tensor_degree_diagram K L 0)).inv ≫
            (ModuleCat.coprodIsoDirectSum (R := R) Z).hom =
        Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := by
    change
      ((colimit.ι (exactPairing_tensor_degree_diagram K L 0) s ≫
          (Sigma.isoColimit (exactPairing_tensor_degree_diagram K L 0)).inv) ≫
            (ModuleCat.coprodIsoDirectSum (R := R) Z).hom) =
        Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom
    rw [Sigma.ι_isoColimit_inv]
    change
      Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom =
        Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom
    rfl
  -- Compare the tensor summand injection with the chosen colimit comparison, then pass to the
  -- standard `ModuleCat` direct-sum model.
  calc
    HomologicalComplex.ιTensorObj K L p q 0 (by simpa using h) ≫
        (exactPairing_tensor_degree_iso_directSum K L 0).hom =
      Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := by
        calc
          HomologicalComplex.ιTensorObj K L p q 0 (by simpa using h) ≫
              (exactPairing_tensor_degree_iso_directSum K L 0).hom =
            HomologicalComplex.ιTensorObj K L p q 0 (by simpa using h) ≫ e.hom ≫
              (Sigma.isoColimit (exactPairing_tensor_degree_diagram K L 0)).inv ≫
              (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := by
                simp [exactPairing_tensor_degree_iso_directSum, e, Z, Category.assoc]
          _ =
            colimit.ι (exactPairing_tensor_degree_diagram K L 0) s ≫
              (Sigma.isoColimit (exactPairing_tensor_degree_diagram K L 0)).inv ≫
              (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := by
                rw [hcolim]
          _ = Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := by
                simpa [Category.assoc] using hsigma
    _ = ModuleCat.ofHom
          (DirectSum.lof R (exactPairing_tensor_degree_preimage 0)
            (exactPairing_tensor_degree_summands_type K L 0) s.as) := by
          simpa [Z] using
            (ModuleCat.ι_coprodIsoDirectSum_hom (R := R) (Z := Z) s.as)

/-- Helper for Lemma 15.73.2: under the direct-sum model of the degree-`0` tensor piece, the
diagonal projection is the corresponding direct-sum coordinate projection. -/
private theorem exactPairing_degreewise_projection_eq_directSum_component
    (K L : CpxR) (n : ℤ) :
    exactPairing_degreewise_projection (M := K) (N := L) n =
      (exactPairing_tensor_degree_iso_directSum K L 0).hom ≫
        ModuleCat.ofHom
          (DirectSum.component R (exactPairing_tensor_degree_preimage 0)
            (exactPairing_tensor_degree_summands_type K L 0)
            (exactPairing_diagonalTensorIndex n)) := by
  -- Compare the two projections on each `(p,q)` summand of the degree-`0` tensor totalization.
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  by_cases hdiag : p = n ∧ q = -n
  · rcases hdiag with ⟨hp, hq⟩
    subst hp
    subst hq
    rw [Category.assoc, exactPairing_degreewise_projection_diag]
    rw [Category.assoc, ιTensorObj_exactPairing_tensor_degree_iso_directSum_hom]
    simp [exactPairing_diagonalTensorIndex]
  · have hneq :
        exactPairing_tensor_degree_index p q 0 (by simpa using h) ≠
          exactPairing_diagonalTensorIndex n := by
      intro hs
      have hpair : (p, q) = (n, -n) := congrArg Subtype.val hs
      exact hdiag (Prod.mk.inj_iff.mp hpair)
    have hoff : p ≠ n ∨ q ≠ -n := by
      by_cases hp : p = n
      · right
        intro hq
        exact hdiag ⟨hp, hq⟩
      · exact Or.inl hp
    rw [exactPairing_degreewise_projection_off_diagonal (K := K) (L := L) (n := n)
      (p := p) (q := q) (h := by simpa using h) hoff]
    rw [Category.assoc, ιTensorObj_exactPairing_tensor_degree_iso_directSum_hom]
    ext x
    simpa [exactPairing_diagonalTensorIndex, hneq] using
      (DirectSum.component.of R (exactPairing_tensor_degree_preimage 0)
        (exactPairing_tensor_degree_summands_type K L 0)
        (exactPairing_diagonalTensorIndex n)
        (exactPairing_tensor_degree_index p q 0 (by simpa using h)) x)

/-- Helper for Lemma 15.73.2: every element of the degree-`0` tensor piece has only finitely many
nonzero diagonal components. -/
private theorem exactPairing_finite_diagonal_projection_support
    {K L : CpxR} (z : (K ⊗ L : CpxR).X 0) :
    Set.Finite {n : ℤ | exactPairing_degreewise_projection (M := K) (N := L) n z ≠ 0} := by
  classical
  let z' : ⨁ s : exactPairing_tensor_degree_preimage 0, exactPairing_tensor_degree_summands_type K L 0 s :=
    (exactPairing_tensor_degree_iso_directSum K L 0).hom z
  let T : Finset ℤ := (DFinsupp.support z').image fun s : exactPairing_tensor_degree_preimage 0 ↦ s.1.1
  refine T.finite_toSet.subset ?_
  intro n hn
  have hcomponent :
      DirectSum.component R (exactPairing_tensor_degree_preimage 0)
          (exactPairing_tensor_degree_summands_type K L 0)
          (exactPairing_diagonalTensorIndex n) z' ≠ 0 := by
    -- Transport the diagonal projection across the direct-sum identification.
    rw [← exactPairing_degreewise_projection_eq_directSum_component (K := K) (L := L) (n := n)]
      at hn
    simpa [z'] using hn
  have hsupport :
      exactPairing_diagonalTensorIndex n ∈ DFinsupp.support z' := by
    exact DFinsupp.mem_support_toFun.mpr (by
      simpa [DirectSum.apply_eq_component] using hcomponent)
  refine Finset.mem_image.mpr ?_
  exact ⟨exactPairing_diagonalTensorIndex n, hsupport, by
    simp [exactPairing_diagonalTensorIndex]⟩

/-- Helper for Lemma 15.73.2: the diagonal coevaluation components are nonzero in only finitely
many degrees. -/
private theorem exactPairing_finite_degreewise_coevaluation_support :
    Set.Finite {n : ℤ | exactPairing_degreewise_coevaluation (M := M) (N := N) n ≠ 0} := by
  let z : (M ⊗ N : CpxR).X 0 :=
    ((singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
      ((inferInstance : ExactPairing M N).coevaluation').f 0) (1 : R)
  -- The source proof controls the finite support of the concrete coevaluation element `η(1)`.
  refine (exactPairing_finite_diagonal_projection_support (K := M) (L := N) z).subset ?_
  intro n hn
  -- A morphism `R ⟶ M^n ⊗ N^{-n}` is determined by its value at `1`.
  intro hzero
  apply hn
  ext a
  calc
    exactPairing_degreewise_coevaluation (M := M) (N := N) n a =
      a • exactPairing_degreewise_coevaluation (M := M) (N := N) n 1 := by
        simpa using
          (exactPairing_degreewise_coevaluation (M := M) (N := N) n).map_smul a (1 : R)
    _ = 0 := by
      simp [exactPairing_degreewise_coevaluation, z, hzero]

-- Proof sketch: the coevaluation `η : 𝟙 ⟶ M ⊗ N` has only finitely many nonzero homogeneous
-- components because the tensor unit is concentrated in degree `0`; the triangle identities then
-- force both complexes to vanish outside a finite interval.
/-- Lemma 15.73.2 (1): if `M^•` is a left dual of `N^•` in the monoidal category of cochain
complexes of `R`-modules, then `M^•` is bounded. -/
theorem exactPairing_left_complex_isBounded :
    BoundedCpx M := by
  classical
  obtain ⟨a, ha⟩ := exactPairing_finite_degreewise_coevaluation_support (M := M) (N := N) |>.bddBelow
  obtain ⟨b, hb⟩ := exactPairing_finite_degreewise_coevaluation_support (M := M) (N := N) |>.bddAbove
  refine (CochainComplex.bounded_iff (ModuleCat R) M).2 ?_
  constructor
  · refine (CochainComplex.plus_iff (ModuleCat R) M).2 ?_
    refine ⟨a, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    by_contra hnotzero
    have hmem :
        n ∈ {n : ℤ | exactPairing_degreewise_coevaluation (M := M) (N := N) n ≠ 0} := by
      intro hcoevaluation
      exact hnotzero
        (exactPairing_degreewise_zero_coevaluation_implies_terms_zero
          (M := M) (N := N) n hcoevaluation).1
    exact not_lt_of_ge (ha hmem) hn
  · refine (CochainComplex.minus_iff (ModuleCat R) M).2 ?_
    refine ⟨b, ?_⟩
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    by_contra hnotzero
    have hmem :
        n ∈ {n : ℤ | exactPairing_degreewise_coevaluation (M := M) (N := N) n ≠ 0} := by
      intro hcoevaluation
      exact hnotzero
        (exactPairing_degreewise_zero_coevaluation_implies_terms_zero
          (M := M) (N := N) n hcoevaluation).1
    exact not_lt_of_ge (hb hmem) hn

-- Proof sketch: apply the same boundedness argument after swapping the exact pairing.
/-- Lemma 15.73.2 (2): if `M^•` is a left dual of `N^•`, then `N^•` is bounded. -/
theorem exactPairing_right_complex_isBounded :
    BoundedCpx N := by
  classical
  obtain ⟨a, ha⟩ := exactPairing_finite_degreewise_coevaluation_support (M := M) (N := N) |>.bddBelow
  obtain ⟨b, hb⟩ := exactPairing_finite_degreewise_coevaluation_support (M := M) (N := N) |>.bddAbove
  refine (CochainComplex.bounded_iff (ModuleCat R) N).2 ?_
  constructor
  · refine (CochainComplex.plus_iff (ModuleCat R) N).2 ?_
    refine ⟨-b, ?_⟩
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    by_contra hnotzero
    have hmem :
        -n ∈ {n : ℤ | exactPairing_degreewise_coevaluation (M := M) (N := N) n ≠ 0} := by
      intro hcoevaluation
      exact hnotzero
        (exactPairing_degreewise_zero_coevaluation_implies_terms_zero
          (M := M) (N := N) (-n) hcoevaluation).2
    have hle : -n ≤ b := hb hmem
    exact not_lt_of_ge (by simpa using neg_le_neg hle) hn
  · refine (CochainComplex.minus_iff (ModuleCat R) N).2 ?_
    refine ⟨-a, ?_⟩
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    by_contra hnotzero
    have hmem :
        -n ∈ {n : ℤ | exactPairing_degreewise_coevaluation (M := M) (N := N) n ≠ 0} := by
      intro hcoevaluation
      exact hnotzero
        (exactPairing_degreewise_zero_coevaluation_implies_terms_zero
          (M := M) (N := N) (-n) hcoevaluation).2
    have hge : a ≤ -n := ha hmem
    exact not_lt_of_ge (by simpa using neg_le_neg hge) hn

-- Proof sketch: the degree-`0` components of the coevaluation and evaluation induce a left dual
-- pairing between `M^n` and `N^{-n}`; then apply the single-module duality lemma degreewise.
include N

/-- Lemma 15.73.2 (3): for every `n`, the module `M^n` is finite projective over `R`. -/
theorem exactPairing_left_term_finite_projective (n : ℤ) :
    Module.Finite R (M.X n) ∧ Module.Projective R (M.X n) := by
  -- Restrict the complex duality to the diagonal degree `(n,-n)` and apply Lemma `15.73.1`.
  letI : ExactPairing (ModuleCat.of R (M.X n)) (ModuleCat.of R (N.X (-n))) :=
    exactPairing_degreewise_left_dual_aux (M := M) (N := N) n
  simpa using
    (ExactPairing.exactPairing_target_finite_projective
      (R := R) (M := N.X (-n)) (N := M.X n))

-- Proof sketch: after extracting the degreewise left dual pairing between `M^n` and `N^{-n}`,
-- apply the single-module duality lemma to the dual module `N^{-n}`.
include M

/-- Lemma 15.73.2 (4): for every `n`, the module `N^n` is finite projective over `R`. -/
theorem exactPairing_right_term_finite_projective (n : ℤ) :
    Module.Finite R (N.X n) ∧ Module.Projective R (N.X n) := by
  -- Shift the index to `-n` so that the degreewise pairing has target `N^n`.
  letI : ExactPairing (ModuleCat.of R (M.X (-n))) (ModuleCat.of R (N.X n)) := by
    simpa [neg_neg] using
      (exactPairing_degreewise_left_dual_aux (M := M) (N := N) (-n) :
        ExactPairing (ModuleCat.of R (M.X (-n))) (ModuleCat.of R (N.X (-(-n)))))
  exact
    (ExactPairing.exactPairing_source_finite_projective
      (R := R) (M := N.X n) (N := M.X (-n)))

-- Proof sketch: decompose the degree-`0` parts of the complex coevaluation and evaluation into
-- their homogeneous summands; the triangle identities then restrict to degree `n` and `-n`,
-- yielding the required left dual pairing on modules.
/-- Lemma 15.73.2 (5): the degreewise components `M^n` and `N^{-n}` inherit a left dual pairing
from the exact pairing of complexes. -/
noncomputable abbrev exactPairing_degreewise_left_dual (n : ℤ) :
    ExactPairing (M.X n : ModuleCat R) (N.X (-n) : ModuleCat R) :=
  exactPairing_degreewise_left_dual_aux (M := M) (N := N) n

section ClosedDuality

variable [SymmetricCategory (CochainComplex (ModuleCat R) ℤ)]
variable [MonoidalClosed (CochainComplex (ModuleCat R) ℤ)]
omit N
omit [ExactPairing M N]

/-- The dual complex `M^∨ = \operatorname{Hom}^\bullet_R(M^\bullet, R[0])`, realized as internal
Hom into the tensor unit. -/
noncomputable abbrev moduleComplexDual
    (M : CochainComplex (ModuleCat R) ℤ) :
    CochainComplex (ModuleCat R) ℤ :=
  (ihom M).obj (𝟙_ CpxR)

@[inherit_doc moduleComplexDual]
postfix:max "^∨" => moduleComplexDual

private noncomputable def moduleComplexInternalHomIdUnit
    (M : CochainComplex (ModuleCat R) ℤ) :
    𝟙_ CpxR ⟶ (ihom M).obj M :=
  curry ((ρ_ M).hom)

private abbrev moduleComplexDualTensorToEnd
    (M : CochainComplex (ModuleCat R) ℤ) :
    M ⊗ M^∨ ⟶ (ihom M).obj M :=
  module_complex_tensor_internal_hom_comparison M (𝟙_ CpxR) M ≫
    (ihom M).map ((ρ_ M).hom)

/-- Helper for Lemma 15.73.2: the tensor-to-endomorphism comparison for the canonical dual is the
tensor/internal-Hom comparison followed by postcomposition with the right unitor of `M`. -/
private theorem moduleComplexDualTensorToEnd_eq_comparison_comp
    (M : CochainComplex (ModuleCat R) ℤ) :
    moduleComplexDualTensorToEnd M =
      module_complex_tensor_internal_hom_comparison M (𝟙_ CpxR) M ≫
        (ihom M).map ((ρ_ M).hom) := by
  -- This is just the defining expansion of `moduleComplexDualTensorToEnd`.
  rfl

private noncomputable def moduleComplexDualCoevaluation
    (M : CochainComplex (ModuleCat R) ℤ)
    [IsIso (moduleComplexDualTensorToEnd M)] :
    𝟙_ CpxR ⟶ M ⊗ M^∨ :=
  moduleComplexInternalHomIdUnit M ≫
    inv (moduleComplexDualTensorToEnd M)

private abbrev moduleComplexDualEvaluation
    (M : CochainComplex (ModuleCat R) ℤ) :
    M^∨ ⊗ M ⟶ 𝟙_ CpxR :=
  (β_ M^∨ M).hom ≫ (ihom.ev M).app (𝟙_ CpxR)

/-- Helper for Lemma 15.73.2: once the tensor-to-endomorphism comparison has been inserted, the
remaining left-triangle tail is the evaluation of the internal endomorphism object at `K^∨`. -/
private abbrev moduleComplexDual_left_triangle_inserted_tail
    (K : CochainComplex (ModuleCat R) ℤ) :
    K^∨ ⊗ (ihom K).obj K ⟶ K^∨ :=
  -- This is the canonical precomposition action of endomorphisms of `K` on the dual object
  -- `[K, 𝟙]`, written in source order by inserting the braiding once.
  (β_ K^∨ ((ihom K).obj K)).hom ≫
    MonoidalClosed.comp K K (𝟙_ CpxR)

/-- Helper for Lemma 15.73.2: the coevaluation is defined so that composing it with the
tensor-to-endomorphism comparison recovers the curried identity morphism of `M`. -/
private theorem moduleComplexDualCoevaluation_comp_tensorToEnd
    {K : CochainComplex (ModuleCat R) ℤ}
    [IsIso (moduleComplexDualTensorToEnd K)] :
    moduleComplexDualCoevaluation K ≫ moduleComplexDualTensorToEnd K =
      moduleComplexInternalHomIdUnit K := by
  -- Cancel the inverse introduced in the definition of the coevaluation.
  simp [moduleComplexDualCoevaluation, Category.assoc]

/-- Helper for Lemma 15.73.2: whiskering the coevaluation/comparison identity on the left by the
dual object turns the first-triangle coevaluation prefix into the curried identity map. -/
private theorem moduleComplexDualCoevaluation_whiskerLeft_comp_tensorToEnd
    {K : CochainComplex (ModuleCat R) ℤ}
    [IsIso (moduleComplexDualTensorToEnd K)] :
    K^∨ ◁ moduleComplexDualCoevaluation K ≫
        K^∨ ◁ moduleComplexDualTensorToEnd K =
      K^∨ ◁ moduleComplexInternalHomIdUnit K := by
  -- Whisker the defining comparison equality of the coevaluation by the dual object.
  have hBase :
      moduleComplexDualCoevaluation K ≫ moduleComplexDualTensorToEnd K =
        moduleComplexInternalHomIdUnit K := by
    simp [moduleComplexDualCoevaluation, Category.assoc]
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ K^∨ ◁ k)
      hBase

/-- Helper for Lemma 15.73.2: the curried identity of `M` evaluates back to the left unitor after
braiding the internal-Hom factor past `M`. -/
private theorem moduleComplexInternalHomIdUnit_whiskerRight_evaluation
    (K : CochainComplex (ModuleCat R) ℤ) :
    moduleComplexInternalHomIdUnit K ▷ K ≫
        (β_ ((ihom K).obj K) K).hom ≫
        (ihom.ev K).app K =
      (λ_ K).hom := by
  -- Rewrite the curried identity as `curry' (𝟙 M)` and then use the standard evaluation identity
  -- for `curry'`, followed by the braiding-right-unitor coherence relation.
  change MonoidalClosed.curry' (𝟙 K) ▷ K ≫
      (β_ ((ihom K).obj K) K).hom ≫
      (ihom.ev K).app K =
    (λ_ K).hom
  calc
    MonoidalClosed.curry' (𝟙 K) ▷ K ≫
        (β_ ((ihom K).obj K) K).hom ≫
        (ihom.ev K).app K =
      (β_ (𝟙_ CpxR) K).hom ≫ K ◁ MonoidalClosed.curry' (𝟙 K) ≫
        (ihom.ev K).app K := by
        simp [Category.assoc]
    _ = (β_ (𝟙_ CpxR) K).hom ≫ (ρ_ K).hom := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ (β_ (𝟙_ CpxR) K).hom ≫ k)
          (MonoidalClosed.whiskerLeft_curry'_ihom_ev_app (𝟙 K))
    _ = (λ_ K).hom := by
      simpa [Category.assoc] using braiding_rightUnitor K

/-- Helper for Lemma 15.73.2: braiding the dual factor past the tensor unit turns the left
unitor on `K^∨` into the right unitor. This is the final coherence step in the left triangle
normalization. -/
private theorem moduleComplexDual_braiding_leftUnitor
    (K : CochainComplex (ModuleCat R) ℤ) :
    (β_ K^∨ (𝟙_ CpxR)).hom ≫ (λ_ K^∨).hom =
      (ρ_ K^∨).hom := by
  -- This is the standard braiding-left-unitor coherence specialized to the internal-Hom dual.
  simpa [moduleComplexDual] using braiding_leftUnitor K^∨

/-- Helper for Lemma 15.73.2: the uncurried tensor-to-endomorphism comparison becomes the
book-order evaluation map after braiding the `K` factor to the right. -/
private theorem moduleComplexDualTensorToEnd_braided_uncurry
    (K : CochainComplex (ModuleCat R) ℤ) :
    (β_ (K ⊗ K^∨) K).hom ≫ uncurry (moduleComplexDualTensorToEnd K) =
      moduleComplexDualTensorToEnd K ▷ K ≫
        (β_ ((ihom K).obj K) K).hom ≫
        (ihom.ev K).app K := by
  -- Rewrite `uncurry` as evaluation on the left tensor factor, then move the comparison morphism
  -- past the braiding by naturality.
  rw [uncurry_eq]
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ (ihom.ev K).app K)
      (braiding_naturality (moduleComplexDualTensorToEnd K) (𝟙 K)).symm

/-- Helper for Lemma 15.73.2: in the symmetric monoidal category of cochain complexes, braiding
an object past itself twice is the identity. -/
private theorem cochainComplexBraiding_self_square_canonical
    (K : CochainComplex (ModuleCat R) ℤ) :
    (β_ K K).hom ≫ (β_ K K).hom = 𝟙 (K ⊗ K) := by
  -- Route correction: after specializing the closed-duality block to a symmetric owner, the
  -- self-braiding square is exactly the canonical symmetry relation.
  simpa using
    (SymmetricCategory.symmetry (X := K) (Y := K) :
      (β_ K K).hom ≫ (β_ K K).hom = 𝟙 (K ⊗ K))

/-- Helper for Lemma 15.73.2: the residual braiding-associator composite on
`((K ⊗ K^∨) ⊗ K)` collapses to the book-order evaluation braid because cochain complexes carry
the symmetric Koszul braiding. -/
private theorem moduleComplexDual_explicitEvaluation_hexagon
    (K : CochainComplex (ModuleCat R) ℤ) :
    (β_ (K ⊗ K^∨) K).hom ≫
        (α_ K K K^∨).inv ≫
        (β_ K K).hom ▷ K^∨ ≫
        (α_ K K K^∨).hom =
      (α_ K K^∨ K).hom ≫
        K ◁ (β_ K^∨ K).hom := by
  -- Specialize the reverse hexagon to `(K, K^∨, K)` and then use symmetry on `K ⊗ K`.
  apply (cancel_epi (α_ K K^∨ K).inv).1
  have hHex :
      (α_ K K^∨ K).inv ≫
          (β_ (K ⊗ K^∨) K).hom ≫
          (α_ K K K^∨).inv =
        K ◁ (β_ K^∨ K).hom ≫
          (α_ K K K^∨).inv ≫
          (β_ K K).hom ▷ K^∨ := by
    simpa using (BraidedCategory.hexagon_reverse K K^∨ K)
  have hSym :
      (β_ K K).hom ▷ K^∨ ≫
          (β_ K K).hom ▷ K^∨ =
        𝟙 ((K ⊗ K) ⊗ K^∨) := by
    calc
      (β_ K K).hom ▷ K^∨ ≫
          (β_ K K).hom ▷ K^∨ =
        ((β_ K K).hom ≫ (β_ K K).hom) ▷ K^∨ := by
          rw [comp_whiskerRight]
      _ = 𝟙 ((K ⊗ K) ⊗ K^∨) := by
        simpa using
          congrArg
            (fun k ↦ k ▷ K^∨)
            (cochainComplexBraiding_self_square_canonical (R := R) K)
  calc
    (α_ K K^∨ K).inv ≫
        ((β_ (K ⊗ K^∨) K).hom ≫
          (α_ K K K^∨).inv ≫
          (β_ K K).hom ▷ K^∨ ≫
          (α_ K K K^∨).hom) =
      ((α_ K K^∨ K).inv ≫
          (β_ (K ⊗ K^∨) K).hom ≫
          (α_ K K K^∨).inv) ≫
        (β_ K K).hom ▷ K^∨ ≫
        (α_ K K K^∨).hom := by
          simp [Category.assoc]
    _ =
      (K ◁ (β_ K^∨ K).hom ≫
          (α_ K K K^∨).inv ≫
          (β_ K K).hom ▷ K^∨) ≫
        (β_ K K).hom ▷ K^∨ ≫
        (α_ K K K^∨).hom := by
          rw [hHex]
    _ =
      K ◁ (β_ K^∨ K).hom ≫
        (α_ K K K^∨).inv ≫
        ((β_ K K).hom ▷ K^∨ ≫
          (β_ K K).hom ▷ K^∨) ≫
        (α_ K K K^∨).hom := by
          simp [Category.assoc]
    _ = (α_ K K^∨ K).inv ≫
          (α_ K K^∨ K).hom ≫
          K ◁ (β_ K^∨ K).hom := by
      simp [hSym, Category.assoc]

/-- Helper for Lemma 15.73.2: after postcomposing with the right unitor, evaluating against the
explicit dual factor agrees with evaluating after the tensor-to-endomorphism comparison. -/
private theorem moduleComplexDual_explicitEvaluation_expand
    (K : CochainComplex (ModuleCat R) ℤ) :
    (α_ K K^∨ K).hom ≫ K ◁ moduleComplexDualEvaluation K ≫ (ρ_ K).hom =
      (α_ K K^∨ K).hom ≫
        K ◁ (β_ K^∨ K).hom ≫
        K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫
        (ρ_ K).hom := by
  -- Unfold the explicit evaluation morphism once so the remaining transport is purely braided
  -- coherence on the `K`, `K^∨`, and `K` factors.
  simp [moduleComplexDualEvaluation, Category.assoc]

/-- Helper for Lemma 15.73.2: the explicit evaluation composite is the braided form of the
canonical uncurried comparison morphism. -/
private theorem moduleComplexDual_explicitEvaluation_braided_normal_form
    (K : CochainComplex (ModuleCat R) ℤ) :
    (α_ K K^∨ K).hom ≫
        K ◁ (β_ K^∨ K).hom ≫
        K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫
        (ρ_ K).hom =
      (β_ (K ⊗ K^∨) K).hom ≫
        (α_ K K K^∨).inv ≫
        (β_ K K).hom ▷ K^∨ ≫
        (α_ K K K^∨).hom ≫
        K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫
        (ρ_ K).hom := by
  -- Normalize the residual braiding/associator block by the specialized hexagon identity, while
  -- keeping the final evaluation and unitor tail untouched.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫ (ρ_ K).hom)
      (moduleComplexDual_explicitEvaluation_hexagon (M := M) (K := K)).symm

/-- Helper for Lemma 15.73.2: the braided explicit-evaluation normal form is exactly the
braided `uncurry` of `moduleComplexDualTensorToEnd`. -/
private theorem moduleComplexDual_explicitEvaluation_uncurry_bridge
    (K : CochainComplex (ModuleCat R) ℤ) :
    (β_ (K ⊗ K^∨) K).hom ≫
        (α_ K K K^∨).inv ≫
        (β_ K K).hom ▷ K^∨ ≫
        (α_ K K K^∨).hom ≫
        K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫
        (ρ_ K).hom =
      (β_ (K ⊗ K^∨) K).hom ≫
        uncurry (moduleComplexDualTensorToEnd K) := by
  -- Reuse the already established uncurried comparison formula, then postcompose it with the
  -- same outer braiding seen in the textbook left-triangle calculation.
  have hUncurry :
      uncurry (moduleComplexDualTensorToEnd K) =
        (α_ K K K^∨).inv ≫
          (β_ K K).hom ▷ K^∨ ≫
          (α_ K K K^∨).hom ≫
          K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫
          (ρ_ K).hom := by
    rw [show moduleComplexDualTensorToEnd K =
      module_complex_tensor_internal_hom_comparison K (𝟙_ CpxR) K ≫
        (ihom K).map ((ρ_ K).hom) by rfl,
      MonoidalClosed.uncurry_natural_right]
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ k ≫ (ρ_ K).hom)
        (module_complex_tensor_internal_hom_comparison_uncurry
          K (𝟙_ CpxR) K)
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ (β_ (K ⊗ K^∨) K).hom ≫ k)
      hUncurry.symm

/-- Helper for Lemma 15.73.2: after postcomposing with the right unitor, evaluating against the
explicit dual factor agrees with evaluating after the tensor-to-endomorphism comparison. -/
private theorem moduleComplexDual_explicitEvaluation_comp_rightUnitor
    (K : CochainComplex (ModuleCat R) ℤ) :
    (α_ K K^∨ K).hom ≫ K ◁ moduleComplexDualEvaluation K ≫ (ρ_ K).hom =
      moduleComplexDualTensorToEnd K ▷ K ≫
        (β_ ((ihom K).obj K) K).hom ≫
        (ihom.ev K).app K := by
  -- Route correction: rewrite the explicit evaluation into the uncurried comparison composite,
  -- normalize the residual coherence with the specialized hexagon lemma, and finish by the
  -- already established braided `uncurry` formula.
  calc
    (α_ K K^∨ K).hom ≫ K ◁ moduleComplexDualEvaluation K ≫ (ρ_ K).hom =
      (α_ K K^∨ K).hom ≫
        K ◁ (β_ K^∨ K).hom ≫
        K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫
        (ρ_ K).hom := by
          simpa using moduleComplexDual_explicitEvaluation_expand (M := M) K
    _ =
      (β_ (K ⊗ K^∨) K).hom ≫
        (α_ K K K^∨).inv ≫
        (β_ K K).hom ▷ K^∨ ≫
        (α_ K K K^∨).hom ≫
        K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫
        (ρ_ K).hom := by
          simpa using
            moduleComplexDual_explicitEvaluation_braided_normal_form (M := M) K
    _ =
      (β_ (K ⊗ K^∨) K).hom ≫
        uncurry (moduleComplexDualTensorToEnd K) := by
          simpa using
            moduleComplexDual_explicitEvaluation_uncurry_bridge (M := M) K
    _ =
      moduleComplexDualTensorToEnd K ▷ K ≫
        (β_ ((ihom K).obj K) K).hom ≫
        (ihom.ev K).app K := by
          simpa [Category.assoc] using
            moduleComplexDualTensorToEnd_braided_uncurry (M := M) (K := K)

/-- Helper for Lemma 15.73.2: once a left-handed evaluation bridge inserts the factor
`K^∨ ◁ moduleComplexDualTensorToEnd K`, the coevaluation prefix can already be replaced by the
curried identity map `K^∨ ◁ moduleComplexInternalHomIdUnit K`. -/
private theorem moduleComplexDual_left_triangle_prefix_transport
    {K : CochainComplex (ModuleCat R) ℤ}
    [IsIso (moduleComplexDualTensorToEnd K)] :
    K^∨ ◁ moduleComplexDualCoevaluation K ≫
        K^∨ ◁ moduleComplexDualTensorToEnd K ≫
        moduleComplexDual_left_triangle_inserted_tail K =
      K^∨ ◁ moduleComplexInternalHomIdUnit K ≫
        moduleComplexDual_left_triangle_inserted_tail K := by
  -- Postcompose the whiskered coevaluation/comparison identity with the now-canonical evaluation
  -- tail at `K^∨`.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ moduleComplexDual_left_triangle_inserted_tail K)
      (moduleComplexDualCoevaluation_whiskerLeft_comp_tensorToEnd (M := M) (K := K))

/-- Helper for Lemma 15.73.2: after postcomposing with the left unitor on `K^∨`, the remaining
left-triangle suffix is just the explicit braiding/evaluation composite defining
`moduleComplexDualEvaluation K`. -/
private theorem moduleComplexDual_left_triangle_suffix_expand
    (K : CochainComplex (ModuleCat R) ℤ) :
    (α_ K^∨ K K^∨).inv ≫
        moduleComplexDualEvaluation K ▷ K^∨ ≫
        (λ_ K^∨).hom =
      (α_ K^∨ K K^∨).inv ≫
        (β_ K^∨ K).hom ▷ K^∨ ≫
        (ihom.ev K).app (𝟙_ CpxR) ▷ K^∨ ≫
        (λ_ K^∨).hom := by
  -- Unfold the explicit evaluation morphism once so the remaining blocker is purely coherence.
  simp [moduleComplexDualEvaluation, Category.assoc]

/-- Helper for Lemma 15.73.2: the inserted left-triangle tail is literally the braiding followed
by the curried enriched composition morphism `comp K K (𝟙)`. -/
private theorem moduleComplexDual_left_triangle_inserted_tail_expand
    (K : CochainComplex (ModuleCat R) ℤ) :
    moduleComplexDual_left_triangle_inserted_tail K =
      (β_ K^∨ ((ihom K).obj K)).hom ≫
        curry (MonoidalClosed.compTranspose K K (𝟙_ CpxR)) := by
  -- Rewrite `comp` once to expose the curried composition tail needed by the blocked bridge.
  rw [moduleComplexDual_left_triangle_inserted_tail, MonoidalClosed.comp_eq]

/-- Helper for Lemma 15.73.2: the tensor-to-endomorphism comparison is the curry of the normalized
uncurried suffix obtained by moving the left `K`-factor into the slot seen by the closed
adjunction. -/
private theorem moduleComplexDualTensorToEnd_eq_curry_uncurry_normal_form
    (K : CochainComplex (ModuleCat R) ℤ) :
    moduleComplexDualTensorToEnd K =
      curry
        ((α_ K K K^∨).inv ≫
          (β_ K K).hom ▷ K^∨ ≫
          (α_ K K K^∨).hom ≫
          K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫
          (ρ_ K).hom) := by
  -- Compare the two morphisms after uncurrying so the existing comparison-uncurry formula can be
  -- reused without introducing a second transport layer.
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry]
  rw [show moduleComplexDualTensorToEnd K =
    module_complex_tensor_internal_hom_comparison K (𝟙_ CpxR) K ≫
      (ihom K).map ((ρ_ K).hom) by rfl,
    MonoidalClosed.uncurry_natural_right]
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ (ρ_ K).hom)
      (module_complex_tensor_internal_hom_comparison_uncurry K (𝟙_ CpxR) K)

/-- Helper for Lemma 15.73.2: after expanding the left-triangle suffix, the remaining transport
step is the explicit suffix-only coherence comparison between the whiskered curried comparison
map and the book-order evaluation composite. -/
private theorem moduleComplexDual_left_triangle_inserted_tail_curry_normal_form
    (K : CochainComplex (ModuleCat R) ℤ) :
    K^∨ ◁
        curry
          ((α_ K K K^∨).inv ≫
            (β_ K K).hom ▷ K^∨ ≫
            (α_ K K K^∨).hom ≫
            K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫
            (ρ_ K).hom) ≫
        (β_ K^∨ ((ihom K).obj K)).hom ≫
        curry (MonoidalClosed.compTranspose K K (𝟙_ CpxR)) =
        (α_ K^∨ K K^∨).inv ≫
        (β_ K^∨ K).hom ▷ K^∨ ≫
        (ihom.ev K).app (𝟙_ CpxR) ▷ K^∨ ≫
        (λ_ K^∨).hom := by
  -- Route correction: the remaining problem is closed-monoidal transport, so the intended next
  -- step is to compare these suffixes after pushing them through `MonoidalClosed.uncurry`.
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  calc
    K ◁ (K^∨ ◁
          curry
            ((α_ K K K^∨).inv ≫
              (β_ K K).hom ▷ K^∨ ≫
              (α_ K K K^∨).hom ≫
              K ◁ (ihom.ev K).app (𝟙_ CpxR) ≫
              (ρ_ K).hom)) ≫
        (α_ K K^∨ ((ihom K).obj K)).inv ≫
        (β_ K (K^∨ ⟶[CpxR] K^∨)).hom ▷ ((ihom K).obj K) ≫
        (α_ K (K^∨ ⟶[CpxR] K^∨) ((ihom K).obj K)).hom ≫
        (β_ K^∨ ((ihom K).obj K)).hom ≫
        MonoidalClosed.comp K K (𝟙_ CpxR) =
      (α_ K K^∨ K^∨).inv ≫
        (β_ K K^∨).hom ▷ K^∨ ≫
        (α_ K^∨ K K^∨).inv ≫
        (β_ K^∨ K).hom ▷ K^∨ ≫
        (ihom.ev K).app (𝟙_ CpxR) ▷ K^∨ ≫
        (λ_ K^∨).hom := by
          simp [Category.assoc]

/-- Helper for Lemma 15.73.2: after expanding the left-triangle suffix, the remaining transport
step is to insert the factor `K^∨ ◁ moduleComplexDualTensorToEnd K` before applying the
evaluation tail. -/
private theorem moduleComplexDual_left_triangle_uncurry_whiskerLeft_bridge
    {K : CochainComplex (ModuleCat R) ℤ}
    [IsIso (moduleComplexDualTensorToEnd K)] :
    (α_ K^∨ K K^∨).inv ≫
        moduleComplexDualEvaluation K ▷ K^∨ ≫
        (λ_ K^∨).hom =
      K^∨ ◁ moduleComplexDualTensorToEnd K ≫
        moduleComplexDual_left_triangle_inserted_tail K := by
  -- Route correction: isolate the transport fight at the suffix level before reattaching the
  -- coevaluation prefix. The intended proof is to rewrite both sides with
  -- `moduleComplexDual_left_triangle_suffix_expand`, rewrite the inserted comparison map by the
  -- new curry normal form `moduleComplexDualTensorToEnd_eq_curry_uncurry_normal_form`, and reduce
  -- the remaining work to the specific inserted-tail coherence equality.
  rw [moduleComplexDual_left_triangle_suffix_expand (M := M) (K := K),
    moduleComplexDualTensorToEnd_eq_curry_uncurry_normal_form (M := M) (K := K),
    moduleComplexDual_left_triangle_inserted_tail_expand (M := M) (K := K)]
  -- The bridge itself is now reduced to the isolated suffix-only coherence lemma.
  simpa [Category.assoc] using
    (moduleComplexDual_left_triangle_inserted_tail_curry_normal_form (M := M) (K := K)).symm

/-- Helper for Lemma 15.73.2: after expanding the left-triangle suffix, the remaining transport
step is to insert the factor `K^∨ ◁ moduleComplexDualTensorToEnd K` before applying the
evaluation tail, and this becomes a suffix-only comparison after factoring out the coevaluation
prefix. -/
private theorem moduleComplexDual_left_triangle_postunitor_bridge_via_uncurry
    {K : CochainComplex (ModuleCat R) ℤ}
    [IsIso (moduleComplexDualTensorToEnd K)] :
    K^∨ ◁ moduleComplexDualCoevaluation K ≫
        (α_ K^∨ K K^∨).inv ≫
        moduleComplexDualEvaluation K ▷ K^∨ ≫
        (λ_ K^∨).hom =
      K^∨ ◁ moduleComplexDualCoevaluation K ≫
        K^∨ ◁ moduleComplexDualTensorToEnd K ≫
        moduleComplexDual_left_triangle_inserted_tail K := by
  -- Reattach the coevaluation prefix to the suffix-only comparison obtained from the uncurry
  -- bridge.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ K^∨ ◁ moduleComplexDualCoevaluation K ≫ k)
      (moduleComplexDual_left_triangle_uncurry_whiskerLeft_bridge (M := M) (K := K))

omit M in
/-- Helper for Lemma 15.73.2: after replacing the curried identity map by
`MonoidalClosed.id K`, the residual inserted tail is the standard `id_comp` composite for the
closed structure, so the left-triangle suffix closes to the right unitor of `K^∨`. -/
private theorem moduleComplexDual_left_triangle_id_tail
    (K : CochainComplex (ModuleCat R) ℤ) :
    K^∨ ◁ moduleComplexInternalHomIdUnit K ≫
        moduleComplexDual_left_triangle_inserted_tail K =
      (ρ_ K^∨).hom := by
  -- Replace the curried identity by `MonoidalClosed.id K`, then use braiding naturality to move
  -- it across the explicit dual factor before applying the standard `id_comp` identity.
  change K^∨ ◁ MonoidalClosed.id K ≫
      (β_ K^∨ ((ihom K).obj K)).hom ≫
      MonoidalClosed.comp K K (𝟙_ CpxR) =
    (ρ_ K^∨).hom
  have hNat :
      K^∨ ◁ MonoidalClosed.id K ≫
          (β_ K^∨ ((ihom K).obj K)).hom =
        (β_ K^∨ (𝟙_ CpxR)).hom ≫
          MonoidalClosed.id K ▷ K^∨ := by
    -- Naturality of the braiding swaps the inserted identity map to the right.
    simpa [Category.assoc] using
      (CategoryTheory.BraidedCategory.braiding_naturality
        (𝟙 K^∨) (MonoidalClosed.id K)).symm
  have hIdComp :
      MonoidalClosed.id K ▷ K^∨ ≫
          MonoidalClosed.comp K K (𝟙_ CpxR) =
        (λ_ K^∨).hom := by
    -- `id_comp` is the closed-category statement that the internal identity acts trivially.
    apply (cancel_epi (λ_ K^∨).inv).1
    simpa [Category.assoc] using MonoidalClosed.id_comp K (𝟙_ CpxR)
  calc
    K^∨ ◁ MonoidalClosed.id K ≫
        (β_ K^∨ ((ihom K).obj K)).hom ≫
        MonoidalClosed.comp K K (𝟙_ CpxR) =
      (β_ K^∨ (𝟙_ CpxR)).hom ≫
        MonoidalClosed.id K ▷ K^∨ ≫
        MonoidalClosed.comp K K (𝟙_ CpxR) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ MonoidalClosed.comp K K (𝟙_ CpxR))
              hNat
    _ = (β_ K^∨ (𝟙_ CpxR)).hom ≫
          (λ_ K^∨).hom := by
            rw [hIdComp]
    _ = (ρ_ K^∨).hom := by
      simpa using CategoryTheory.braiding_leftUnitor K^∨

private theorem moduleComplexDual_coevaluation_evaluation
    {M : CochainComplex (ModuleCat R) ℤ}
    [IsIso (moduleComplexDualTensorToEnd M)] :
    M^∨ ◁ moduleComplexDualCoevaluation M ≫
        (α_ _ _ _).inv ≫
        moduleComplexDualEvaluation M ▷ M^∨ =
      (ρ_ M^∨).hom ≫
        (λ_ M^∨).inv := by
  -- Postcompose with the left unitor, replace the suffix by the tensor-to-endomorphism bridge,
  -- and then collapse the remaining tail with the closed-category identity morphism.
  apply (cancel_mono (λ_ M^∨).hom).1
  calc
    M^∨ ◁ moduleComplexDualCoevaluation M ≫
        (α_ _ _ _).inv ≫
        moduleComplexDualEvaluation M ▷ M^∨ ≫
        (λ_ M^∨).hom =
      M^∨ ◁ moduleComplexDualCoevaluation M ≫
        M^∨ ◁ moduleComplexDualTensorToEnd M ≫
        moduleComplexDual_left_triangle_inserted_tail M := by
          simpa [Category.assoc] using
            moduleComplexDual_left_triangle_postunitor_bridge_via_uncurry (M := M) (K := M)
    _ =
      M^∨ ◁ moduleComplexInternalHomIdUnit M ≫
        moduleComplexDual_left_triangle_inserted_tail M := by
          simpa [Category.assoc] using
            moduleComplexDual_left_triangle_prefix_transport (M := M) (K := M)
    _ = (ρ_ M^∨).hom := by
      simpa using moduleComplexDual_left_triangle_id_tail (R := R) (K := M)
    _ = ((ρ_ M^∨).hom ≫ (λ_ M^∨).inv) ≫ (λ_ M^∨).hom := by
      simp [Category.assoc]

private theorem moduleComplexDual_evaluation_coevaluation
    {M : CochainComplex (ModuleCat R) ℤ}
    [IsIso (moduleComplexDualTensorToEnd M)] :
    moduleComplexDualCoevaluation M ▷ M ≫
        (α_ _ _ _).hom ≫
        M ◁ moduleComplexDualEvaluation M =
      (λ_ M).hom ≫ (ρ_ M).inv := by
  -- Route correction: reduce the triangle identity to the universal evaluation identity for the
  -- curried identity map, leaving only the tensor-to-endomorphism comparison bridge as a helper.
  apply (cancel_mono (ρ_ M).hom).1
  have hCoevComp :
      moduleComplexDualCoevaluation M ≫ moduleComplexDualTensorToEnd M =
        moduleComplexInternalHomIdUnit M := by
    -- The coevaluation is defined using the inverse of the comparison morphism.
    simp [moduleComplexDualCoevaluation, Category.assoc]
  have hEval :
      moduleComplexDualCoevaluation M ▷ M ≫
          moduleComplexDualTensorToEnd M ▷ M ≫
          (β_ ((ihom M).obj M) M).hom ≫
          (ihom.ev M).app M =
        (λ_ M).hom := by
    have hWhisker :
        moduleComplexDualCoevaluation M ▷ M ≫
            moduleComplexDualTensorToEnd M ▷ M ≫
            (β_ ((ihom M).obj M) M).hom ≫
            (ihom.ev M).app M =
          moduleComplexInternalHomIdUnit M ▷ M ≫
            (β_ ((ihom M).obj M) M).hom ≫
            (ihom.ev M).app M := by
      -- Whisker the defining equality of the coevaluation by `M`.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ▷ M ≫
            (β_ ((ihom M).obj M) M).hom ≫
            (ihom.ev M).app M)
          hCoevComp
    have hIdUnit :
        moduleComplexInternalHomIdUnit M ▷ M ≫
            (β_ ((ihom M).obj M) M).hom ≫
            (ihom.ev M).app M =
          (λ_ M).hom := by
      -- Rewrite the curried identity as `curry' (𝟙 M)` and evaluate it directly.
      change MonoidalClosed.curry' (𝟙 M) ▷ M ≫
          (β_ ((ihom M).obj M) M).hom ≫
          (ihom.ev M).app M =
        (λ_ M).hom
      calc
        MonoidalClosed.curry' (𝟙 M) ▷ M ≫
            (β_ ((ihom M).obj M) M).hom ≫
            (ihom.ev M).app M =
          (β_ (𝟙_ CpxR) M).hom ≫ M ◁ MonoidalClosed.curry' (𝟙 M) ≫
            (ihom.ev M).app M := by
            simp [Category.assoc]
        _ = (β_ (𝟙_ CpxR) M).hom ≫ (ρ_ M).hom := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ (β_ (𝟙_ CpxR) M).hom ≫ k)
              (MonoidalClosed.whiskerLeft_curry'_ihom_ev_app (𝟙 M))
        _ = (λ_ M).hom := by
          simpa [Category.assoc] using braiding_rightUnitor M
    exact hWhisker.trans hIdUnit
  have hBridge :
      moduleComplexDualCoevaluation M ▷ M ≫
          (α_ _ _ _).hom ≫
          M ◁ moduleComplexDualEvaluation M ≫
          (ρ_ M).hom =
        moduleComplexDualCoevaluation M ▷ M ≫
          moduleComplexDualTensorToEnd M ▷ M ≫
          (β_ ((ihom M).obj M) M).hom ≫
          (ihom.ev M).app M := by
    -- Whisker the explicit evaluation/comparison bridge by the coevaluation prefix.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ moduleComplexDualCoevaluation M ▷ M ≫ k)
        (moduleComplexDual_explicitEvaluation_comp_rightUnitor (M := M) (K := M))
  have hMain :
      moduleComplexDualCoevaluation M ▷ M ≫
          (α_ _ _ _).hom ≫
          M ◁ moduleComplexDualEvaluation M ≫
          (ρ_ M).hom =
        (λ_ M).hom := by
    exact hBridge.trans hEval
  simpa [Category.assoc] using hMain.trans (by simp [Category.assoc])

omit M

/-- Helper for Lemma 15.73.2: the first triangle identity for the canonical internal-Hom dual,
written with the explicit target object `(ihom K).obj (𝟙_ CpxR)`. -/
private theorem moduleComplexDual_coevaluation_evaluation_explicit
    {K : CochainComplex (ModuleCat R) ℤ}
    [IsIso (moduleComplexDualTensorToEnd K)] :
    ((ihom K).obj (𝟙_ CpxR)) ◁ moduleComplexDualCoevaluation K ≫
        (α_ ((ihom K).obj (𝟙_ CpxR)) K ((ihom K).obj (𝟙_ CpxR))).inv ≫
        moduleComplexDualEvaluation K ▷ ((ihom K).obj (𝟙_ CpxR)) =
      (ρ_ ((ihom K).obj (𝟙_ CpxR))).hom ≫
        (λ_ ((ihom K).obj (𝟙_ CpxR))).inv := by
  -- This is the same triangle identity, with the dual object written out explicitly.
  simpa [moduleComplexDual] using
    (moduleComplexDual_coevaluation_evaluation (M := K))

/-- Helper for Lemma 15.73.2: the second triangle identity for the canonical internal-Hom dual,
written with the explicit target object `(ihom K).obj (𝟙_ CpxR)`. -/
private theorem moduleComplexDual_evaluation_coevaluation_explicit
    {K : CochainComplex (ModuleCat R) ℤ}
    [IsIso (moduleComplexDualTensorToEnd K)] :
    moduleComplexDualCoevaluation K ▷ K ≫
        (α_ K ((ihom K).obj (𝟙_ CpxR)) K).hom ≫
        K ◁ moduleComplexDualEvaluation K =
      (λ_ K).hom ≫ (ρ_ K).inv := by
  -- This is the same triangle identity, with the dual object written out explicitly.
  simpa [moduleComplexDual] using
    (moduleComplexDual_evaluation_coevaluation (M := K))

include M

/-- Helper for Lemma 15.73.2: if `N` is a chosen left dual of `A`, then tensoring by `N` on the
right computes the ordinary linear-Hom module `Hom_R(A, B)`. -/
private noncomputable abbrev leftDualTensorToLinearHom
    {A B N : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup N] [Module R N]
    [ExactPairing (ModuleCat.of R N) (ModuleCat.of R A)] :
    (ModuleCat.of R B ⊗ ModuleCat.of R N) ⟶ ModuleCat.of R (A →ₗ[R] B) :=
  (β_ (ModuleCat.of R B) (ModuleCat.of R N)).hom ≫
    ((Adjunction.rightAdjointUniq
        (tensorLeftAdjunction (ModuleCat.of R N) (ModuleCat.of R A))
        (ihom.adjunction (ModuleCat.of R A))).app (ModuleCat.of R B)).hom ≫
      (ModuleCat.homLinearEquiv :
        ((ModuleCat.of R A) ⟶ ModuleCat.of R B) ≃ₗ[R] (A →ₗ[R] B)).toModuleIso.hom

/-- Helper for Lemma 15.73.2: once a module `A` is equipped with a chosen left dual `N`, the
comparison `B ⊗ N ⟶ Hom_R(A, B)` is an isomorphism. -/
private theorem leftDualTensorToLinearHom_isIso
    {A B N : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup N] [Module R N]
    [ExactPairing (ModuleCat.of R N) (ModuleCat.of R A)] :
    IsIso (leftDualTensorToLinearHom (R := R) (A := A) (B := B) (N := N)) := by
  -- Route correction: isolate the owner theorem for a chosen degreewise left dual before trying
  -- to specialize it to the canonical module dual coming from finite projectivity.
  let e : tensorLeft (ModuleCat.of R N) ≅ ihom (ModuleCat.of R A) :=
    Adjunction.rightAdjointUniq
      (tensorLeftAdjunction (ModuleCat.of R N) (ModuleCat.of R A))
      (ihom.adjunction (ModuleCat.of R A))
  -- The comparison is a composite of the braiding, the right-adjoint uniqueness isomorphism, and
  -- the standard identification of internal Hom with linear maps in `ModuleCat`.
  let _ : IsIso ((β_ (ModuleCat.of R B) (ModuleCat.of R N)).hom) := by
    infer_instance
  let _ : IsIso (e.app (ModuleCat.of R B)).hom := by
    infer_instance
  let _ :
      IsIso
        ((ModuleCat.homLinearEquiv :
            ((ModuleCat.of R A) ⟶ ModuleCat.of R B) ≃ₗ[R] (A →ₗ[R] B)).toModuleIso.hom) := by
    infer_instance
  simpa [leftDualTensorToLinearHom, e] using
    (inferInstance :
      IsIso
        ((β_ (ModuleCat.of R B) (ModuleCat.of R N)).hom ≫
          (e.app (ModuleCat.of R B)).hom ≫
          (ModuleCat.homLinearEquiv :
            ((ModuleCat.of R A) ⟶ ModuleCat.of R B) ≃ₗ[R] (A →ₗ[R] B)).toModuleIso.hom))

/-- Helper for Lemma 15.73.2: the canonical contraction map
`B ⊗ Hom_R(A, R) → Hom_R(A, B)` used in the converse construction. -/
private noncomputable def moduleDualTensorToLinearMap
    {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] :
    TensorProduct R B (Module.Dual R A) →ₗ[R] (A →ₗ[R] B) :=
  TensorProduct.lift
    (LinearMap.flip (LinearMap.smulRightₗ (R := R) (M := B) (M₂ := A)))

/-- Helper for Lemma 15.73.2: the categorical form of the canonical contraction map
`B ⊗ Hom_R(A, R) → Hom_R(A, B)`. -/
private noncomputable abbrev moduleDualTensorToLinearHom
    {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] :
    (ModuleCat.of R B ⊗ ModuleCat.of R (Module.Dual R A)) ⟶ ModuleCat.of R (A →ₗ[R] B) :=
  ModuleCat.ofHom (moduleDualTensorToLinearMap (R := R) (A := A) (B := B))

/-- Helper for Lemma 15.73.2: the direct module-dual contraction map sends a pure tensor
`b ⊗ φ` to the linear map `a ↦ φ(a) • b`. -/
private theorem moduleDualTensorToLinearMap_tmul_apply
    {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (b : B) (φ : Module.Dual R A) (a : A) :
    moduleDualTensorToLinearMap (R := R) (A := A) (B := B) (TensorProduct.tmul R b φ) a =
      φ a • b := by
  -- Expand the tensor-lifted definition once; the remaining evaluation is exactly `smulRight`.
  simp [moduleDualTensorToLinearMap]

/-- Helper for Lemma 15.73.2: the direct contraction map is natural under precomposition on the
dualized argument. -/
private theorem moduleDualTensorToLinearMap_natural
    {A F B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup F] [Module R F]
    [AddCommGroup B] [Module R B] (u : F →ₗ[R] A) :
    moduleDualTensorToLinearMap (R := R) (A := F) (B := B) ∘ₗ
        TensorProduct.map (LinearMap.id : B →ₗ[R] B) (LinearMap.dualMap u) =
      LinearMap.lcomp R B u ∘ₗ moduleDualTensorToLinearMap (R := R) (A := A) (B := B) := by
  -- Compare the two composites on pure tensors; both evaluate to `a ↦ φ (u a) • b`.
  apply TensorProduct.ext'
  intro b φ
  ext x
  simp [moduleDualTensorToLinearMap_tmul_apply, LinearMap.lcomp_apply, LinearMap.dualMap_apply]

/-- Helper for Lemma 15.73.2: the free finite inverse formula for
`moduleDualTensorToLinearMap` is additive in the input linear map. -/
private theorem moduleDualTensorToLinearMap_finInv_map_add
    {B : Type u} [AddCommGroup B] [Module R B] (n : ℕ)
    (f g : (Fin n → R) →ₗ[R] B) :
    (∑ i, TensorProduct.tmul R ((f + g) (Pi.basisFun R (Fin n) i)) (LinearMap.proj i)) =
      (∑ i, TensorProduct.tmul R (f (Pi.basisFun R (Fin n) i)) (LinearMap.proj i)) +
        ∑ i, TensorProduct.tmul R (g (Pi.basisFun R (Fin n) i)) (LinearMap.proj i) := by
  -- The inverse formula is a finite sum, so additivity is termwise.
  simp [Finset.sum_add_distrib, TensorProduct.tmul_add]

/-- Helper for Lemma 15.73.2: the free finite inverse formula for
`moduleDualTensorToLinearMap` is `R`-linear in the input linear map. -/
private theorem moduleDualTensorToLinearMap_finInv_map_smul
    {B : Type u} [AddCommGroup B] [Module R B] (n : ℕ) (a : R)
    (f : (Fin n → R) →ₗ[R] B) :
    (∑ i, TensorProduct.tmul R ((a • f) (Pi.basisFun R (Fin n) i)) (LinearMap.proj i)) =
      a • ∑ i, TensorProduct.tmul R (f (Pi.basisFun R (Fin n) i)) (LinearMap.proj i) := by
  -- Scalar multiplication also passes through the finite sum termwise.
  simp [Finset.smul_sum, TensorProduct.smul_tmul']

/-- Helper for Lemma 15.73.2: on a finite free module `R^n`, the inverse to the direct
contraction map is obtained by summing over the standard basis and coordinate functionals. -/
private noncomputable def moduleDualTensorToLinearMapFinInv
    {B : Type u} [AddCommGroup B] [Module R B] (n : ℕ) :
    ((Fin n → R) →ₗ[R] B) →ₗ[R] TensorProduct R B (Module.Dual R (Fin n → R)) :=
  { toFun := fun f ↦
      ∑ i, TensorProduct.tmul R (f (Pi.basisFun R (Fin n) i)) (LinearMap.proj i)
    map_add' := moduleDualTensorToLinearMap_finInv_map_add (R := R) (B := B) n
    map_smul' := moduleDualTensorToLinearMap_finInv_map_smul (R := R) (B := B) n }

/-- Helper for Lemma 15.73.2: every functional on the finite free module `R^n` is the sum of its
coordinates against the standard dual basis. -/
private theorem moduleDualTensorToLinearMap_fin_dual_expansion
    (n : ℕ) (φ : Module.Dual R (Fin n → R)) :
    (∑ i, φ (Pi.basisFun R (Fin n) i) • LinearMap.proj i) = φ := by
  -- Expand a vector in the standard basis of `R^n` and evaluate `φ` termwise.
  ext x
  calc
    (∑ i, φ (Pi.basisFun R (Fin n) i) • LinearMap.proj i) x =
        ∑ i, φ (Pi.basisFun R (Fin n) i) * x i := by
          simp [LinearMap.proj_apply, smul_eq_mul]
    _ = φ (∑ i, x i • Pi.basisFun R (Fin n) i) := by
          rw [map_sum]
          congr with i
          simp [Pi.basisFun]
    _ = φ x := by
          simpa [Pi.basisFun_repr] using congrArg φ ((Pi.basisFun R (Fin n)).sum_repr x)

/-- Helper for Lemma 15.73.2: the explicit finite free inverse reconstructs a linear map from its
values on the standard basis. -/
private theorem moduleDualTensorToLinearMap_fin_right_inverse
    {B : Type u} [AddCommGroup B] [Module R B] (n : ℕ)
    (f : (Fin n → R) →ₗ[R] B) :
    moduleDualTensorToLinearMap (R := R) (A := Fin n → R) (B := B)
        (moduleDualTensorToLinearMapFinInv (R := R) (B := B) n f) =
      f := by
  -- Evaluate on a basis expansion of the input vector in `R^n`.
  ext x
  calc
    moduleDualTensorToLinearMap (R := R) (A := Fin n → R) (B := B)
        (moduleDualTensorToLinearMapFinInv (R := R) (B := B) n f) x =
      ∑ i, x i • f (Pi.basisFun R (Fin n) i) := by
        simp [moduleDualTensorToLinearMapFinInv, moduleDualTensorToLinearMap_tmul_apply]
    _ = f (∑ i, x i • Pi.basisFun R (Fin n) i) := by
        rw [map_sum]
        congr with i
        simp
    _ = f x := by
        simp [Pi.basisFun_repr]

/-- Helper for Lemma 15.73.2: the explicit finite free inverse also recovers a pure tensor
`b ⊗ φ`. -/
private theorem moduleDualTensorToLinearMap_fin_left_inverse
    {B : Type u} [AddCommGroup B] [Module R B] (n : ℕ) :
    moduleDualTensorToLinearMapFinInv (R := R) (B := B) n ∘ₗ
        moduleDualTensorToLinearMap (R := R) (A := Fin n → R) (B := B) =
      LinearMap.id := by
  -- Reduce to pure tensors, then use the standard dual-basis expansion of `φ`.
  apply TensorProduct.ext'
  intro b φ
  calc
    moduleDualTensorToLinearMapFinInv (R := R) (B := B) n
        (moduleDualTensorToLinearMap (R := R) (A := Fin n → R) (B := B)
          (TensorProduct.tmul R b φ)) =
      ∑ i, TensorProduct.tmul R (φ (Pi.basisFun R (Fin n) i) • b) (LinearMap.proj i) := by
        simp [moduleDualTensorToLinearMapFinInv, moduleDualTensorToLinearMap_tmul_apply]
    _ = ∑ i, TensorProduct.tmul R b (φ (Pi.basisFun R (Fin n) i) • LinearMap.proj i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp [TensorProduct.tmul_smul]
    _ = TensorProduct.tmul R b (∑ i, φ (Pi.basisFun R (Fin n) i) • LinearMap.proj i) := by
        simp [TensorProduct.tmul_sum]
    _ = TensorProduct.tmul R b φ := by
        rw [moduleDualTensorToLinearMap_fin_dual_expansion (R := R) n φ]
    _ = LinearMap.id (TensorProduct.tmul R b φ) := by
        rfl

/-- Helper for Lemma 15.73.2: the direct contraction map is an isomorphism on the finite free
module `R^n`. -/
private theorem moduleDualTensorToLinearHom_fin_isIso
    {B : Type u} [AddCommGroup B] [Module R B] (n : ℕ) :
    IsIso (moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B)) := by
  -- The inverse is the explicit dual-basis formula proved above.
  refine ⟨⟨ModuleCat.ofHom (moduleDualTensorToLinearMapFinInv (R := R) (B := B) n), ?_, ?_⟩⟩
  · ext z
    change
      moduleDualTensorToLinearMapFinInv (R := R) (B := B) n
          (moduleDualTensorToLinearMap (R := R) (A := Fin n → R) (B := B) z) =
        z
    simpa using congrArg (fun f ↦ f z)
      (moduleDualTensorToLinearMap_fin_left_inverse (R := R) (B := B) n)
  · ext f x
    change
      moduleDualTensorToLinearMap (R := R) (A := Fin n → R) (B := B)
          (moduleDualTensorToLinearMapFinInv (R := R) (B := B) n f) x =
        f x
    simpa using congrArg (fun g : (Fin n → R) →ₗ[R] B ↦ g x)
      (moduleDualTensorToLinearMap_fin_right_inverse (R := R) (B := B) n f)

/-- Helper for Lemma 15.73.2: the direct contraction map is an isomorphism for finite projective
modules, obtained by descending the finite free case along a split finite free cover. -/
private theorem moduleDualTensorToLinearHom_isIso_of_finite_projective
    {A B : Type u} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] :
    IsIso (moduleDualTensorToLinearHom (R := R) (A := A) (B := B)) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R A
  let πCat : ModuleCat.of R (Fin n → R) ⟶ ModuleCat.of R A := ModuleCat.ofHom π
  letI : Epi πCat := (ModuleCat.epi_iff_surjective _).2 hπ
  letI : Projective (ModuleCat.of R A) := by infer_instance
  let σCat : ModuleCat.of R A ⟶ ModuleCat.of R (Fin n → R) :=
    Projective.factorThru (𝟙 (ModuleCat.of R A)) πCat
  have hsplit : σCat ≫ πCat = 𝟙 (ModuleCat.of R A) := by
    exact Projective.factorThru_comp (𝟙 (ModuleCat.of R A)) πCat
  let σ : A →ₗ[R] (Fin n → R) := ModuleCat.Hom.hom σCat
  have hsplit_linear : π.comp σ = LinearMap.id := by
    ext a
    simpa [σ] using congrArg (fun f : ModuleCat.of R A ⟶ ModuleCat.of R A ↦ f a) hsplit
  let α :
      ModuleCat.of R B ⊗ ModuleCat.of R (Module.Dual R A) ⟶
        ModuleCat.of R B ⊗ ModuleCat.of R (Module.Dual R (Fin n → R)) :=
    (𝟙 (ModuleCat.of R B)) ⊗ₘ ModuleCat.ofHom (LinearMap.dualMap π)
  let rα :
      ModuleCat.of R B ⊗ ModuleCat.of R (Module.Dual R (Fin n → R)) ⟶
        ModuleCat.of R B ⊗ ModuleCat.of R (Module.Dual R A) :=
    (𝟙 (ModuleCat.of R B)) ⊗ₘ ModuleCat.ofHom (LinearMap.dualMap σ)
  let β : ModuleCat.of R (A →ₗ[R] B) ⟶ ModuleCat.of R ((Fin n → R) →ₗ[R] B) :=
    ModuleCat.ofHom (LinearMap.lcomp R B π)
  let rβ : ModuleCat.of R ((Fin n → R) →ₗ[R] B) ⟶ ModuleCat.of R (A →ₗ[R] B) :=
    ModuleCat.ofHom (LinearMap.lcomp R B σ)
  have hα : α ≫ rα = 𝟙 _ := by
    -- The tensor-side comparison is a retract because `π ∘ σ = id_A`.
    apply TensorProduct.ext'
    intro b φ
    apply congrArg (TensorProduct.tmul R b)
    ext a
    simp [α, rα, LinearMap.dualMap_apply]
    exact congrArg (fun f : A →ₗ[R] A => f a) hsplit_linear
  have hβ : β ≫ rβ = 𝟙 _ := by
    -- Precomposition by `π` is split by precomposition by `σ`.
    ext f a
    change f (π (σ a)) = f a
    simpa using congrArg (fun g : A →ₗ[R] A => f (g a)) hsplit_linear
  have hπ_nat :
      α ≫ moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B) =
        moduleDualTensorToLinearHom (R := R) (A := A) (B := B) ≫ β := by
    -- This is the categorical form of the linear naturality square for `π`.
    ext b φ a
    simpa [α, β, moduleDualTensorToLinearHom, Category.assoc] using
      congrArg (fun f :
        TensorProduct R B (Module.Dual R A) →ₗ[R] ((Fin n → R) →ₗ[R] B) ↦
          f (TensorProduct.tmul R b φ) a)
        (moduleDualTensorToLinearMap_natural (R := R) (A := A) (F := Fin n → R) (B := B) π)
  have hσ_nat :
      rα ≫ moduleDualTensorToLinearHom (R := R) (A := A) (B := B) =
        moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B) ≫ rβ := by
    -- The same naturality square, now for the section `σ`.
    ext b φ a
    simpa [rα, rβ, moduleDualTensorToLinearHom, Category.assoc] using
      congrArg (fun f :
        TensorProduct R B (Module.Dual R (Fin n → R)) →ₗ[R] (A →ₗ[R] B) ↦
          f (TensorProduct.tmul R b φ) a)
        (moduleDualTensorToLinearMap_natural (R := R) (A := Fin n → R) (F := A) (B := B) σ)
  letI :
      IsIso (moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B)) :=
    moduleDualTensorToLinearHom_fin_isIso (R := R) (B := B) n
  refine ⟨⟨β ≫ inv (moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B)) ≫ rα, ?_, ?_⟩⟩
  · -- Transport the free finite inverse across the split retract square.
    calc
      moduleDualTensorToLinearHom (R := R) (A := A) (B := B) ≫
          (β ≫ inv (moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B)) ≫ rα) =
        α ≫ moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B) ≫
          inv (moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B)) ≫ rα := by
            rw [Category.assoc, hπ_nat]
      _ = α ≫ rα := by simp [Category.assoc]
      _ = 𝟙 _ := hα
  · -- The reverse composite uses the section-side naturality square and the same retract data.
    calc
      (β ≫ inv (moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B)) ≫ rα) ≫
          moduleDualTensorToLinearHom (R := R) (A := A) (B := B) =
        β ≫ inv (moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B)) ≫
          moduleDualTensorToLinearHom (R := R) (A := Fin n → R) (B := B) ≫ rβ := by
            rw [Category.assoc, Category.assoc, hσ_nat]
      _ = β ≫ rβ := by simp [Category.assoc]
      _ = 𝟙 _ := hβ

/-- Helper for Lemma 15.73.2: boundedness and termwise finite projectivity force the canonical
tensor-to-endomorphism comparison for the internal-Hom dual complex to be an isomorphism. -/
private theorem moduleComplexDualTensorToEnd_degreewise_isIso
    {M : CochainComplex (ModuleCat R) ℤ}
    (hbounded : BoundedCpx M)
    (hfinite_projective : ∀ n : ℤ, Module.Finite R (M.X n) ∧ Module.Projective R (M.X n))
    (n : ℤ) :
    IsIso ((moduleComplexDualTensorToEnd M).f n) := by
  -- Route correction: the attempted shortcut via an inferable
  -- `ExactPairing (ModuleCat.of R (Module.Dual R A)) (ModuleCat.of R A)` is unavailable in this
  -- toolchain, so the converse must use the direct contraction map
  -- `moduleDualTensorToLinearHom` instead.
  -- TODO: the module-level finite-projective block is now available via
  -- `moduleDualTensorToLinearHom_isIso_of_finite_projective`. The remaining blocker is purely the
  -- complex-level transport: conjugate `((moduleComplexDualTensorToEnd M).f n)` by the tensor
  -- direct-sum model and the internal-Hom product model, identify the surviving `(n + p, -p)`
  -- coordinate with `moduleDualTensorToLinearHom (A := M.X p) (B := M.X (n + p))`, and then
  -- assemble those finitely many block isomorphisms using boundedness of `M`.
  sorry

/-- Helper for Lemma 15.73.2: boundedness and termwise finite projectivity force the canonical
tensor-to-endomorphism comparison for the internal-Hom dual complex to be an isomorphism. -/
private theorem moduleComplexDualTensorToEnd_isIso_of_bounded_termwise_finite_projective
    {M : CochainComplex (ModuleCat R) ℤ}
    (hbounded : BoundedCpx M)
    (hfinite_projective : ∀ n : ℤ, Module.Finite R (M.X n) ∧ Module.Projective R (M.X n)) :
    IsIso (moduleComplexDualTensorToEnd M) := by
  -- Reduce the global isomorphism to the degreewise components furnished by the finite-projective
  -- comparison on each summand.
  letI : ∀ n : ℤ, IsIso ((moduleComplexDualTensorToEnd M).f n) :=
    fun n ↦ moduleComplexDualTensorToEnd_degreewise_isIso
      (M := M) hbounded hfinite_projective n
  exact HomologicalComplex.Hom.isIso_of_components (moduleComplexDualTensorToEnd M)

@[reducible] private noncomputable def moduleComplexDualExactPairingOfIsIso
    (M : CochainComplex (ModuleCat R) ℤ)
    [IsIso (moduleComplexDualTensorToEnd M)] :
    ExactPairing ((ihom M).obj (𝟙_ CpxR)) M :=
  letI : ExactPairing M ((ihom M).obj (𝟙_ CpxR)) :=
    { coevaluation' := moduleComplexDualCoevaluation M
      evaluation' := moduleComplexDualEvaluation M
      coevaluation_evaluation' := moduleComplexDual_coevaluation_evaluation_explicit (K := M)
      evaluation_coevaluation' := moduleComplexDual_evaluation_coevaluation_explicit (K := M) }
  BraidedCategory.exactPairing_swap M ((ihom M).obj (𝟙_ CpxR))

-- Proof sketch: define the coevaluation by transporting the identity of `M^•` across the
-- canonical comparison `M^• ⊗ (M^•)^∨ ⟶ Hom^•(M^•, M^•)`, use the evaluation map from `ihom.ev`,
-- and then verify the triangle identities by the signed-transpose description of the dual
-- differential.
/-- Lemma 15.73.2 (7): conversely, if `M^•` is bounded and each `M^n` is a finite projective
`R`-module, then the dual complex `M^∨ = \operatorname{Hom}^\bullet_R(M^\bullet, R[0])` is a left
dual of `M^•`. -/
@[reducible]
noncomputable def moduleComplexDualExactPairing
    (hbounded : BoundedCpx M)
    (hfinite_projective : ∀ n : ℤ, Module.Finite R (M.X n) ∧ Module.Projective R (M.X n)) :
    ExactPairing M^∨ M :=
  letI : IsIso (moduleComplexDualTensorToEnd M) :=
    moduleComplexDualTensorToEnd_isIso_of_bounded_termwise_finite_projective
      (M := M) hbounded hfinite_projective
  show ExactPairing ((ihom M).obj (𝟙_ CpxR)) M from
    moduleComplexDualExactPairingOfIsIso M

end ClosedDuality

/-- Helper for Lemma 15.73.2: rewriting the degreewise complex pairing at `-n` produces a left
dual pairing between `M^{-n}` and `N^n`. -/
private noncomputable abbrev exactPairing_degreewise_left_dual_neg (n : ℤ) :
    ExactPairing (ModuleCat.of R (M.X (-n))) (ModuleCat.of R (N.X n)) := by
  -- The diagonal pairing for `-n` already has the required target once the index is simplified.
  simpa [neg_neg] using
    (exactPairing_degreewise_left_dual_aux (M := M) (N := N) (-n) :
      ExactPairing (ModuleCat.of R (M.X (-n))) (ModuleCat.of R (N.X (-(-n)))))

-- Proof sketch: specialize Lemma `15.73.1` to the degreewise exact pairing from clause `(5)`,
-- with index `-n`, to identify `N^n` with `Hom_R(M^{-n}, R)`.
/-- The degreewise identification used in Lemma `15.73.2 (6)`: under an exact pairing
`M^• ⊣ N^•`, the term `N^n` is canonically isomorphic to `Hom_R(M^{-n}, R)`. -/
noncomputable abbrev exactPairing_rightTermIso_moduleDual
    (M N : CpxR) [ExactPairing M N] (n : ℤ) :
    ModuleCat.of R (N.X n) ≅ ModuleCat.of R (Module.Dual R (M.X (-n))) :=
  letI : ExactPairing (ModuleCat.of R (M.X (-n))) (ModuleCat.of R (N.X n)) :=
    exactPairing_degreewise_left_dual_neg (M := M) (N := N) n
  letI : ExactPairing (ModuleCat.of R (N.X n)) (ModuleCat.of R (M.X (-n))) :=
    BraidedCategory.exactPairing_swap _ _
  asIso ExactPairing.toModuleDual

/-- Helper for Lemma 15.73.2: evaluating the degreewise identification
`N^n ≅ Hom_R(M^{-n}, R)` on `ψ` and `m` is exactly the extracted degreewise evaluation pairing. -/
private theorem exactPairing_rightTermIso_moduleDual_hom_apply
    (n : ℤ) (ψ : N.X n) (m : M.X (-n)) :
    (exactPairing_rightTermIso_moduleDual M N n).hom ψ m =
      ModuleCat.Hom.hom (exactPairing_degreewise_evaluation (M := M) (N := N) (-n))
        (TensorProduct.tmul R ψ m) := by
  letI : ExactPairing (ModuleCat.of R (M.X (-n))) (ModuleCat.of R (N.X n)) :=
    exactPairing_degreewise_left_dual_neg (M := M) (N := N) n
  letI : ExactPairing (ModuleCat.of R (N.X n)) (ModuleCat.of R (M.X (-n))) :=
    BraidedCategory.exactPairing_swap _ _
  -- The degreewise isomorphism is `toModuleDual` for the swapped pairing, so its evaluation is
  -- the swapped degreewise evaluation, i.e. the original evaluation after the braiding.
  simpa [exactPairing_rightTermIso_moduleDual, exactPairing_degreewise_left_dual_neg,
    exactPairing_degreewise_left_dual_aux, exactPairing_degreewise_evaluation] using
    (ExactPairing.toModuleDual_apply (R := R) (M := M.X (-n)) (N := N.X n) ψ m)

/-- Helper for Lemma 15.73.2: the inverse of the degreewise duality isomorphism is the textbook
coevaluation element `e(φ) = (φ ⊗ 1)(η_{-n})`. -/
private theorem exactPairing_rightTermIso_moduleDual_inv_apply
    (n : ℤ) (φ : Module.Dual R (M.X (-n))) :
    (exactPairing_rightTermIso_moduleDual M N n).inv φ =
      ModuleCat.Hom.hom
        (exactPairing_degreewise_coevaluation (M := M) (N := N) (-n) ≫
          ((ModuleCat.ofHom φ) ⊗ₘ 𝟙 (N.X n : ModuleCat R)) ≫
          (λ_ (N.X n : ModuleCat R)).hom) 1 := by
  -- Route correction: prove the textbook inverse formula by applying the degreewise duality
  -- isomorphism to the coevaluation element and then using the degreewise triangle identity.
  apply (exactPairing_rightTermIso_moduleDual M N n).hom.injective
  ext m
  have hleft :
      (exactPairing_rightTermIso_moduleDual M N n).hom
          ((exactPairing_rightTermIso_moduleDual M N n).inv φ) m =
        φ m := by
    simpa using congrArg (fun ψ : Module.Dual R (M.X (-n)) ↦ ψ m)
      ((exactPairing_rightTermIso_moduleDual M N n).hom_inv_id_apply φ)
  have hright :
      (exactPairing_rightTermIso_moduleDual M N n).hom
          (ModuleCat.Hom.hom
            (exactPairing_degreewise_coevaluation (M := M) (N := N) (-n) ≫
              ((ModuleCat.ofHom φ) ⊗ₘ 𝟙 (N.X n : ModuleCat R)) ≫
              (λ_ (N.X n : ModuleCat R)).hom) 1) m =
        φ m := by
    -- Evaluate the textbook element through the extracted degreewise pairing and simplify the
    -- result with the degreewise triangle identity.
    rw [exactPairing_rightTermIso_moduleDual_hom_apply]
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          ModuleCat.Hom.hom k (TensorProduct.tmul R (1 : R) m))
        (exactPairing_degreewise_evaluation_coevaluation_projection (M := M) (N := N) (-n))
  exact hleft.trans hright.symm

/-- Helper for Lemma 15.73.2: evaluating the differential square on `φ` and
`m ∈ M^{-n-1}` gives the scalar identity coming from the projected coevaluation chain relation. -/
private theorem exactPairing_rightTermIso_moduleDual_d_apply
    (n : ℤ) (φ : Module.Dual R (M.X (-n))) (m : M.X (-(n + 1))) :
    (exactPairing_rightTermIso_moduleDual M N (n + 1)).hom
        (N.d n (n + 1)
          ((exactPairing_rightTermIso_moduleDual M N n).inv φ)) m =
      -(-n).negOnePow * φ (M.d (-(n + 1)) (-n) m) := by
  let eφ : N.X n := (exactPairing_rightTermIso_moduleDual M N n).inv φ
  have hchain :=
    exactPairing_coevaluation_chain_relation_neg_degree (M := M) (N := N) n
  have hpost :
      ModuleCat.Hom.hom
          (exactPairing_degreewise_coevaluation (M := M) (N := N) (-(n + 1)) ≫
              (M.d (-(n + 1)) (-n) ⊗ₘ 𝟙 (N.X (n + 1))) ≫
              ((ModuleCat.ofHom φ) ⊗ₘ 𝟙 (N.X (n + 1) : ModuleCat R)) ≫
              (λ_ (N.X (n + 1) : ModuleCat R)).hom) 1 +
        (-n).negOnePow *
          ModuleCat.Hom.hom
            (exactPairing_degreewise_coevaluation (M := M) (N := N) (-n) ≫
                (𝟙 (M.X (-n) : ModuleCat R) ⊗ₘ N.d n (n + 1)) ≫
                ((ModuleCat.ofHom φ) ⊗ₘ 𝟙 (N.X (n + 1) : ModuleCat R)) ≫
                (λ_ (N.X (n + 1) : ModuleCat R)).hom) 1 =
        0 := by
    -- Postcompose the projected chain relation with `φ ⊗ 1`, then identify maps out of the unit
    -- with the resulting degreewise elements.
    simpa [Category.assoc, Preadditive.comp_add, Preadditive.comp_smul, map_add, map_smul] using
      congrArg
        (fun k ↦
          ModuleCat.Hom.hom
            (k ≫ ((ModuleCat.ofHom φ) ⊗ₘ 𝟙 (N.X (n + 1) : ModuleCat R)) ≫
              (λ_ (N.X (n + 1) : ModuleCat R)).hom) 1)
        hchain
  have hfirst :
      ModuleCat.Hom.hom
          (exactPairing_degreewise_coevaluation (M := M) (N := N) (-(n + 1)) ≫
              (M.d (-(n + 1)) (-n) ⊗ₘ 𝟙 (N.X (n + 1))) ≫
              ((ModuleCat.ofHom φ) ⊗ₘ 𝟙 (N.X (n + 1) : ModuleCat R)) ≫
              (λ_ (N.X (n + 1) : ModuleCat R)).hom) 1 =
        (exactPairing_rightTermIso_moduleDual M N (n + 1)).inv
          ((LinearMap.dualMap (ModuleCat.Hom.hom (M.d (-(n + 1)) (-n)))) φ) := by
    -- The first summand is the textbook coevaluation element for the composite functional
    -- `φ ∘ d_M`.
    simpa [LinearMap.dualMap_apply, Category.assoc] using
      (exactPairing_rightTermIso_moduleDual_inv_apply (M := M) (N := N) (n := n + 1)
        ((LinearMap.dualMap (ModuleCat.Hom.hom (M.d (-(n + 1)) (-n)))) φ))
  have hsecond :
      ModuleCat.Hom.hom
          (exactPairing_degreewise_coevaluation (M := M) (N := N) (-n) ≫
              (𝟙 (M.X (-n) : ModuleCat R) ⊗ₘ N.d n (n + 1)) ≫
              ((ModuleCat.ofHom φ) ⊗ₘ 𝟙 (N.X (n + 1) : ModuleCat R)) ≫
              (λ_ (N.X (n + 1) : ModuleCat R)).hom) 1 =
        N.d n (n + 1) eφ := by
    -- Rewrite the second summand by first identifying the textbook coevaluation element with
    -- `eφ`, then append the differential.
    rw [← exactPairing_rightTermIso_moduleDual_inv_apply (M := M) (N := N) (n := n) φ]
    simp [eφ, Category.assoc]
  have hchain' :
      (exactPairing_rightTermIso_moduleDual M N (n + 1)).inv
          ((LinearMap.dualMap (ModuleCat.Hom.hom (M.d (-(n + 1)) (-n)))) φ) +
        (-n).negOnePow • (N.d n (n + 1) eφ) =
      0 := by
    simpa [hfirst, hsecond, eφ, add_comm, add_left_comm, add_assoc] using hpost
  have hdual :
      (LinearMap.dualMap (ModuleCat.Hom.hom (M.d (-(n + 1)) (-n)))) φ m +
        (-n).negOnePow *
          (exactPairing_rightTermIso_moduleDual M N (n + 1)).hom
            (N.d n (n + 1) eφ) m =
      0 := by
    -- Apply the degreewise duality isomorphism to the element relation and then evaluate at `m`.
    have hhom :
        (exactPairing_rightTermIso_moduleDual M N (n + 1)).hom
            ((exactPairing_rightTermIso_moduleDual M N (n + 1)).inv
              ((LinearMap.dualMap (ModuleCat.Hom.hom (M.d (-(n + 1)) (-n)))) φ)) +
          (-n).negOnePow •
            (exactPairing_rightTermIso_moduleDual M N (n + 1)).hom
              (N.d n (n + 1) eφ) =
        0 := by
      simpa [map_add, map_smul] using
        congrArg
          (exactPairing_rightTermIso_moduleDual M N (n + 1)).hom
          hchain'
    simpa [LinearMap.dualMap_apply, eφ] using
      congrArg
        (fun ψ : Module.Dual R (M.X (-(n + 1))) ↦ ψ m)
        hhom
  linarith

/-- Helper for Lemma 15.73.2: on the `(p,q)` summand of the tensor totalization, the differential
splits into the horizontal differential plus `(-1)^p` times the vertical differential. -/
private theorem exactPairing_tensorObj_d_on_summand_eq
    (K L : CpxR) [HomologicalComplex.HasTensor K L] (p q : ℤ) :
    HomologicalComplex.ιTensorObj K L p q (p + q) (by simp) ≫
        (HomologicalComplex.tensorObj K L).d (p + q) (p + q + 1) =
      (K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
          HomologicalComplex.ιTensorObj K L (p + 1) q (p + q + 1) (by abel_nf) +
        p.negOnePow •
          ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
            HomologicalComplex.ιTensorObj K L p (q + 1) (p + q + 1) (by abel_nf)) := by
  -- Route correction: expand the total differential directly on the chosen summand instead of
  -- normalizing it indirectly through a larger transport calculation.
  change
    HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R)) (up ℤ) p q (p + q) (by simp) ≫
        (HomologicalComplex.mapBifunctor K L (curriedTensor (ModuleCat R)) (up ℤ)).d
          (p + q) (p + q + 1) =
      (K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
          HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R)) (up ℤ)
            (p + 1) q (p + q + 1)
            (by simpa using (show (p + 1) + q = p + q + 1 by abel_nf)) +
        p.negOnePow •
          ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
            HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R)) (up ℤ)
              p (q + 1) (p + q + 1)
              (by simpa using (show p + (q + 1) = p + q + 1 by abel_nf)))
  -- This is the owner Leibniz rule for the tensor differential, written on one fixed summand.
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    Category.assoc]
  simp only [Category.assoc]

/-- Helper for Lemma 15.73.2: projecting the tensor differential to the bidegree
`(-n, n + 1)` keeps exactly the two diagonal coevaluation contributions from degrees
`-(n + 1)` and `-n`. -/
private theorem exactPairing_tensor_d_successor_projection (n : ℤ) :
    (M ⊗ N : CpxR).d 0 1 ≫
        exactPairing_bidegree_projection (K := M) (L := N) (-n) (n + 1) =
      exactPairing_degreewise_projection (M := M) (N := N) (-(n + 1)) ≫
        (M.d (-(n + 1)) (-n) ⊗ₘ 𝟙 (N.X (n + 1))) +
      (-n).negOnePow •
        (exactPairing_degreewise_projection (M := M) (N := N) (-n) ≫
          (𝟙 (M.X (-n)) ⊗ₘ N.d n (n + 1))) := by
  -- Route correction: compare both morphisms on each degree-`0` tensor summand, so only the two
  -- source-faithful diagonal pairs from the coevaluation chain relation can survive.
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  by_cases hleft : p = -(n + 1) ∧ q = n + 1
  · rcases hleft with ⟨hp, hq⟩
    subst hp
    subst hq
    have hproj_vertical :
        HomologicalComplex.ιTensorObj M N (-(n + 1)) (n + 2) 1 (by simp) ≫
            exactPairing_bidegree_projection (K := M) (L := N) (-n) (n + 1) =
          0 := by
      -- The vertical successor term lands in the wrong bidegree, so the projection kills it.
      simpa using
        (exactPairing_bidegree_projection_off_diagonal
          (K := M) (L := N) (p := -n) (q := n + 1)
          (p' := -(n + 1)) (q' := n + 2) (h := by simp)
          (hdiag := Or.inl (by omega)))
    have hproj_right :
        HomologicalComplex.ιTensorObj M N (-(n + 1)) (n + 1) 0 (by simp) ≫
            exactPairing_degreewise_projection (M := M) (N := N) (-n) =
          0 := by
      -- The degreewise projection to `(-n,n)` also kills this off-diagonal source summand.
      simpa using
        (exactPairing_degreewise_projection_off_diagonal
          (K := M) (L := N) (n := -n) (p := -(n + 1)) (q := n + 1) (h := by simp)
          (hdiag := Or.inl (by omega)))
    -- Only the horizontal differential from degree `-(n + 1)` survives.
    rw [Category.assoc, exactPairing_tensorObj_d_on_summand_eq, Preadditive.add_comp,
      Preadditive.smul_comp, Category.assoc,
      exactPairing_bidegree_projection_diag (K := M) (L := N) (-n) (n + 1),
      hproj_vertical, smul_zero, add_zero, Preadditive.comp_add, Preadditive.comp_smul,
      Category.assoc, exactPairing_degreewise_projection_diag (K := M) (L := N) (-(n + 1)),
      hproj_right, zero_comp, smul_zero, add_zero, Category.id_comp]
  · by_cases hright : p = -n ∧ q = n
    · rcases hright with ⟨hp, hq⟩
      subst hp
      subst hq
      have hproj_horizontal :
          HomologicalComplex.ιTensorObj M N (-n + 1) n 1 (by simp) ≫
              exactPairing_bidegree_projection (K := M) (L := N) (-n) (n + 1) =
            0 := by
        -- The horizontal successor term misses the target bidegree, so the projection vanishes.
        simpa using
          (exactPairing_bidegree_projection_off_diagonal
            (K := M) (L := N) (p := -n) (q := n + 1)
            (p' := -n + 1) (q' := n) (h := by simp)
            (hdiag := Or.inl (by omega)))
      have hproj_left :
          HomologicalComplex.ιTensorObj M N (-n) n 0 (by simp) ≫
              exactPairing_degreewise_projection (M := M) (N := N) (-(n + 1)) =
            0 := by
        -- Projecting to `(-(n + 1), n + 1)` kills the other diagonal summand.
        simpa using
          (exactPairing_degreewise_projection_off_diagonal
            (K := M) (L := N) (n := -(n + 1)) (p := -n) (q := n) (h := by simp)
            (hdiag := Or.inl (by omega)))
      -- Only the vertical differential from degree `-n` survives.
      rw [Category.assoc, exactPairing_tensorObj_d_on_summand_eq, Preadditive.add_comp,
        Preadditive.smul_comp, Category.assoc, hproj_horizontal, zero_comp, zero_add,
        exactPairing_bidegree_projection_diag (K := M) (L := N) (-n) (n + 1),
        Preadditive.comp_add, Preadditive.comp_smul, Category.assoc, hproj_left,
        zero_comp, add_zero,
        exactPairing_degreewise_projection_diag (K := M) (L := N) (-n),
        Category.id_comp]
    · have hproj_horizontal :
          HomologicalComplex.ιTensorObj M N (p + 1) q 1 (by abel_nf) ≫
              exactPairing_bidegree_projection (K := M) (L := N) (-n) (n + 1) =
            0 := by
        have hdiag : p + 1 ≠ -n ∨ q ≠ n + 1 := by
          by_cases hp : p + 1 = -n
          · right
            intro hq
            apply hleft
            constructor
            · omega
            · exact hq
          · exact Or.inl hp
        -- Away from the `(-(n + 1), n + 1)` source pair, the projected horizontal term vanishes.
        simpa using
          (exactPairing_bidegree_projection_off_diagonal
            (K := M) (L := N) (p := -n) (q := n + 1)
            (p' := p + 1) (q' := q) (h := by abel_nf) (hdiag := hdiag))
      have hproj_vertical :
          HomologicalComplex.ιTensorObj M N p (q + 1) 1 (by abel_nf) ≫
              exactPairing_bidegree_projection (K := M) (L := N) (-n) (n + 1) =
            0 := by
        have hdiag : p ≠ -n ∨ q + 1 ≠ n + 1 := by
          by_cases hp : p = -n
          · right
            intro hq
            apply hright
            constructor
            · exact hp
            · omega
          · exact Or.inl hp
        -- Away from the `(-n,n)` source pair, the projected vertical term also vanishes.
        simpa using
          (exactPairing_bidegree_projection_off_diagonal
            (K := M) (L := N) (p := -n) (q := n + 1)
            (p' := p) (q' := q + 1) (h := by abel_nf) (hdiag := hdiag))
      have hproj_left :
          HomologicalComplex.ιTensorObj M N p q 0 h ≫
              exactPairing_degreewise_projection (M := M) (N := N) (-(n + 1)) =
            0 := by
        have hdiag : p ≠ -(n + 1) ∨ q ≠ n + 1 := by
          by_cases hp : p = -(n + 1)
          · right
            intro hq
            exact hleft ⟨hp, hq⟩
          · exact Or.inl hp
        -- The first degreewise projection only keeps the `(-(n + 1), n + 1)` diagonal summand.
        exact exactPairing_degreewise_projection_off_diagonal
          (K := M) (L := N) (n := -(n + 1)) (p := p) (q := q) (h := h) hdiag
      have hproj_right :
          HomologicalComplex.ιTensorObj M N p q 0 h ≫
              exactPairing_degreewise_projection (M := M) (N := N) (-n) =
            0 := by
        have hdiag : p ≠ -n ∨ q ≠ n := by
          by_cases hp : p = -n
          · right
            intro hq
            exact hright ⟨hp, hq⟩
          · exact Or.inl hp
        -- The second degreewise projection only keeps the `(-n,n)` diagonal summand.
        exact exactPairing_degreewise_projection_off_diagonal
          (K := M) (L := N) (n := -n) (p := p) (q := q) (h := h) hdiag
      -- Once both distinguished source pairs are excluded, every projected contribution vanishes.
      rw [Category.assoc, exactPairing_tensorObj_d_on_summand_eq, Preadditive.add_comp,
        Preadditive.smul_comp, Category.assoc, hproj_horizontal, hproj_vertical, zero_comp,
        zero_add, smul_zero, Preadditive.comp_add, Preadditive.comp_smul, Category.assoc,
        hproj_left, hproj_right, zero_comp, zero_add, smul_zero]

/-- Helper for Lemma 15.73.2: the tensor unit is concentrated in degree `0`, so its outgoing
degree-`0 → 1` differential vanishes after identifying degree `0` with the underlying module. -/
private theorem exactPairing_single₀_objXSelf_inv_comp_d_eq_zero :
    (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
        (𝟙_ CpxR).d 0 1 =
      0 := by
  -- The tensor unit is the degree-zero single cochain complex, so its first differential is zero.
  rw [HomologicalComplex.single_obj_d]
  simp [CochainComplex.single₀ObjXSelf]
  rfl

/-- Helper for Lemma 15.73.2: the degree `-n` component of the coevaluation chain-map equation
is exactly the two-term relation used to recover the signed transpose differential on the dual
complex. -/
private theorem exactPairing_coevaluation_chain_relation_neg_degree (n : ℤ) :
    exactPairing_degreewise_coevaluation (M := M) (N := N) (-(n + 1)) ≫
        (M.d (-(n + 1)) (-n) ⊗ₘ 𝟙 (N.X (n + 1))) +
      (-n).negOnePow •
        (exactPairing_degreewise_coevaluation (M := M) (N := N) (-n) ≫
          (𝟙 (M.X (-n)) ⊗ₘ N.d n (n + 1))) =
      0 := by
  let e := (inferInstance : ExactPairing M N).coevaluation'
  have hcomm :
      (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
          e.f 0 ≫
          (M ⊗ N : CpxR).d 0 1 =
        0 := by
    -- Compose the chain-map square with the degree-zero identification of the tensor unit.
    calc
      (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
          e.f 0 ≫
          (M ⊗ N : CpxR).d 0 1 =
        (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
          ((𝟙_ CpxR).d 0 1 ≫ e.f 1) := by
            simpa [e, Category.assoc] using
              congrArg
                (fun k ↦
                  (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫ k)
                (e.comm 0 1)
      _ =
        ((singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
            (𝟙_ CpxR).d 0 1) ≫
          e.f 1 := by
            simp [Category.assoc]
      _ = 0 := by
        simp [exactPairing_single₀_objXSelf_inv_comp_d_eq_zero, Category.assoc]
  have hprojected :
      (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
          e.f 0 ≫
          ((M ⊗ N : CpxR).d 0 1 ≫
            exactPairing_bidegree_projection (K := M) (L := N) (-n) (n + 1)) =
        0 := by
    -- Postcompose the chain-map relation with the chosen bidegree projection.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ exactPairing_bidegree_projection (K := M) (L := N) (-n) (n + 1))
        hcomm
  -- Rewrite the projected tensor differential by the previously isolated successor-projection
  -- formula, then recognize the two surviving diagonal terms as the degreewise coevaluations.
  calc
    exactPairing_degreewise_coevaluation (M := M) (N := N) (-(n + 1)) ≫
        (M.d (-(n + 1)) (-n) ⊗ₘ 𝟙 (N.X (n + 1))) +
      (-n).negOnePow •
        (exactPairing_degreewise_coevaluation (M := M) (N := N) (-n) ≫
          (𝟙 (M.X (-n)) ⊗ₘ N.d n (n + 1))) =
      (singleObjXSelf (up ℤ) (0 : ℤ) (𝟙_ (ModuleCat R))).inv ≫
          e.f 0 ≫
          ((M ⊗ N : CpxR).d 0 1 ≫
            exactPairing_bidegree_projection (K := M) (L := N) (-n) (n + 1)) := by
            rw [Category.assoc, exactPairing_tensor_d_successor_projection]
            simp [exactPairing_degreewise_coevaluation, Category.assoc,
              Preadditive.comp_add, Preadditive.comp_smul]
    _ = 0 := hprojected

-- Proof sketch: identify `N^n` and `N^{n+1}` with the degreewise dual modules using
-- `exactPairing_rightTermIso_moduleDual`; then the chain-map compatibility of the complex pairing
-- gives the textbook formula that `d_N^n` is the signed transpose of `d_M^{-n-1}`.
/-- Lemma 15.73.2 (6): under the degreewise identifications
`N^n ≅ Hom_R(M^{-n}, R)` and `N^{n + 1} ≅ Hom_R(M^{-n-1}, R)` coming from Lemma `15.73.1`, the
differential `d_N^n` is the signed transpose `-(-1)^n (d_M^{-n-1})ᵗ`. -/
theorem exactPairing_rightTermIso_moduleDual_d_comm (n : ℤ) :
    CommSq (N.d n (n + 1))
      (exactPairing_rightTermIso_moduleDual M N n).hom
      (exactPairing_rightTermIso_moduleDual M N (n + 1)).hom
      ((-n.negOnePow) •
        ModuleCat.ofHom
          ((LinearMap.dualMap (ModuleCat.Hom.hom (M.d (-(n + 1)) (-n)))) :
            Module.Dual R (M.X (-n)) →ₗ[R] Module.Dual R (M.X (-(n + 1))))) := by
  -- Evaluate the square pointwise on a functional and an element of `M^{-(n+1)}`; the resulting
  -- scalar identity is exactly the source-faithful coevaluation chain relation.
  refine ⟨?_⟩
  ext φ m
  -- The pointwise identity is already the desired square after expanding the scalar action on the
  -- bottom edge and normalizing `(-n).negOnePow`.
  simpa [Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.dualMap_apply,
    Int.negOnePow_neg] using
    (exactPairing_rightTermIso_moduleDual_d_apply (M := M) (N := N) n φ m)

end
