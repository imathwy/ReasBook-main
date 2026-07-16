import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import stacks_proof.stacks_project.Chap10.Lemma_10_86_3
import stacks_proof.stacks_project.Chap12.Lemma_12_13_9
import stacks_proof.stacks_project.Chap12.Lemma_12_25_4
import stacks_proof.stacks_project.Chap12.Lemma_12_26_1
import stacks_proof.stacks_project.Chap12.Lemma_12_26_ProductTotalAPI

open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂ Opposite

noncomputable section

universe v u

/-
Domain-style sampling for Lemma 12.26.4 in the product-total domain:
- primary domain: product total complexes attached to an augmented row
  `⋯ ⟶ A₂^• ⟶ A₁^• ⟶ A₀^• ⟶ M^•`;
- sampled owner abstractions:
  * `HomologicalComplex₂.productTotal` from the shared product-total API module as the canonical
    bicomplex-level owner on bicomplexes;
  * `HomologicalComplex₂.productTotalOp` and `HomologicalComplex₂.ιTotal` for the canonical
    opposite-side total and its summand inclusions;
  * `ChainComplex.cochainComplexEquivalence` and `CochainComplex.opEquivalence` for the transport
    that identifies product totals with opposite-side coproduct totals;
  * `augmentedTotalTo` from `Lemma_12_26_2` as the chapter-level comparison-map owner on the
    coproduct-total side of the same construction.

Layer triage:
- `source-facing`: the row-specific notation `Tot_π(A)` and
  `productTotalToTarget A π hπ : Tot_π(A) ⟶ M`;
- `core/canonical`: `HomologicalComplex₂.productTotal (augmentedRowBicomplex A)`;
- `bridge/view`: the transported opposite bicomplex and the zeroth-row inclusion into its
  canonical total.

Primitive data are only the augmented row `A` and the augmentation `π : A.X 0 ⟶ M`. The product
coordinates and the total differential are derived API from the shared bicomplex owner, so this
file should expose the row-specific `Tot_π(A)` surface only as a local notation bridge to that
owner, rather than as a second public wrapper definition.
-/

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

local notation "CochainComplex₀" => CochainComplex C ℤ
local notation "CochainResolution" => ChainComplex CochainComplex₀ ℕ

/-- The opposite-side target complex corresponding to `M`. -/
private abbrev productTotalTargetOp
    (M : CochainComplex₀) :
    CochainComplex Cᵒᵖ ℤ :=
  (CochainComplex.opEquivalence C).functor.obj (op M)

/-- The degree-`n` term of the opposite-side target identifies with `M^{-n}` in `Cᵒᵖ`. -/
private theorem productTotalTargetOp_objEq
    (M : CochainComplex₀) (n : ℤ) :
    (productTotalTargetOp M).X n = op (M.X (-n)) := by
  simp [productTotalTargetOp, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence]

/-- Helper for Lemma 12.26.4: under the degree identifications
`(productTotalTargetOp M).X n = op (M.X (-n))`, the transported opposite differential is exactly
the opposite of the original cochain differential on `M^\bullet`. -/
private theorem productTotalTargetOp_d_eq
    (M : CochainComplex₀) {n n' : ℤ} (hn : (up ℤ).Rel n n') :
    eqToHom (productTotalTargetOp_objEq M n) ≫ (productTotalTargetOp M).d n n' ≫
      eqToHom (productTotalTargetOp_objEq M n').symm =
        (M.d (-n') (-n)).op := by
  -- Reindexing through the opposite/cochain equivalences only reverses the degree labels, so the
  -- differential is the original cochain differential viewed in the opposite category.
  have hnn' : n + 1 = n' := by
    simpa [ComplexShape.up, ComplexShape.up'] using hn
  subst hnn'
  simp [productTotalTargetOp, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence]

variable [HasZeroObject C]

/-- The reindexed bicomplex obtained by placing outer degree `n` in horizontal degree `-n`. -/
private abbrev augmentedRowBicomplex (A : CochainResolution) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  A.extend embeddingDownNat

/-- Helper for Lemma 12.26.4: the embedding `embeddingDownNat` sends `0` to `0`. -/
private theorem embeddingDownNat_zero :
    embeddingDownNat.f 0 = (0 : ℤ) := by
  simp

/-- Helper for Lemma 12.26.4: the embedding `embeddingDownNat` sends `1` to `-1`. -/
private theorem embeddingDownNat_one :
    embeddingDownNat.f 1 = (-1 : ℤ) := by
  simp

/-- Helper for Lemma 12.26.4: the embedding `embeddingDownNat` sends `n` to `-n`. -/
private theorem embeddingDownNat_nat (n : ℕ) :
    embeddingDownNat.f n = (-(n : ℤ)) := by
  simp [ComplexShape.embeddingDownNat]

/-- The canonical identification of the horizontal degree-zero row in the reindexed bicomplex with
the original complex `A₀^\bullet`. -/
private abbrev augmentedRowBicomplexZeroIso
    (A : CochainResolution) :
    (augmentedRowBicomplex A).X 0 ≅ A.X 0 :=
  A.extendXIso embeddingDownNat embeddingDownNat_zero

/-- Helper for Lemma 12.26.4: the horizontal degree `-1` row in the reindexed bicomplex is the
original complex `A₁^\bullet`. -/
private abbrev augmentedRowBicomplexNegOneIso
    (A : CochainResolution) :
    (augmentedRowBicomplex A).X (-1) ≅ A.X 1 :=
  A.extendXIso embeddingDownNat embeddingDownNat_one

/-- Helper for Lemma 12.26.4: the horizontal degree `-n` row in the reindexed bicomplex is the
original complex `A_n^\bullet`. -/
private abbrev augmentedRowBicomplexNegIso
    (A : CochainResolution) (n : ℕ) :
    (augmentedRowBicomplex A).X (-(n : ℤ)) ≅ A.X n :=
  A.extendXIso embeddingDownNat (embeddingDownNat_nat n)

/-- Helper for Lemma 12.26.4: the reindexed horizontal differential is the original outer
differential after transporting through the canonical `-n` row identifications. -/
private theorem augmentedRowBicomplex_d_eq
    (A : CochainResolution) (n n' : ℕ) :
    (augmentedRowBicomplex A).d (-(n : ℤ)) (-(n' : ℤ)) =
      (augmentedRowBicomplexNegIso A n).hom ≫
        A.d n n' ≫
        (augmentedRowBicomplexNegIso A n').inv := by
  -- Rewrite the `embeddingDownNat`-extended differential back to the original resolution map.
  simpa [augmentedRowBicomplex, augmentedRowBicomplexNegIso, embeddingDownNat_nat] using
    (HomologicalComplex.extend_d_eq
      (K := A) (e := embeddingDownNat)
      (i := n) (j := n')
      (i' := (-(n : ℤ))) (j' := (-(n' : ℤ)))
      (embeddingDownNat_nat n) (embeddingDownNat_nat n'))

local notation "Tot_π(" A ")" => HomologicalComplex₂.productTotal (augmentedRowBicomplex A)
local notation "ev₀ᵒᵖ" => HomologicalComplex.eval Cᵒᵖ (up ℤ) (0 : ℤ)

/-- Helper for Lemma 12.26.4: the zeroth column of a bicomplex in `Cᵒᵖ` is canonically the
zeroth row of its flip. -/
private noncomputable def product_total_zero_column_iso_zero_row_flip
    (B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)) :
    B.X 0 ≅ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B.flip :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ Iso.refl _)
    (fun q q' hqq' ↦ by
      have h : q + 1 = q' := by
        simpa [ComplexShape.up, ComplexShape.up'] using hqq'
      subst h
      simp)

/-- Helper for Lemma 12.26.4: totalization is available on the flipped bicomplex whenever it is
available on the original bicomplex. -/
private instance product_total_flip_hasTotal
    (B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)) [hB : B.HasTotal (up ℤ)] :
    B.flip.HasTotal (up ℤ) := by
  -- Flipping only swaps the two indices, and total degree is symmetric under that swap.
  classical
  change ∀ j : ℤ,
    HasCoproduct ((B.flip.toGradedObject).mapObjFun (ComplexShape.π (up ℤ) (up ℤ) (up ℤ)) j)
  intro j
  let e : {x : ℤ × ℤ // ComplexShape.π (up ℤ) (up ℤ) (up ℤ) x = j} ≃
      {x : ℤ × ℤ // ComplexShape.π (up ℤ) (up ℤ) (up ℤ) x = j} := {
    toFun := fun x ↦ ⟨(x.1.2, x.1.1), by simpa [ComplexShape.π, add_comm] using x.2⟩
    invFun := fun x ↦ ⟨(x.1.2, x.1.1), by simpa [ComplexShape.π, add_comm] using x.2⟩
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      cases x
      rfl
  }
  let f : {x : ℤ × ℤ // ComplexShape.π (up ℤ) (up ℤ) (up ℤ) x = j} → Cᵒᵖ := fun x ↦
    B.toGradedObject x.1
  let g : {x : ℤ × ℤ // ComplexShape.π (up ℤ) (up ℤ) (up ℤ) x = j} → Cᵒᵖ := fun x ↦
    B.flip.toGradedObject x.1
  have hf : HasCoproduct f := by
    simpa [f, CategoryTheory.GradedObject.mapObjFun, HomologicalComplex₂.HasTotal] using
      (show HasCoproduct
        (B.toGradedObject.mapObjFun (ComplexShape.π (up ℤ) (up ℤ) (up ℤ)) j) from hB j)
  letI : HasCoproduct f := hf
  exact CategoryTheory.Limits.hasCoproduct_of_equiv_of_iso f g e (fun x ↦ Iso.refl _)

/-- Helper for Lemma 12.26.4: a map into the zeroth row of a bicomplex in `Cᵒᵖ` induces the
expected degreewise map into its total complex. -/
private noncomputable def product_total_zero_row_to_total_component
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B) (n : ℤ) :
    K.X n ⟶ (B.total (up ℤ)).X n :=
  α.f n ≫ B.ιTotal (up ℤ) n 0 n (Int.add_zero n)

/-- Helper for Lemma 12.26.4: the degree-`n` component of the row-zero owner is literally the
row map followed by the inclusion of the `(n,0)` antidiagonal summand. -/
private theorem product_total_zero_row_to_total_component_eq
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B) (n : ℤ) :
    product_total_zero_row_to_total_component α n =
      α.f n ≫ B.ιTotal (up ℤ) n 0 n (Int.add_zero n) := by
  -- This simply exposes the definition so later transport lemmas can rewrite with it directly.
  rfl

/-- Helper for Lemma 12.26.4: if the zeroth-row map lands in row cycles, its degreewise total
components assemble to a cochain map. -/
private theorem product_total_zero_row_to_total_d1_on_zero_summand
    {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (n n' : ℤ) :
    B.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫ B.D₁ (up ℤ) n n' =
      B.d₁ (up ℤ) n 0 n' := by
  -- This is the owner `ι_D₁_assoc` formula specialized with the identity postcomposition.
  simpa using
    (HomologicalComplex₂.ι_D₁_assoc (K := B) (c₁₂ := up ℤ)
      n n' n 0 (Int.add_zero n) (𝟙 _))

/-- Helper for Lemma 12.26.4: on the `(n,0)` summand, the total vertical piece restricts to the
owner `d₂` term. -/
private theorem product_total_zero_row_to_total_d2_on_zero_summand
    {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (n n' : ℤ) :
    B.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫ B.D₂ (up ℤ) n n' =
      B.d₂ (up ℤ) n 0 n' := by
  -- This is the owner `ι_D₂_assoc` formula specialized with the identity postcomposition.
  simpa using
    (HomologicalComplex₂.ι_D₂_assoc (K := B) (c₁₂ := up ℤ)
      n n' n 0 (Int.add_zero n) (𝟙 _))

/-- Helper for Chap12 Lemma 12 26 4: move the total-complex sign from the outside of the
precomposed vertical contribution back onto the vertical factor itself. -/
private theorem product_total_zero_row_to_total_vertical_smul_transport
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B)
    (n n' : ℤ) (hn' : n + 1 = n') :
    n.negOnePow • α.f n ≫ ((B.X n).d 0 1 ≫ B.ιTotal (up ℤ) n 1 n' hn') =
      α.f n ≫ (n.negOnePow • ((B.X n).d 0 1 ≫ B.ιTotal (up ℤ) n 1 n' hn')) := by
  -- This is the canonical preadditive transport `f ≫ (r • g) = r • (f ≫ g)` in the opposite row.
  simpa [Category.assoc] using
    (Linear.comp_units_smul (α.f n) n.negOnePow
      (((B.X n).d 0 1) ≫ B.ιTotal (up ℤ) n 1 n' hn')).symm

/-- Helper for Chap12 Lemma 12 26 4: precomposing the owner `D₁` contribution with the row-zero
component map preserves the specialized `(n,0)` horizontal summand formula. -/
private theorem productTotalZeroRowToTotalD1AfterPrecompose
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B)
    (n n' : ℤ) :
    α.f n ≫ (B.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫ B.D₁ (up ℤ) n n') =
      α.f n ≫ B.d₁ (up ℤ) n 0 n' := by
  -- This is the horizontal `(n,0)` owner identity postcomposed with `α.f n`.
  simpa [Category.assoc] using
    congrArg (fun f ↦ α.f n ≫ f)
      (product_total_zero_row_to_total_d1_on_zero_summand (B := B) n n')

/-- Helper for Chap12 Lemma 12 26 4: precomposing the owner `D₂` contribution with the row-zero
component map preserves the specialized `(n,0)` vertical summand formula. -/
private theorem productTotalZeroRowToTotalD2AfterPrecompose
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B)
    (n n' : ℤ) :
    α.f n ≫ (B.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫ B.D₂ (up ℤ) n n') =
      α.f n ≫ B.d₂ (up ℤ) n 0 n' := by
  -- This is the vertical `(n,0)` owner identity postcomposed with `α.f n`.
  simpa [Category.assoc] using
    congrArg (fun f ↦ α.f n ≫ f)
      (product_total_zero_row_to_total_d2_on_zero_summand (B := B) n n')

/-- Helper for Chap12 Lemma 12 26 4: precomposing the row-zero summand inclusion with the total
differential first splits into the specialized horizontal and vertical total pieces. -/
private theorem productTotalZeroRowToTotalTotalDDecomposition
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B)
    (n n' : ℤ) :
    product_total_zero_row_to_total_component α n ≫ (B.total (up ℤ)).d n n' =
      α.f n ≫ B.d₁ (up ℤ) n 0 n' +
        α.f n ≫ B.d₂ (up ℤ) n 0 n' := by
  -- Expand the total differential into its horizontal and vertical parts on the `(n,0)` summand.
  calc
    product_total_zero_row_to_total_component α n ≫ (B.total (up ℤ)).d n n' =
        α.f n ≫
          (B.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫
            (B.D₁ (up ℤ) n n' + B.D₂ (up ℤ) n n')) := by
      rfl
    _ =
        α.f n ≫ (B.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫ B.D₁ (up ℤ) n n') +
          α.f n ≫ (B.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫ B.D₂ (up ℤ) n n') := by
      rw [Preadditive.comp_add, Category.assoc, Category.assoc]
    _ =
        α.f n ≫ B.d₁ (up ℤ) n 0 n' +
          α.f n ≫ B.d₂ (up ℤ) n 0 n' := by
      rw [productTotalZeroRowToTotalD1AfterPrecompose,
        productTotalZeroRowToTotalD2AfterPrecompose]

/-- Helper for Chap12 Lemma 12 26 4: the row-zero vertical relation needed in the normalization
step is the unique successor relation `0 ⟶ 1` in `ComplexShape.up ℤ`. -/
private theorem productTotalZeroRowRelZeroOne :
    (up ℤ).Rel (0 : ℤ) 1 := by
  simp [ComplexShape.up, ComplexShape.up']

/-- Helper for Chap12 Lemma 12 26 4: on the `(n,0)` summand, the opposite-side total
differential first appears in the raw scalar-outside form produced by `d₂_eq`. -/
private theorem productTotalZeroRowToTotalTotalDOnZeroSummandInside
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B)
    (n n' : ℤ) (hrel : (up ℤ).Rel n n') (hn' : n + 1 = n') :
    product_total_zero_row_to_total_component α n ≫ (B.total (up ℤ)).d n n' =
      α.f n ≫ ((B.d n n').f 0 ≫ B.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
        α.f n ≫
          (n.negOnePow • ((B.X n).d 0 1 ≫ B.ιTotal (up ℤ) n 1 n' hn')) := by
  -- Rewrite the two specialized total pieces with the owner `d₁_eq` and `d₂_eq` formulas.
  calc
    product_total_zero_row_to_total_component α n ≫ (B.total (up ℤ)).d n n' =
        α.f n ≫ B.d₁ (up ℤ) n 0 n' + α.f n ≫ B.d₂ (up ℤ) n 0 n' := by
      exact productTotalZeroRowToTotalTotalDDecomposition α n n'
    _ =
        α.f n ≫ ((B.d n n').f 0 ≫ B.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
          α.f n ≫
            (n.negOnePow • ((B.X n).d 0 1 ≫ B.ιTotal (up ℤ) n 1 n' hn')) := by
      rw [B.d₁_eq hrel 0 n' (Int.add_zero n'), B.d₂_eq n productTotalZeroRowRelZeroOne n' hn']
      simp [ComplexShape.ε_up_ℤ]

/-- Helper for Chap12 Lemma 12 26 4: on the `(n,0)` summand, the opposite-side total
differential first appears in the raw scalar-outside form produced by `d₂_eq`. -/
private theorem productTotalZeroRowToTotalTotalDOnZeroSummandScalarOutside
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B)
    (n n' : ℤ) (hrel : (up ℤ).Rel n n') (hn' : n + 1 = n') :
    product_total_zero_row_to_total_component α n ≫ (B.total (up ℤ)).d n n' =
      α.f n ≫ ((B.d n n').f 0 ≫ B.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
        n.negOnePow • (α.f n ≫ ((B.X n).d 0 1 ≫ B.ιTotal (up ℤ) n 1 n' hn')) := by
  -- Transport the inside-smul normalization to the raw outside-smul surface used by `d₂_eq`.
  calc
    product_total_zero_row_to_total_component α n ≫ (B.total (up ℤ)).d n n' =
        α.f n ≫ ((B.d n n').f 0 ≫ B.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
          α.f n ≫
            (n.negOnePow • ((B.X n).d 0 1 ≫ B.ιTotal (up ℤ) n 1 n' hn')) := by
      exact productTotalZeroRowToTotalTotalDOnZeroSummandInside α n n' hrel hn'
    _ =
        α.f n ≫ ((B.d n n').f 0 ≫ B.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
          n.negOnePow • (α.f n ≫ ((B.X n).d 0 1 ≫ B.ιTotal (up ℤ) n 1 n' hn')) := by
      rw [← product_total_zero_row_to_total_vertical_smul_transport (α := α) n n' hn']

/-- Helper for Lemma 12.26.4: if the zeroth-row map lands in row cycles, its degreewise total
components assemble to a cochain map. -/
private theorem product_total_zero_row_to_total_total_d_on_zero_summand
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B)
    (n n' : ℤ) (hrel : (up ℤ).Rel n n') (hn' : n + 1 = n') :
    product_total_zero_row_to_total_component α n ≫ (B.total (up ℤ)).d n n' =
      α.f n ≫ ((B.d n n').f 0 ≫ B.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
        α.f n ≫
          (n.negOnePow • ((B.X n).d 0 1 ≫ B.ιTotal (up ℤ) n 1 n' hn')) := by
  -- This is the normalized row-zero total-differential formula used by the commutativity proof.
  exact productTotalZeroRowToTotalTotalDOnZeroSummandInside α n n' hrel hn'

/-- Helper for Lemma 12.26.4: if the zeroth-row map lands in row cycles, its degreewise total
components assemble to a cochain map. -/
private theorem product_total_zero_row_to_total_comm
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (B.X p).d 0 1 = 0)
    (n n' : ℤ) (hrel : (up ℤ).Rel n n') :
    product_total_zero_row_to_total_component α n ≫ (B.total (up ℤ)).d n n' =
      K.d n n' ≫ product_total_zero_row_to_total_component α n' := by
  have hn' : n + 1 = n' := by
    simpa [ComplexShape.up, ComplexShape.up'] using hrel
  -- Normalize the total differential on the `(n,0)` summand, then remove the vertical term.
  calc
    product_total_zero_row_to_total_component α n ≫ (B.total (up ℤ)).d n n' =
        α.f n ≫ ((B.d n n').f 0 ≫ B.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
          α.f n ≫
            (n.negOnePow • ((B.X n).d 0 1 ≫ B.ιTotal (up ℤ) n 1 n' hn')) := by
      exact product_total_zero_row_to_total_total_d_on_zero_summand α n n' hrel hn'
    _ =
        α.f n ≫ ((B.d n n').f 0 ≫ B.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) := by
      rw [Linear.comp_units_smul, hαcycles n, zero_comp, smul_zero, add_zero]
    _ =
        K.d n n' ≫ α.f n' ≫ B.ιTotal (up ℤ) n' 0 n' (Int.add_zero n') := by
      rw [← Category.assoc, α.comm n n' hrel]
    _ = K.d n n' ≫ product_total_zero_row_to_total_component α n' := by
      rfl

/-- Helper for Lemma 12.26.4: the row-zero comparison into the total complex of a bicomplex in
`Cᵒᵖ`. -/
private noncomputable def product_total_zero_row_to_total
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (B.X p).d 0 1 = 0) :
    K ⟶ B.total (up ℤ) where
  f := product_total_zero_row_to_total_component α
  comm' := product_total_zero_row_to_total_comm α hαcycles

/-- Helper for Lemma 12.26.4: the zero-column comparison becomes a zero-row comparison after
flipping the bicomplex. -/
private noncomputable def product_total_zero_column_to_zero_row_flip
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)}
    (α : K ⟶ B.X 0) :
    K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B.flip :=
  α ≫ (product_total_zero_column_iso_zero_row_flip B).hom

/-- Helper for Lemma 12.26.4: the zero-column cycle condition is exactly the zero-row cycle
condition after flipping. -/
private theorem product_total_zero_column_to_zero_row_flip_comp_d
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)}
    (α : K ⟶ B.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (B.d 0 1).f q = 0) :
    ∀ q : ℤ,
      (product_total_zero_column_to_zero_row_flip α).f q ≫ (B.flip.X q).d 0 1 = 0 := by
  intro q
  -- The zero-column/zero-row identification is componentwise the identity.
  simpa [product_total_zero_column_to_zero_row_flip,
    product_total_zero_column_iso_zero_row_flip] using hαcycles q

/-- Helper for Lemma 12.26.4: the generic zero-column comparison into the total complex of a
bicomplex in `Cᵒᵖ`. -/
private noncomputable def product_total_zero_column_to_total
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ B.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (B.d 0 1).f q = 0) :
    K ⟶ B.total (up ℤ) :=
  product_total_zero_row_to_total
      (product_total_zero_column_to_zero_row_flip α)
      (product_total_zero_column_to_zero_row_flip_comp_d α hαcycles) ≫
    (B.totalFlipIso (up ℤ)).hom

/-- Helper for Lemma 12.26.4: `(0,n)` lies on the antidiagonal of total degree `n`. -/
private theorem zero_column_total_degree (n : ℤ) :
    ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (0, n) = n := by
  simp

/-- Helper for Lemma 12.26.4: the generic zero-column owner already lands on the literal
`(0,n)` summand after undoing the flip transport. -/
private theorem product_total_zero_column_to_total_component_on_zero_summand
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ B.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (B.d 0 1).f q = 0)
    (n : ℤ) :
    (product_total_zero_column_to_total α hαcycles).f n =
      α.f n ≫ B.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) := by
  -- Unfold the owner map once; the flip isomorphism then collapses the `(n,0)` summand of
  -- `B.flip` to the literal `(0,n)` summand of `B`.
  calc
    (product_total_zero_column_to_total α hαcycles).f n =
        α.f n ≫ B.flip.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫
          (B.totalFlipIso (up ℤ)).hom.f n := by
      simp [product_total_zero_column_to_total, product_total_zero_row_to_total,
        product_total_zero_row_to_total_component, product_total_zero_column_to_zero_row_flip,
        product_total_zero_column_iso_zero_row_flip, Category.assoc]
    -- Reduce the flip transport to the literal `(0,n)` summand using the owner symmetry formula.
    _ =
        α.f n ≫
          (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) 0 n •
            B.ιTotal (up ℤ) 0 n n (zero_column_total_degree n)) := by
      have hflip :
          B.flip.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫ (B.totalFlipIso (up ℤ)).hom.f n =
            ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) 0 n •
              B.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) := by
        simpa [zero_column_total_degree] using
          (HomologicalComplex₂.ιTotal_totalFlipIso_f_hom
            (K := B) (c := up ℤ) (i₁ := 0) (i₂ := n) (j := n) (h := Int.add_zero n))
      exact congrArg (fun f ↦ α.f n ≫ f) hflip
    _ = α.f n ≫ B.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) := by
      simp

/-- The zeroth row of the opposite-side bicomplex in degree `n` is the opposite of
`A₀^{-n}`. -/
private theorem productTotalZeroRow_objEq
    (A : CochainResolution) (n : ℤ) :
    ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).X 0).X n =
      op (((augmentedRowBicomplex A).X 0).X (-n)) := by
  simp [HomologicalComplex₂.productTotalOpBicomplex, HomologicalComplex₂.productTotalCochainOp,
    CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
    HomologicalComplex.opEquivalence]

/-- Helper for Lemma 12.26.4: the `p`-th column of the opposite product-total bicomplex in degree
`n` is the opposite of the `(-p)`-th row of the original reindexed bicomplex in degree `-n`. -/
private theorem productTotalColumn_objEq
    (A : CochainResolution) (p n : ℤ) :
    ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).X p).X n =
      op (((augmentedRowBicomplex A).X (-p)).X (-n)) := by
  -- Both the outer and inner cochain/opposite transports reverse the corresponding degrees.
  simp [HomologicalComplex₂.productTotalOpBicomplex, HomologicalComplex₂.productTotalCochainOp,
    CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
    HomologicalComplex.opEquivalence]

/-- Helper for Lemma 12.26.4: under the degree identifications for the zeroth column of the
opposite product-total bicomplex, the transported vertical differential is the opposite of the
original cochain differential on `A₀^\bullet`. -/
private theorem productTotalZeroRow_d_eq
    (A : CochainResolution) {n n' : ℤ} (hn : (up ℤ).Rel n n') :
    eqToHom (productTotalZeroRow_objEq A n) ≫
      ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).X 0).d n n' ≫
        eqToHom (productTotalZeroRow_objEq A n').symm =
          (((augmentedRowBicomplex A).X 0).d (-n') (-n)).op := by
  -- Reindexing the zeroth column through the opposite/cochain equivalences only reverses the
  -- degree labels, so the column differential is the original cochain differential in `Cᵒᵖ`.
  have hnn' : n + 1 = n' := by
    simpa [ComplexShape.up, ComplexShape.up'] using hn
  subst hnn'
  simp [HomologicalComplex₂.productTotalOpBicomplex, HomologicalComplex₂.productTotalCochainOp,
    CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
    HomologicalComplex.opEquivalence]

/-- Helper for Lemma 12.26.4: after transporting the horizontal differential of the opposite
product-total bicomplex, one recovers the opposite of the original row differential. -/
private theorem productTotalColumn_d_eq
    (A : CochainResolution) {p p' q : ℤ} (hp : (up ℤ).Rel p p') :
    eqToHom (productTotalColumn_objEq A p q) ≫
      ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).d p p').f q ≫
        eqToHom (productTotalColumn_objEq A p' q).symm =
          (((augmentedRowBicomplex A).d (-p') (-p)).f (-q)).op := by
  -- Reindexing through the opposite/cochain equivalences reverses the horizontal degree labels.
  have hpp' : p + 1 = p' := by
    simpa [ComplexShape.up, ComplexShape.up'] using hp
  subst hpp'
  simp [HomologicalComplex₂.productTotalOpBicomplex, HomologicalComplex₂.productTotalCochainOp,
    CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
    HomologicalComplex.opEquivalence]

variable [HasCountableProducts C]

variable (A : CochainResolution)
variable {M : CochainComplex₀} (π : A.X 0 ⟶ M)

/-- Helper for Lemma 12.26.4: the `(0,n)` summand lies on the antidiagonal of total degree `n`. -/
private theorem product_total_zero_column_total_degree (n : ℤ) :
    ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (0, n) = n := by
  simp

/-- The degree-`n` component of the canonical comparison map from `Tot_π(A)` to the augmented
target complex. On the opposite side, it is the canonical inclusion of the `(0,n)` summand in the
coproduct total. -/
private noncomputable def productTotalToTargetOpComponent
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M) (n : ℤ) :
    (productTotalTargetOp M).X n ⟶
      (HomologicalComplex₂.productTotalOp (augmentedRowBicomplex A)).X n :=
  (π.f (-n)).op ≫
    ((augmentedRowBicomplexZeroIso A).hom.f (-n)).op ≫
      (HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).ιTotal
        (up ℤ) 0 n n (product_total_zero_column_total_degree n)

/-- Helper for Lemma 12.26.4: the zero-column comparison map is the component family underlying
`productTotalToTargetOpComponent` before inserting the total inclusion. -/
private noncomputable def product_total_target_zero_column_component
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M) (n : ℤ) :
    (productTotalTargetOp M).X n ⟶
      ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).X 0).X n :=
  (π.f (-n)).op ≫ ((augmentedRowBicomplexZeroIso A).hom.f (-n)).op

/-- Helper for Lemma 12.26.4: the unique horizontal differential entering the zero column becomes
zero after composing with the augmentation map, because it is exactly `A₁^\bullet ⟶ A₀^\bullet`
followed by `π`. -/
private theorem product_total_target_prev_column_comp_zero
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    (augmentedRowBicomplex A).d (-1) 0 ≫ (augmentedRowBicomplexZeroIso A).hom ≫ π = 0 := by
  have hd :
      (augmentedRowBicomplex A).d (-1) 0 =
        (augmentedRowBicomplexNegOneIso A).hom ≫
          A.d 1 0 ≫
            (augmentedRowBicomplexZeroIso A).inv := by
    -- Rewrite the reindexed horizontal differential back in terms of the original resolution.
    simpa [augmentedRowBicomplex, augmentedRowBicomplexNegOneIso, augmentedRowBicomplexZeroIso]
      using
        (HomologicalComplex.extend_d_eq
          (K := A) (e := embeddingDownNat) (i := 1) (j := 0)
          (i' := (-1 : ℤ)) (j' := (0 : ℤ)) rfl rfl)
  -- After identifying the `(-1)`-st and `0`-th rows with `A₁^\bullet` and `A₀^\bullet`, the
  -- composite is exactly `A.d 1 0 ≫ π`.
  rw [hd]
  simp [Category.assoc, hπ]

/-- Helper for Lemma 12.26.4: evaluating the vanishing of the previous-row augmentation composite
in degree `-q` gives the componentwise zero relation needed for the opposite-side cycle check. -/
private theorem product_total_target_prev_column_comp_zero_f
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) (q : ℤ) :
    ((augmentedRowBicomplex A).d (-1) 0).f (-q) ≫
        (augmentedRowBicomplexZeroIso A).hom.f (-q) ≫ π.f (-q) = 0 := by
  -- Evaluate the complex-level augmentation-zero relation in the required vertical degree.
  simpa [Category.assoc] using
    congrArg (fun f ↦ f.f (-q)) (product_total_target_prev_column_comp_zero A π hπ)

/-- Helper for Lemma 12.26.4: after passing to the opposite category, the degree-`-q` vanishing of
the previous-row augmentation composite acquires the orientation used by the explicit zero-column
component family. -/
private theorem product_total_target_prev_column_comp_zero_op
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) (q : ℤ) :
    (π.f (-q)).op ≫ ((augmentedRowBicomplexZeroIso A).hom.f (-q)).op ≫
        (((augmentedRowBicomplex A).d (-1) 0).f (-q)).op = 0 := by
  -- Opposites reverse the composite, matching the orientation on the transported zero column.
  simpa [Category.assoc] using
    congrArg Quiver.Hom.op (product_total_target_prev_column_comp_zero_f A π hπ q)

/-- Helper for Lemma 12.26.4: the explicit opposite-side zero-column component family is already a
cochain map into the zeroth column. -/
private theorem product_total_target_zero_column_map_comm
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (n n' : ℤ) (_ : (up ℤ).Rel n n') :
    product_total_target_zero_column_component A π n ≫
      ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).X 0).d n n' =
        (productTotalTargetOp M).d n n' ≫ product_total_target_zero_column_component A π n' := by
  let φ :
      productTotalTargetOp M ⟶
        ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).X 0) :=
    ((CochainComplex.opEquivalence C).functor.map
      (((augmentedRowBicomplexZeroIso A).hom ≫ π).op))
  -- Route correction: use the transported opposite chain map directly, then read off its
  -- degreewise components instead of conjugating the differential comparison by hand.
  simpa [φ, product_total_target_zero_column_component, productTotalTargetOp,
    HomologicalComplex₂.productTotalOpBicomplex, HomologicalComplex₂.productTotalCochainOp,
    CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
    HomologicalComplex.opEquivalence, Category.assoc] using φ.comm n n'

/-- Helper for Lemma 12.26.4: the zero-column comparison into the opposite bicomplex is the
explicit opposite-side augmentation family into the zeroth column. -/
private noncomputable def product_total_target_zero_column_map
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M) :
    productTotalTargetOp M ⟶
      ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).X 0) where
  f := product_total_target_zero_column_component A π
  comm' := product_total_target_zero_column_map_comm A π

/-- Helper for Lemma 12.26.4: the packaged zero-column comparison has the expected degreewise
components. -/
private theorem product_total_target_zero_column_map_eq_component
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M) (n : ℤ) :
    (product_total_target_zero_column_map A π).f n =
      product_total_target_zero_column_component A π n := by
  -- The packaged zero-column comparison was defined from the explicit component family.
  rfl

/-- Helper for Lemma 12.26.4: the packaged zero-column comparison lands in the cycles of the
first horizontal differential. -/
private theorem product_total_target_zero_column_map_cycles
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (q : ℤ) :
    (product_total_target_zero_column_map A π).f q ≫
        ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).d 0 1).f q = 0 := by
  -- Rewrite the horizontal differential of the opposite bicomplex to the opposite of the
  -- original row differential, then use the already-proved augmentation vanishing in degree `-q`.
  rw [product_total_target_zero_column_map_eq_component]
  simpa [product_total_target_zero_column_component, Category.assoc,
    HomologicalComplex₂.productTotalOpBicomplex, HomologicalComplex₂.productTotalCochainOp,
    CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
    HomologicalComplex.opEquivalence] using
    product_total_target_prev_column_comp_zero_op A π hπ q

/-- Helper for Lemma 12.26.4: the degree-`q` zero-column row is the short complex whose cycles
identify the target object with the zeroth-column cycles of the opposite bicomplex. -/
private abbrev product_total_target_zero_column_shortComplex
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) (q : ℤ) :
    ShortComplex Cᵒᵖ :=
  ShortComplex.mk
    (product_total_target_zero_column_component A π q)
    (((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).d 0 1).f q)
    (product_total_target_zero_column_map_cycles (A := A) (π := π) hπ q)

/-- Helper for Lemma 12.26.4: the generic zero-column comparison from Lemma 12.25.4 has the same
degreewise components as the explicit map `productTotalToTargetOpComponent`. -/
private theorem product_total_target_op_component_eq_zero_column_to_total
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (n : ℤ) :
    (product_total_zero_column_to_total
        (product_total_target_zero_column_map A π)
        (product_total_target_zero_column_map_cycles (A := A) (π := π) hπ)).f n =
      productTotalToTargetOpComponent A π n := by
  -- Both sides are the same zero-column component followed by the inclusion of the `(0,n)`
  -- antidiagonal summand in the opposite total complex.
  have hcomponent :=
    product_total_zero_column_to_total_component_on_zero_summand
      (α := product_total_target_zero_column_map A π)
      (hαcycles := product_total_target_zero_column_map_cycles (A := A) (π := π) hπ) n
  simpa [productTotalToTargetOpComponent, product_total_target_zero_column_component,
    product_total_target_zero_column_map, Category.assoc] using hcomponent

/-- The opposite-side comparison morphism from the transported target complex into the coproduct
total. -/
private noncomputable def productTotalToTargetOp
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    productTotalTargetOp M ⟶ HomologicalComplex₂.productTotalOp (augmentedRowBicomplex A) :=
  product_total_zero_column_to_total
    (product_total_target_zero_column_map A π)
    (product_total_target_zero_column_map_cycles (A := A) (π := π) hπ)

/-- Helper for Chap12 Lemma 12 26 4: the opposite comparison map is literally the owner-level
zero-column comparison from Lemma 12.25.4 applied to the explicit augmentation data. -/
private theorem productTotalToTargetOpUsesZeroColumnOwner
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    productTotalToTargetOp A π hπ =
      product_total_zero_column_to_total
        (product_total_target_zero_column_map A π)
        (product_total_target_zero_column_map_cycles (A := A) (π := π) hπ) := by
  -- The file now reuses the owner construction directly, so this bridge is definitional.
  rfl

/-- Helper for Lemma 12.26.4: after packaging the zero-column comparison through the generic
owner from Lemma 12.25.4, the old explicit component family is recovered degreewise. -/
private theorem productTotalToTargetOp_comm_unop
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (i j : ℤ) (_ : (up ℤ).Rel i j) :
    productTotalToTargetOpComponent A π i ≫
        (HomologicalComplex₂.productTotalOp (augmentedRowBicomplex A)).d i j =
      (productTotalTargetOp M).d i j ≫
        productTotalToTargetOpComponent A π j := by
  have hcomm := (productTotalToTargetOp A π hπ).comm i j
  -- The generic zero-column owner is already a chain map, so the explicit component formula
  -- follows by rewriting its degreewise components on both sides.
  rw [← product_total_target_op_component_eq_zero_column_to_total (A := A) (π := π) hπ i,
    ← product_total_target_op_component_eq_zero_column_to_total (A := A) (π := π) hπ j]
  exact hcomm

/-- The canonical comparison map from `Tot_π(A)` to the augmented target complex in the abelian
groups setting. -/
@[stacks 0E1R]
def productTotalToTarget
    (A : ChainComplex (CochainComplex AddCommGrpCat ℤ) ℕ)
    {M : CochainComplex AddCommGrpCat ℤ} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    Tot_π(A) ⟶ M :=
  (((CochainComplex.opEquivalence AddCommGrpCat).inverse.map
    (productTotalToTargetOp A π hπ))).unop ≫
      (((CochainComplex.opEquivalence AddCommGrpCat).unitIso.app (op M)).unop).hom

end

section

local notation "AbOpCochainComplex" => CochainComplex AddCommGrpCatᵒᵖ ℤ
local notation "ev₀ᵒᵖₐᵦ" => HomologicalComplex.eval AddCommGrpCatᵒᵖ (up ℤ) (0 : ℤ)

/-- Helper for Lemma 12.26.4: a map into the zero row of a bicomplex in `AddCommGrpCatᵒᵖ`
induces the corresponding map to cycles. -/
private noncomputable def doubleComplexZeroRowCyclesMap
    {K : AbOpCochainComplex} {B : HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)}
    (α : K ⟶ (ev₀ᵒᵖₐᵦ.mapHomologicalComplex (up ℤ)).obj B)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (B.X p).d 0 1 = 0) (p : ℤ) :
    K.X p ⟶ (B.X p).cycles 0 :=
  (B.X p).liftCycles' (α.f p) 1 rfl (hαcycles p)

/-- Helper for Lemma 12.26.4: the zero-column/zero-row flip owner used later in the file is the
same local comparison map introduced above. -/
private noncomputable abbrev doubleComplexZeroColumnToZeroRowFlip
    {K : AbOpCochainComplex} {B : HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)}
    (α : K ⟶ B.X 0) :
    K ⟶ (ev₀ᵒᵖₐᵦ.mapHomologicalComplex (up ℤ)).obj B.flip :=
  product_total_zero_column_to_zero_row_flip α

/-- Helper for Lemma 12.26.4: the zero-column cycle condition is exactly the row-zero cycle
condition after flipping. -/
private theorem doubleComplexZeroColumnToZeroRowFlip_comp_d
    {K : AbOpCochainComplex} {B : HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)}
    (α : K ⟶ B.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (B.d 0 1).f q = 0) :
    ∀ q : ℤ, (doubleComplexZeroColumnToZeroRowFlip α).f q ≫ (B.flip.X q).d 0 1 = 0 :=
  product_total_zero_column_to_zero_row_flip_comp_d α hαcycles

/-- Helper for Lemma 12.26.4: a map into the zero column induces the corresponding map to the
row cycles of the flipped bicomplex. -/
private noncomputable def doubleComplexZeroColumnCyclesMap
    {K : AbOpCochainComplex} {B : HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)}
    (α : K ⟶ B.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (B.d 0 1).f q = 0) (q : ℤ) :
    K.X q ⟶ (B.flip.X q).cycles 0 :=
  doubleComplexZeroRowCyclesMap
    (doubleComplexZeroColumnToZeroRowFlip α)
    (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) q

end

section

local notation "AbCochainComplex" => CochainComplex AddCommGrpCat ℤ
local notation "AbCochainResolution" => ChainComplex AbCochainComplex ℕ

/-- Helper for Lemma 12.26.4: exactness of the augmented row of cochain complexes can be checked
degreewise, so every vertical degree yields an exact short complex of objects. -/
private theorem augmented_row_degreewise_exact
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (q : ℤ) :
    (ShortComplex.mk ((A.d 1 0).f q) (π.f q)
      (by simpa using congrArg (fun f ↦ f.f q) hπ)).Exact := by
  -- Evaluate the exact short complex of cochain complexes at degree `q`.
  simpa using
    (HomologicalComplex.exact_iff_degreewise_exact
      (S := ShortComplex.mk (A.d 1 0) π hπ)).1 hExact₀ q

/-- Helper for Lemma 12.26.4: an epimorphic augmentation of cochain complexes is epimorphic in
each vertical degree. This is the base-step surjectivity used in the staircase lift. -/
private theorem augmentation_degreewise_epi
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hEpi : Epi π)
    (q : ℤ) :
    Epi (π.f q) := by
  -- Reduce the complex-level epimorphism to degreewise epimorphy via the Chapter 12 bridge.
  letI : Epi π := hEpi
  exact (cochainComplex_epi_iff_degreewise_epi π).1 inferInstance q

/-- Helper for Chap12 Lemma 12 26 4: after identifying the rows `-1` and `0` of the reindexed
augmented bicomplex with `A₁^\bullet` and `A₀^\bullet`, the degree-`q` augmented row is still
exact. -/
private theorem augmented_row_reindexed_degreewise_exact
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (q : ℤ) :
    (ShortComplex.mk
      (((augmentedRowBicomplex A).d (-1) 0).f q)
      ((augmentedRowBicomplexZeroIso A).hom.f q ≫ π.f q)
      (by
        simpa [Category.assoc] using
          congrArg (fun f : (augmentedRowBicomplex A).X (-1) ⟶ M ↦ f.f q)
            (product_total_target_prev_column_comp_zero A π hπ))).Exact := by
  let e₁ :
      (((augmentedRowBicomplex A).X (-1)).X q) ≅ ((A.X 1).X q) :=
    (HomologicalComplex.eval AddCommGrpCat (up ℤ) q).mapIso (augmentedRowBicomplexNegOneIso A)
  let e₂ :
      (((augmentedRowBicomplex A).X 0).X q) ≅ ((A.X 0).X q) :=
    (HomologicalComplex.eval AddCommGrpCat (up ℤ) q).mapIso (augmentedRowBicomplexZeroIso A)
  let S₁ : ShortComplex AddCommGrpCat :=
    ShortComplex.mk
      (((augmentedRowBicomplex A).d (-1) 0).f q)
      ((augmentedRowBicomplexZeroIso A).hom.f q ≫ π.f q)
      (by
        simpa [Category.assoc] using
          congrArg (fun f : (augmentedRowBicomplex A).X (-1) ⟶ M ↦ f.f q)
            (product_total_target_prev_column_comp_zero A π hπ))
  let S₂ : ShortComplex AddCommGrpCat :=
    ShortComplex.mk ((A.d 1 0).f q) (π.f q)
      (by simpa using congrArg (fun f ↦ f.f q) hπ)
  have hd :
      (augmentedRowBicomplex A).d (-1) 0 =
        (augmentedRowBicomplexNegOneIso A).hom ≫
          A.d 1 0 ≫
            (augmentedRowBicomplexZeroIso A).inv := by
    -- Rewrite the reindexed horizontal differential back to the original resolution map.
    simpa [augmentedRowBicomplex, augmentedRowBicomplexNegOneIso, augmentedRowBicomplexZeroIso]
      using
        (HomologicalComplex.extend_d_eq
          (K := A) (e := embeddingDownNat) (i := 1) (j := 0)
          (i' := (-1 : ℤ)) (j' := (0 : ℤ)) rfl rfl)
  have hIso : S₁ ≅ S₂ := by
    refine ShortComplex.isoMk e₁ e₂ (Iso.refl _) ?_ ?_
    · -- Evaluating the owner `extend_d_eq` comparison identifies the reindexed first map.
      have hdq :
          (((augmentedRowBicomplex A).d (-1) 0).f q) =
            e₁.hom ≫ (A.d 1 0).f q ≫ e₂.inv := by
        simpa [e₁, e₂] using congrArg (fun f ↦ f.f q) hd
      simpa [S₁, S₂, Category.assoc] using
        (congrArg (fun f ↦ f ≫ e₂.hom) hdq).symm
    · -- The second map is already the original augmentation after the row-zero identification.
      simp [S₁, S₂, e₂]
  -- Transport the already-proved degreewise exact row across the row identifications.
  simpa [S₁, S₂] using
    ShortComplex.exact_of_iso hIso.symm
      (augmented_row_degreewise_exact (A := A) (π := π) hπ hExact₀ q)

/-- Helper for Chap12 Lemma 12 26 4: the reindexed degree-`q` augmentation remains epimorphic,
because it differs from `π^q` only by an isomorphism on the middle object. -/
private theorem augmented_row_reindexed_degreewise_epi
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hEpi : Epi π)
    (q : ℤ) :
    Epi ((augmentedRowBicomplexZeroIso A).hom.f q ≫ π.f q) := by
  -- The row-zero identification is an isomorphism, so epicity is inherited from `π^q`.
  letI : Epi (π.f q) := augmentation_degreewise_epi π hEpi q
  infer_instance

/-- Helper for Lemma 12.26.4: exactness at `A₀^{-q}` together with epicity of `π^{-q}` upgrades
the opposite zero-column comparison to an isomorphism onto the zeroth-column cycles. -/
private theorem product_total_target_zero_column_cycles_isIso
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (q : ℤ) :
    IsIso
      (doubleComplexZeroColumnCyclesMap
        (product_total_target_zero_column_map A π)
        (product_total_target_zero_column_map_cycles (A := A) (π := π) hπ)
        q) := by
  let S₁ : ShortComplex AddCommGrpCatᵒᵖ :=
    product_total_target_zero_column_shortComplex A π hπ q
  let S₂ : ShortComplex AddCommGrpCat :=
    ShortComplex.mk
      (((augmentedRowBicomplex A).d (-1) 0).f (-q))
      ((augmentedRowBicomplexZeroIso A).hom.f (-q) ≫ π.f (-q))
      (by
        -- This is the degreewise form of the augmentation relation on the reindexed row.
        simpa [Category.assoc] using
          congrArg (fun f : (augmentedRowBicomplex A).X (-1) ⟶ M ↦ f.f (-q))
            (product_total_target_prev_column_comp_zero A π hπ))
  have hIso : S₁ ≅ S₂.op := by
    refine ShortComplex.isoMk
      (eqToIso (productTotalTargetOp_objEq M q))
      (eqToIso (productTotalZeroRow_objEq A q))
      (eqToIso (productTotalColumn_objEq A 1 q))
      ?_ ?_
    · -- The first map is literally the opposite of the reindexed augmentation component.
      simp [S₁, S₂, product_total_target_zero_column_shortComplex,
        product_total_target_zero_column_component, Category.assoc]
    · -- The second map is the transported `0 → 1` horizontal differential of the opposite
      -- bicomplex.
      simpa [S₁, S₂, product_total_target_zero_column_shortComplex] using
        (productTotalColumn_d_eq A (p := (0 : ℤ)) (p' := (1 : ℤ)) (q := q) (by simp))
  have hS₂ : S₂.Exact := by
    -- Reuse the already-transported exact augmented row at vertical degree `-q`.
    simpa [S₂] using augmented_row_reindexed_degreewise_exact
      (A := A) (π := π) hπ hExact₀ (-q)
  have hS₁ : S₁.Exact := by
    -- Opposing the exact short complex produces the exact short complex controlling cycles in the
    -- zeroth column.
    exact (ShortComplex.exact_iff_of_iso hIso).2 hS₂.op
  letI : Mono S₁.f := by
    -- In the opposite category, monicity of the first map is the transported epicity of the
    -- original augmentation component.
    letI : Epi ((augmentedRowBicomplexZeroIso A).hom.f (-q) ≫ π.f (-q)) :=
      augmented_row_reindexed_degreewise_epi (A := A) (π := π) hEpi (-q)
    simpa [S₁, product_total_target_zero_column_shortComplex,
      product_total_target_zero_column_component, Category.assoc] using
      (show Mono (((augmentedRowBicomplexZeroIso A).hom.f (-q) ≫ π.f (-q)).op) by
        infer_instance)
  -- The zero-column cycles map is exactly the `toCycles` map of the exact opposite short
  -- complex above.
  simpa [doubleComplexZeroColumnCyclesMap, doubleComplexZeroRowCyclesMap, S₁,
    product_total_target_zero_column_shortComplex] using
    (shortComplex_toCycles_isIso_of_exact_of_mono S₁ hS₁)

/-- Helper for Chap12 Lemma 12 26 4: an acyclic cochain-level mapping cone yields a
quasi-isomorphism. -/
private theorem quasiIso_of_mappingCone_acyclic
    {L M : AbCochainComplex} (f : L ⟶ M) (hCone : (CochainComplex.mappingCone f).Acyclic) :
    QuasiIso f := by
  have hmem :
      HomotopyCategory.subcategoryAcyclic AddCommGrpCat
        ((HomotopyCategory.quotient AddCommGrpCat (up ℤ)).obj (CochainComplex.mappingCone f)) :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (C := AddCommGrpCat) (CochainComplex.mappingCone f)).2 hCone
  have hq :
      HomotopyCategory.quasiIso AddCommGrpCat (up ℤ)
        ((HomotopyCategory.quotient AddCommGrpCat (up ℤ)).map f) := by
    -- The standard mapping-cone triangle turns cone acyclicity into the `trW` witness.
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := AddCommGrpCat)] using
      ((HomotopyCategory.subcategoryAcyclic AddCommGrpCat).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).2 hmem
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff
    (C := AddCommGrpCat) (c := up ℤ) f).1 hq

/-- Helper for Chap12 Lemma 12 26 4: the mapping cone of a quasi-isomorphism of cochain
complexes of abelian groups is acyclic. -/
private theorem mappingCone_acyclic_of_quasiIso
    {L M : AbCochainComplex} (f : L ⟶ M) (hf : QuasiIso f) :
    (CochainComplex.mappingCone f).Acyclic := by
  -- Pass to the homotopy category, where the standard mapping-cone triangle detects
  -- quasi-isomorphisms through the acyclic subcategory.
  have hq :
      HomotopyCategory.quasiIso AddCommGrpCat (up ℤ)
        ((HomotopyCategory.quotient AddCommGrpCat (up ℤ)).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff
      (C := AddCommGrpCat) (c := up ℤ) f).2 hf
  have hq' :
      (HomotopyCategory.subcategoryAcyclic AddCommGrpCat).trW
        ((HomotopyCategory.quotient AddCommGrpCat (up ℤ)).map f) := by
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := AddCommGrpCat)] using hq
  have hmem :
      HomotopyCategory.subcategoryAcyclic AddCommGrpCat
        ((HomotopyCategory.quotient AddCommGrpCat (up ℤ)).obj (CochainComplex.mappingCone f)) := by
    -- The mapping-cone triangle packages the cone as the `trW` witness of `f`.
    simpa using
      ((HomotopyCategory.subcategoryAcyclic AddCommGrpCat).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 hq'
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (C := AddCommGrpCat) (CochainComplex.mappingCone f)).1 hmem

/-- Helper for Chap12 Lemma 12 26 4: taking degree `n` of a categorical inverse limit of
cochain complexes agrees with the inverse limit of the degree-`n` evaluation tower. -/
private noncomputable def limitDegreeIso
    {J : Type*} [Category J] (F : J ⥤ AbCochainComplex) (n : ℤ) :
    (limit F).X n ≅ limit (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n) :=
  (isLimitOfPreserves (HomologicalComplex.eval AddCommGrpCat (up ℤ) n) (limit.isLimit F))
    .conePointUniqueUpToIso
      (limit.isLimit (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n))

/-- Helper for Chap12 Lemma 12 26 4: under `limitDegreeIso`, the projection to a stage is exactly
the evaluated limit projection at that degree. -/
private theorem limitDegreeIso_hom_π
    {J : Type*} [Category J] (F : J ⥤ AbCochainComplex) (n : ℤ) (j : J) :
    (limitDegreeIso F n).hom ≫
        limit.π (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n) j =
      (limit.π F j).f n := by
  -- This is the preserved-limit universal property specialized to the evaluation functor.
  simpa [limitDegreeIso] using
    (isLimitOfPreserves (HomologicalComplex.eval AddCommGrpCat (up ℤ) n) (limit.isLimit F))
      .conePointUniqueUpToIso_hom_comp
      (limit.isLimit (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n)) j

/-- Helper for Chap12 Lemma 12 26 4: the inverse of `limitDegreeIso` recovers the evaluated stage
projection. -/
private theorem limitDegreeIso_inv_π
    {J : Type*} [Category J] (F : J ⥤ AbCochainComplex) (n : ℤ) (j : J) :
    (limitDegreeIso F n).inv ≫ (limit.π F j).f n =
      limit.π (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n) j := by
  -- Proof comment: this is the inverse projection formula dual to `limitDegreeIso_hom_π`.
  simpa [limitDegreeIso] using
    (isLimitOfPreserves (HomologicalComplex.eval AddCommGrpCat (up ℤ) n) (limit.isLimit F))
      .conePointUniqueUpToIso_inv_comp
      (limit.isLimit (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) n)) j

/-- Helper for Chap12 Lemma 12 26 4: degree-`n` elements of a limit of cochain complexes are
determined by all of their stagewise projections. -/
private theorem limitDegree_ext
    {J : Type*} [Category J] (F : J ⥤ AbCochainComplex) (n : ℤ)
    {x y : (limit F).X n}
    (h : ∀ j : J, ((limit.π F j).f n) x = ((limit.π F j).f n) y) :
    x = y := by
  -- Transport to the limit of evaluated degree terms, where `limit.hom_ext` reduces equality
  -- to the stagewise coordinates.
  apply (limitDegreeIso F n).hom.injective
  apply limit.hom_ext
  intro j
  simpa [limitDegreeIso_hom_π] using h j

/-- Helper for Chap12 Lemma 12 26 4: a point of an inverse limit of abelian groups determines the
corresponding compatible family in the underlying `Type`-valued diagram. -/
private noncomputable def underlyingSectionsOfLimit
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat) (x : ↑(limit F)) :
    (F ⋙ forget AddCommGrpCat).sections :=
  Types.limitEquivSections _ ((preservesLimitIso (forget AddCommGrpCat) F).hom x)

/-- Helper for Chap12 Lemma 12 26 4: a limit point is determined by its underlying compatible
family. -/
private theorem underlyingSectionsOfLimit_injective
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat) :
    Function.Injective (underlyingSectionsOfLimit F) := by
  intro x y hxy
  -- Compare the underlying `Type`-valued limit points and transport back through the preserved
  -- limit isomorphism for `forget AddCommGrpCat`.
  have hlimit :
      (preservesLimitIso (forget AddCommGrpCat) F).hom x =
        (preservesLimitIso (forget AddCommGrpCat) F).hom y := by
    exact (Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).injective hxy
  simpa using congrArg ((preservesLimitIso (forget AddCommGrpCat) F).inv) hlimit

/-- Helper for Chap12 Lemma 12 26 4: a compatible family in the underlying `Type`-valued diagram
of abelian groups defines a point of the categorical inverse limit. -/
private noncomputable def limitOfUnderlyingSections
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    (s : (F ⋙ forget AddCommGrpCat).sections) :
    ↑(limit F) :=
  (preservesLimitIso (forget AddCommGrpCat) F).inv
    ((Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s)

/-- Helper for Chap12 Lemma 12 26 4: reading off the section attached to a limit point recovers
each categorical limit projection. -/
private theorem limit_π_underlyingSectionsOfLimit
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat) (x : ↑(limit F)) (j : J) :
    limit.π F j x = (underlyingSectionsOfLimit F x).val j := by
  -- First move to the underlying `Type`-valued limit, then read off the corresponding section.
  let t : limit (F ⋙ forget AddCommGrpCat) :=
    (preservesLimitIso (forget AddCommGrpCat) F).hom x
  have hπ :
      limit.π F j x = limit.π (F ⋙ forget AddCommGrpCat) j t := by
    exact congrArg (fun k ↦ k x) (preservesLimitIso_hom_π (forget AddCommGrpCat) F j)
  have hsections :
      limit.π (F ⋙ forget AddCommGrpCat) j t = (underlyingSectionsOfLimit F x).val j := by
    simpa [underlyingSectionsOfLimit, t] using
      Types.limitEquivSections_symm_apply (F ⋙ forget AddCommGrpCat)
        (underlyingSectionsOfLimit F x) j
  exact hπ.trans hsections

/-- Helper for Chap12 Lemma 12 26 4: the limit point reconstructed from an underlying compatible
family has the expected coordinate at every stage. -/
private theorem limit_π_limitOfUnderlyingSections
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    (s : (F ⋙ forget AddCommGrpCat).sections) (j : J) :
    limit.π F j (limitOfUnderlyingSections F s) = s.val j := by
  -- Pass through the underlying `Type`-valued limit and then evaluate the chosen section.
  let t : limit (F ⋙ forget AddCommGrpCat) :=
    (Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s
  have hπ :
      limit.π F j ((preservesLimitIso (forget AddCommGrpCat) F).inv t) =
        limit.π (F ⋙ forget AddCommGrpCat) j t := by
    exact congrArg (fun k ↦ k t) (preservesLimitIso_inv_π (forget AddCommGrpCat) F j)
  simpa [limitOfUnderlyingSections, t] using
    hπ.trans (Types.limitEquivSections_symm_apply (F ⋙ forget AddCommGrpCat) s j)

/-- Helper for Chap12 Lemma 12 26 4: if every stage of a countable inverse system of abelian
groups is connected by surjective transition maps, then the system is Mittag-Leffler. -/
private theorem orderDualNat_isMittagLeffler_of_surjective
    (F : OrderDual ℕ ⥤ AddCommGrpCat)
    (hsurj : ∀ ⦃i j : OrderDual ℕ⦄ (f : i ⟶ j),
      Function.Surjective ((F.map f).hom)) :
    (F ⋙ forget AddCommGrpCat).IsMittagLeffler := by
  -- The owner theorem applies directly once every transition map is surjective.
  exact Functor.isMittagLeffler_of_surjective (F := F ⋙ forget AddCommGrpCat)
    (fun f ↦ hsurj f)

/-- Helper for Chap12 Lemma 12 26 4: if every transition map in an `OrderDual ℕ`-tower of
abelian groups is surjective, then every projection from the inverse limit is surjective. -/
private theorem orderDualNat_limitProjection_surjective_of_surjective
    (F : OrderDual ℕ ⥤ AddCommGrpCat)
    (hsurj : ∀ ⦃i j : OrderDual ℕ⦄ (f : i ⟶ j),
      Function.Surjective ((F.map f).hom))
    (j : OrderDual ℕ) :
    Function.Surjective ((limit.π F j).hom) := by
  classical
  let G := F ⋙ forget AddCommGrpCat
  have hML : G.IsMittagLeffler := by
    -- Surjective transition maps are exactly the owner criterion for the Mittag-Leffler
    -- condition on the underlying set-valued tower.
    exact orderDualNat_isMittagLeffler_of_surjective F hsurj
  intro x
  let s : Set (G.obj j) := Set.singleton x
  haveI :
      ∀ k : OrderDual ℕ, Nonempty ((G.toPreimages s).obj k) := by
    intro k
    exact G.toPreimages_nonempty_of_surjective s
      (fun _ _ f ↦ hsurj f)
      (Set.singleton_nonempty x) k
  obtain ⟨sec, hsec⟩ :=
    nonempty_sections_of_countable_mittagLeffler_inverse_system (A := G.toPreimages s)
      (Functor.IsMittagLeffler.toPreimages (F := G) (s := s) hML)
  let secG : G.sections :=
    ⟨fun k ↦ (sec k).1, fun f ↦ congrArg Subtype.val (hsec f)⟩
  let y : limit G := (Types.limitEquivSections G).symm secG
  have hmem : (sec j).1 = x := by
    -- The section through the preimage tower is forced to land in the singleton target at stage
    -- `j`.
    have hsecMem : (sec j).1 ∈ ⋂ f : j ⟶ j, G.map f ⁻¹' s := by
      simpa [Functor.toPreimages_obj] using (sec j).2
    rw [Set.mem_iInter] at hsecMem
    simpa [s] using hsecMem (𝟙 j)
  have hy :
      limit.π G j y = x := by
    -- Evaluating the chosen compatible family at stage `j` recovers the prescribed target point.
    have hsec' :
        limit.π G j y = secG j := by
      simpa [y] using
        (Types.limitEquivSections_symm_apply (F := G) (x := secG) (j := j))
    exact hsec'.trans hmem
  refine ⟨(preservesLimitIso (forget AddCommGrpCat) F).inv y, ?_⟩
  -- Translate the underlying-set coordinate computation back to the categorical limit.
  change
    ((forget AddCommGrpCat).map (limit.π F j))
      ((preservesLimitIso (forget AddCommGrpCat) F).inv y) = x
  have hπ' :
      ((forget AddCommGrpCat).map (limit.π F j))
          ((preservesLimitIso (forget AddCommGrpCat) F).inv y) =
        limit.π G j y := by
    simpa using
      congrArg
        (fun g ↦ g ((preservesLimitIso (forget AddCommGrpCat) F).inv y))
        (preservesLimitIso_hom_π
          (G := forget AddCommGrpCat) (F := F) (j := j)).symm
  exact hπ'.trans hy

/-- Helper for Chap12 Lemma 12 26 4: a cocycle-lifting criterion implies exactness at a fixed
degree of an inverse limit complex. -/
private theorem limitExactAtOfCocyclePrimitives
    {J : Type*} [Category J] (F : J ⥤ AbCochainComplex) (n : ℤ)
    (hprim :
      ∀ x : (limit F).X n, ((limit F).d n (n + 1)) x = 0 →
        ∃ y : (limit F).X (n - 1), ((limit F).d (n - 1) n) y = x) :
    (limit F).ExactAt n := by
  -- Rewrite exactness into the explicit elementwise lifting criterion for abelian groups.
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_of_hasForget]
  intro x hx
  -- The assumed primitive one degree lower closes the exactness witness immediately.
  exact hprim x hx

/-- Helper for Chap12 Lemma 12 26 4: if every cocycle in the inverse limit has a primitive one
degree lower, then the inverse limit complex is acyclic. -/
private theorem limitAcyclicOfCocyclePrimitives
    {J : Type*} [Category J] (F : J ⥤ AbCochainComplex)
    (hprim :
      ∀ n : ℤ, ∀ x : (limit F).X n, ((limit F).d n (n + 1)) x = 0 →
        ∃ y : (limit F).X (n - 1), ((limit F).d (n - 1) n) y = x) :
    (limit F).Acyclic := by
  -- Acyclicity is exactness degreewise, so apply the previous lifting criterion at each degree.
  rw [HomologicalComplex.acyclic_iff]
  intro n
  exact limitExactAtOfCocyclePrimitives F n (hprim n)

end

section

-- Proof sketch: pass from complexes of abelian groups to the opposite category, where countable
-- products become countable coproducts and the product total complex becomes the unop of the
-- canonical coproduct total of the opposite bicomplex. The exact augmented row then becomes a
-- coaugmented exact row in the opposite category, and the product-total quasi-isomorphism follows
-- from the corresponding coproduct-total result by transporting back across opposites.
local notation "AbCochainComplex" => CochainComplex AddCommGrpCat ℤ
local notation "AbCochainResolution" => ChainComplex AbCochainComplex ℕ

/-- Helper for Lemma 12.26.4: a quasi-isomorphism on the opposite-side comparison map transports
back to the source-facing product-total comparison via `CochainComplex.opEquivalence`. -/
private theorem productTotalToTarget_quasiIso_of_op
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hOp : QuasiIso (productTotalToTargetOp A π hπ)) :
    QuasiIso (productTotalToTarget A π hπ) := by
  -- Transport the opposite-side quasi-isomorphism back through the unop functor.
  have hUnop :
      QuasiIso
        ((((CochainComplex.opEquivalence AddCommGrpCat).inverse.map
            (productTotalToTargetOp A π hπ))).unop) := by
    simpa [productTotalTargetOp, CochainComplex.opEquivalence,
      ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence] using
      (HomologicalComplex.quasiIso_unopFunctor_map_iff
        (φ := productTotalToTargetOp A π hπ)).2 hOp
  -- The remaining factor is the unit isomorphism identifying the transported target with `M`.
  have hUnit :
      QuasiIso
        ((((CochainComplex.opEquivalence AddCommGrpCat).unitIso.app (op M)).unop).hom) := by
    infer_instance
  letI :
      QuasiIso
        ((((CochainComplex.opEquivalence AddCommGrpCat).inverse.map
            (productTotalToTargetOp A π hπ))).unop) := hUnop
  letI :
      QuasiIso
        ((((CochainComplex.opEquivalence AddCommGrpCat).unitIso.app (op M)).unop).hom) := hUnit
  -- The source-facing map is exactly the transported opposite map followed by that unit isomorphism.
  simpa [productTotalToTarget] using
    (inferInstance :
      QuasiIso
        ((((CochainComplex.opEquivalence AddCommGrpCat).inverse.map
            (productTotalToTargetOp A π hπ))).unop ≫
          (((CochainComplex.opEquivalence AddCommGrpCat).unitIso.app (op M)).unop).hom))

/-- Helper for Lemma 12.26.4: finite antidiagonal support means that in each total degree only
finitely many columns can contribute nonzero summands. -/
private abbrev doubleComplexHasFiniteAntidiagonalSupport
    (K : HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)) : Prop :=
  ∀ n : ℤ, { p : ℤ | ¬ IsZero ((K.X p).X (n - p)) }.Finite

/-- Helper for Lemma 12.26.4: if `t ≤ i`, then the retained degree `i` lies in the image of the
lower brutal truncation embedding `n ↦ t + n`. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (t i : ℤ) (hti : t ≤ i) :
    (ComplexShape.embeddingUpIntGE t).f (Int.toNat (i - t)) = i := by
  -- The retained range witness is the nonnegative difference `i - t`.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 12.26.4: in a retained degree, the lower brutal truncation term is
canonically identified with the original term. -/
private noncomputable def lowerStupidTruncationXIso
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t i : ℤ) (hti : t ≤ i) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X i ≅ K.X i :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntGE t)
    (embeddingUpIntGE_toNat_sub_eq t i hti)

/-- Helper for Lemma 12.26.4: the degreewise components of the canonical map from the lower
brutal truncation into the original complex. -/
private noncomputable def lowerStupidTruncationInclusionF
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t i : ℤ) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X i ⟶ K.X i :=
  if hti : t ≤ i then
    (lowerStupidTruncationXIso K t i hti).hom
  else
    0

/-- Helper for Lemma 12.26.4: in retained degrees, the lower-truncation inclusion component is the
canonical identification with the original term. -/
private theorem lowerStupidTruncationInclusionF_of_ge
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t : ℤ) {i : ℤ} (hti : t ≤ i) :
    lowerStupidTruncationInclusionF K t i =
      (lowerStupidTruncationXIso K t i hti).hom := by
  -- The active branch of the component definition is exactly the retained-degree isomorphism.
  simp [lowerStupidTruncationInclusionF, hti]

/-- Helper for Lemma 12.26.4: the componentwise lower-truncation inclusion is a chain map. -/
private theorem lowerStupidTruncationInclusion_comm
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t : ℤ) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      lowerStupidTruncationInclusionF K t i ≫ K.d i j =
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
          lowerStupidTruncationInclusionF K t j := by
  intro i j hij
  by_cases hti : t ≤ i
  · have htj : t ≤ j := by
      have hj : j = i + 1 := by
        simpa [ComplexShape.up, eq_comm] using hij
      omega
    -- On retained degrees, both truncation terms identify with the original ones.
    rw [lowerStupidTruncationInclusionF_of_ge K t hti,
      lowerStupidTruncationInclusionF_of_ge K t htj]
    let hq : (ComplexShape.embeddingUpIntGE t).f (Int.toNat (i - t)) = i :=
      embeddingUpIntGE_toNat_sub_eq t i hti
    have hd :
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
            (lowerStupidTruncationXIso K t j htj).hom =
          (lowerStupidTruncationXIso K t i hti).hom ≫ K.d i j := by
      -- The retained differential is the functorial truncation of the original differential.
      simpa [lowerStupidTruncationXIso, hq] using
        (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
          (K := K) (L := K) (φ := K.d i j)
          (e := ComplexShape.embeddingUpIntGE t) hq)
    calc
      (lowerStupidTruncationXIso K t i hti).hom ≫ K.d i j =
          (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
            (lowerStupidTruncationXIso K t j htj).hom := by
            simpa using hd.symm
  · have hzero :
        IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X i) := by
      -- Below the cutoff, the source term of the truncation vanishes.
      exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) i
        (by
          simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
            lt_of_not_ge hti)
    by_cases htj : t ≤ j
    · have hsrczero :
          (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j = 0 :=
        hzero.eq_of_src ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j) 0
      -- Once the source object is zero, the commutativity square is trivial.
      simp [lowerStupidTruncationInclusionF, hti, htj, hsrczero]
    · -- If both degrees are discarded, every term in the square is already zero.
      simp [lowerStupidTruncationInclusionF, hti, htj]

/-- Helper for Lemma 12.26.4: the lower brutal truncation has a canonical inclusion into the
original complex. -/
private noncomputable def lowerStupidTruncationInclusion
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE t) ⟶ K :=
  { f := fun i ↦ lowerStupidTruncationInclusionF K t i
    comm' := lowerStupidTruncationInclusion_comm K t }

/-- Helper for Lemma 12.26.4: the functorial map induced on lower brutal truncations. -/
private noncomputable abbrev lowerStupidTruncationMap
    {K L : CochainComplex AddCommGrpCatᵒᵖ ℤ} (f : K ⟶ L) (t : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE t) ⟶
      L.stupidTrunc (ComplexShape.embeddingUpIntGE t) :=
  HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE t)

/-- Helper for Lemma 12.26.4: the lower-truncation inclusion is natural in the complex. -/
private theorem lowerStupidTruncationMapCompInclusion
    {K L : CochainComplex AddCommGrpCatᵒᵖ ℤ} (f : K ⟶ L) (t : ℤ) :
    lowerStupidTruncationMap f t ≫ lowerStupidTruncationInclusion L t =
      lowerStupidTruncationInclusion K t ≫ f := by
  ext i
  by_cases hti : t ≤ i
  · -- On retained degrees, both inclusions are the canonical identifications with degree `i`.
    let hi : (ComplexShape.embeddingUpIntGE t).f (Int.toNat (i - t)) = i :=
      embeddingUpIntGE_toNat_sub_eq t i hti
    simpa [lowerStupidTruncationMap, lowerStupidTruncationInclusion,
      lowerStupidTruncationInclusionF_of_ge, lowerStupidTruncationXIso, hi] using
      (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
        (K := K) (L := L) (φ := f) (e := ComplexShape.embeddingUpIntGE t) hi)
  · -- Below the cutoff, both inclusion components vanish, so the square is trivial.
    simp [lowerStupidTruncationMap, lowerStupidTruncationInclusion,
      lowerStupidTruncationInclusionF, hti]

/-- Helper for Lemma 12.26.4: the lower-truncation inclusions assemble into a natural
transformation from the truncation functor to the identity functor. -/
private noncomputable def lowerStupidTruncationInclusionNatTrans (t : ℤ) :
    (ComplexShape.embeddingUpIntGE t).stupidTruncFunctor AddCommGrpCatᵒᵖ ⟶
      𝟭 (CochainComplex AddCommGrpCatᵒᵖ ℤ) where
  app K := lowerStupidTruncationInclusion K t
  naturality := by
    intro K L f
    simpa [ComplexShape.Embedding.stupidTruncFunctor] using
      lowerStupidTruncationMapCompInclusion (K := K) (L := L) f t

/-- Helper for Chap12 Lemma 12 26 4: if `t₁ ≤ t₂`, then the later cutoff stage
`σ_{\ge t₂} K` includes into the earlier cutoff stage `σ_{\ge t₁} K`. -/
private noncomputable def lowerStupidTruncationComparisonF
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂) (i : ℤ) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).X i ⟶
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₁)).X i :=
  if hti : t₂ ≤ i then
    (lowerStupidTruncationXIso K t₂ i hti).hom ≫
      (lowerStupidTruncationXIso K t₁ i (le_trans ht hti)).inv
  else
    0

/-- Helper for Chap12 Lemma 12 26 4: in retained degrees, the stage-to-stage comparison is the
obvious identification through the ambient term `K.X i`. -/
private theorem lowerStupidTruncationComparisonF_of_ge
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂)
    {i : ℤ} (hti : t₂ ≤ i) :
    lowerStupidTruncationComparisonF K t₁ t₂ ht i =
      (lowerStupidTruncationXIso K t₂ i hti).hom ≫
        (lowerStupidTruncationXIso K t₁ i (le_trans ht hti)).inv := by
  -- In a retained degree, the comparison is exactly the ambient identification.
  simp [lowerStupidTruncationComparisonF, hti]

/-- Helper for Chap12 Lemma 12 26 4: degreewise, the stage-to-stage comparison has the obvious
retraction obtained by forgetting the extra degrees introduced below the later cutoff. -/
private noncomputable def lowerStupidTruncationComparisonFRetraction
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂) (i : ℤ) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₁)).X i ⟶
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).X i :=
  if hti : t₂ ≤ i then
    (lowerStupidTruncationXIso K t₁ i (le_trans ht hti)).hom ≫
      (lowerStupidTruncationXIso K t₂ i hti).inv
  else
    0

/-- Helper for Chap12 Lemma 12 26 4: in retained degrees, the degreewise retraction of the
stage-to-stage comparison is the ambient identity viewed through the two truncation isomorphisms. -/
private theorem lowerStupidTruncationComparisonFRetraction_of_ge
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂)
    {i : ℤ} (hti : t₂ ≤ i) :
    lowerStupidTruncationComparisonFRetraction K t₁ t₂ ht i =
      (lowerStupidTruncationXIso K t₁ i (le_trans ht hti)).hom ≫
        (lowerStupidTruncationXIso K t₂ i hti).inv := by
  -- In a retained degree, the retraction is exactly the ambient identity in the reverse direction.
  simp [lowerStupidTruncationComparisonFRetraction, hti]

/-- Helper for Chap12 Lemma 12 26 4: degreewise, the stage-to-stage comparison becomes split
surjective after unop because its component retraction simply discards the newly introduced cutoff
degree. -/
private theorem lowerStupidTruncationComparisonF_comp_retraction
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂) (i : ℤ) :
    lowerStupidTruncationComparisonF K t₁ t₂ ht i ≫
        lowerStupidTruncationComparisonFRetraction K t₁ t₂ ht i =
      𝟙 ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).X i) := by
  by_cases hti : t₂ ≤ i
  · -- Above the later cutoff, both maps are the identity on the ambient degree `K.X i`.
    rw [lowerStupidTruncationComparisonF_of_ge K t₁ t₂ ht hti,
      lowerStupidTruncationComparisonFRetraction_of_ge K t₁ t₂ ht hti]
    simp [Category.assoc]
  · have hzero :
        IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).X i) := by
      -- Below the later cutoff, the source term already vanishes.
      exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t₂) i
        (by
          simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
            lt_of_not_ge hti)
    have hid :
        (𝟙 ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).X i)) = 0 := by
      simpa using hzero.eq_of_src (𝟙 ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).X i)) 0
    -- Once the source term is zero, both the comparison and its retraction are forced to vanish.
    simp [lowerStupidTruncationComparisonF, lowerStupidTruncationComparisonFRetraction, hti, hid]

/-- Helper for Chap12 Lemma 12 26 4: after unop, each degree component of the lower-truncation
comparison is surjective on the underlying abelian groups. -/
private theorem lowerStupidTruncationComparisonF_unop_surjective
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂) (i : ℤ) :
    Function.Surjective
      ((Quiver.Hom.unop (lowerStupidTruncationComparisonF K t₁ t₂ ht i)).hom) := by
  intro x
  refine ⟨((Quiver.Hom.unop
      (lowerStupidTruncationComparisonFRetraction K t₁ t₂ ht i)).hom x), ?_⟩
  -- Unop reverses the split identity above, so the chosen retraction gives a preimage of `x`.
  have hsplit :=
    congrArg Quiver.Hom.unop
      (lowerStupidTruncationComparisonF_comp_retraction K t₁ t₂ ht i)
  exact congrArg (fun f ↦ f.hom x) hsplit

/-- Helper for Chap12 Lemma 12 26 4: the cutoff-stage comparison is a chain map. This is the
correct stage-to-stage structure; the opposite-direction “projection” across the cutoff is not a
chain map because of the differential crossing degree `t₂ - 1 ⟶ t₂`. -/
private theorem lowerStupidTruncationComparison_comm
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      lowerStupidTruncationComparisonF K t₁ t₂ ht i ≫
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₁)).d i j =
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).d i j ≫
        lowerStupidTruncationComparisonF K t₁ t₂ ht j := by
  intro i j hij
  by_cases hti : t₂ ≤ i
  · have htj : t₂ ≤ j := by
      have hj : j = i + 1 := by
        simpa [ComplexShape.up, eq_comm] using hij
      omega
    let e₁i := lowerStupidTruncationXIso K t₁ i (le_trans ht hti)
    let e₁j := lowerStupidTruncationXIso K t₁ j (le_trans ht htj)
    let e₂i := lowerStupidTruncationXIso K t₂ i hti
    let e₂j := lowerStupidTruncationXIso K t₂ j htj
    have hd₁ :
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₁)).d i j ≫ e₁j.hom =
          e₁i.hom ≫ K.d i j := by
      simpa [e₁i, e₁j] using
        lowerStupidTruncationInclusion_comm K t₁ i j hij
    have hd₂ :
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).d i j ≫ e₂j.hom =
          e₂i.hom ≫ K.d i j := by
      simpa [e₂i, e₂j] using
        lowerStupidTruncationInclusion_comm K t₂ i j hij
    -- Compare both sides after composing with the retained-degree identification in stage `t₁`.
    apply (cancel_mono e₁j.hom).1
    calc
      lowerStupidTruncationComparisonF K t₁ t₂ ht i ≫
          (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₁)).d i j ≫
            e₁j.hom =
        e₂i.hom ≫ K.d i j := by
          rw [lowerStupidTruncationComparisonF_of_ge K t₁ t₂ ht hti, hd₁]
          simp [e₁i, Category.assoc]
      _ = (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).d i j ≫ e₂j.hom := by
          simpa [e₂i, e₂j] using hd₂.symm
      _ =
          (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).d i j ≫
            lowerStupidTruncationComparisonF K t₁ t₂ ht j ≫
              e₁j.hom := by
          rw [lowerStupidTruncationComparisonF_of_ge K t₁ t₂ ht htj]
          simp [e₁j, e₂j, Category.assoc]
  · have hzero :
        IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).X i) := by
      -- Below the later cutoff, the source term of the stage comparison vanishes.
      exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t₂) i
        (by
          simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
            lt_of_not_ge hti)
    have hsrczero :
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).d i j = 0 :=
      hzero.eq_of_src ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂)).d i j) 0
    by_cases htj : t₂ ≤ j
    · -- Once the stage-`t₂` source term is zero, the square is forced to commute.
      simp [lowerStupidTruncationComparisonF, hti, htj, hsrczero]
    · -- If the target is also discarded, every term already vanishes.
      simp [lowerStupidTruncationComparisonF, hti, htj, hsrczero]

/-- Helper for Chap12 Lemma 12 26 4: the stage-to-stage comparison assembles into a morphism of
cochain complexes. The cutoff stages therefore form a direct system by inclusions. -/
private noncomputable def lowerStupidTruncationComparison
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE t₂) ⟶
      K.stupidTrunc (ComplexShape.embeddingUpIntGE t₁) :=
  { f := fun i ↦ lowerStupidTruncationComparisonF K t₁ t₂ ht i
    comm' := lowerStupidTruncationComparison_comm K t₁ t₂ ht }

/-- Helper for Chap12 Lemma 12 26 4: composing the stage-to-stage comparison with the earlier
stage inclusion recovers the later stage inclusion into the ambient complex. -/
private theorem lowerStupidTruncationComparisonCompInclusion
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂) :
    lowerStupidTruncationComparison K t₁ t₂ ht ≫ lowerStupidTruncationInclusion K t₁ =
      lowerStupidTruncationInclusion K t₂ := by
  ext i
  by_cases hti : t₂ ≤ i
  · have ht₁i : t₁ ≤ i := le_trans ht hti
    -- In retained degrees, both routes are the same ambient identification.
    rw [lowerStupidTruncationComparisonF_of_ge K t₁ t₂ ht hti,
      lowerStupidTruncationInclusionF_of_ge K t₁ ht₁i,
      lowerStupidTruncationInclusionF_of_ge K t₂ hti]
    simp [Category.assoc]
  · have h₂i : lowerStupidTruncationInclusionF K t₂ i = 0 := by
      simp [lowerStupidTruncationInclusionF, hti]
    -- Below the later cutoff, the later stage already vanishes, so both composites are zero.
    simp [lowerStupidTruncationComparison, lowerStupidTruncationComparisonF,
      lowerStupidTruncationInclusion, hti, h₂i]

/-- Helper for Chap12 Lemma 12 26 4: the stage-to-stage comparison is natural in the ambient
complex map. This is the bicomplex-row compatibility needed for the stage-cone tower. -/
private theorem lowerStupidTruncationMapCompComparison
    {K L : CochainComplex AddCommGrpCatᵒᵖ ℤ} (f : K ⟶ L)
    (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂) :
    lowerStupidTruncationMap f t₂ ≫ lowerStupidTruncationComparison L t₁ t₂ ht =
      lowerStupidTruncationComparison K t₁ t₂ ht ≫ lowerStupidTruncationMap f t₁ := by
  ext i
  by_cases hti : t₂ ≤ i
  · have ht₁i : t₁ ≤ i := le_trans ht hti
    let hi₂ : (ComplexShape.embeddingUpIntGE t₂).f (Int.toNat (i - t₂)) = i :=
      embeddingUpIntGE_toNat_sub_eq t₂ i hti
    let hi₁ : (ComplexShape.embeddingUpIntGE t₁).f (Int.toNat (i - t₁)) = i :=
      embeddingUpIntGE_toNat_sub_eq t₁ i ht₁i
    let e₂K := lowerStupidTruncationXIso K t₂ i hti
    let e₂L := lowerStupidTruncationXIso L t₂ i hti
    let e₁K := lowerStupidTruncationXIso K t₁ i ht₁i
    let e₁L := lowerStupidTruncationXIso L t₁ i ht₁i
    have hmap₂ :
        (lowerStupidTruncationMap f t₂).f i ≫ e₂L.hom =
          e₂K.hom ≫ f.f i := by
      -- On retained degree `i`, truncation functoriality is the ambient map through the row
      -- identifications at cutoff `t₂`.
      simpa [lowerStupidTruncationMap, e₂K, e₂L, hi₂] using
        (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
          (K := K) (L := L) (φ := f) (e := ComplexShape.embeddingUpIntGE t₂) hi₂)
    have hmap₁ :
        (lowerStupidTruncationMap f t₁).f i ≫ e₁L.hom =
          e₁K.hom ≫ f.f i := by
      -- The same retained-degree normalization holds at the earlier cutoff `t₁`.
      simpa [lowerStupidTruncationMap, e₁K, e₁L, hi₁] using
        (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
          (K := K) (L := L) (φ := f) (e := ComplexShape.embeddingUpIntGE t₁) hi₁)
    apply (cancel_mono e₁L.hom).1
    -- Compare both routes after identifying the degree-`i` target with the ambient object `L.X i`.
    calc
      (lowerStupidTruncationMap f t₂).f i ≫
          (lowerStupidTruncationComparison L t₁ t₂ ht).f i ≫
            e₁L.hom =
        (lowerStupidTruncationMap f t₂).f i ≫ e₂L.hom := by
          rw [lowerStupidTruncationComparisonF_of_ge L t₁ t₂ ht hti]
          simp [e₂L, e₁L, Category.assoc]
      _ = e₂K.hom ≫ f.f i := by
          exact hmap₂
      _ = e₂K.hom ≫ e₁K.inv ≫ e₁K.hom ≫ f.f i := by
          simp [Category.assoc]
      _ =
        (lowerStupidTruncationComparison K t₁ t₂ ht).f i ≫
          ((lowerStupidTruncationMap f t₁).f i ≫ e₁L.hom) := by
          rw [lowerStupidTruncationComparisonF_of_ge K t₁ t₂ ht hti]
          simp [e₂K, e₁K, Category.assoc]
      _ =
        (lowerStupidTruncationComparison K t₁ t₂ ht).f i ≫
          (lowerStupidTruncationMap f t₁).f i ≫ e₁L.hom := by
          simp [Category.assoc]
      _ =
        ((lowerStupidTruncationComparison K t₁ t₂ ht).f i ≫
          (lowerStupidTruncationMap f t₁).f i) ≫ e₁L.hom := by
          simp [Category.assoc]
  · -- Below the later cutoff, the source stage vanishes, so both component maps are zero.
    simp [lowerStupidTruncationMap, lowerStupidTruncationComparison,
      lowerStupidTruncationComparisonF, hti]

/-- Helper for Chap12 Lemma 12 26 4: stage-to-stage comparisons compose transitively along the
cutoff parameter. -/
private theorem lowerStupidTruncationComparison_comp
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ)
    (t₁ t₂ t₃ : ℤ) (h₁₂ : t₁ ≤ t₂) (h₂₃ : t₂ ≤ t₃) :
    lowerStupidTruncationComparison K t₂ t₃ h₂₃ ≫
      lowerStupidTruncationComparison K t₁ t₂ h₁₂ =
        lowerStupidTruncationComparison K t₁ t₃ (le_trans h₁₂ h₂₃) := by
  ext i
  by_cases hti : t₃ ≤ i
  · have h₂i : t₂ ≤ i := le_trans h₂₃ hti
    have h₁i : t₁ ≤ i := le_trans h₁₂ h₂i
    rw [lowerStupidTruncationComparisonF_of_ge K t₂ t₃ h₂₃ hti,
      lowerStupidTruncationComparisonF_of_ge K t₁ t₂ h₁₂ h₂i,
      lowerStupidTruncationComparisonF_of_ge K t₁ t₃ (le_trans h₁₂ h₂₃) hti]
    -- In retained degrees, every stage identifies with `K.X i`, so the comparisons collapse.
    simp [Category.assoc]
  · -- If the latest stage discards degree `i`, every comparison component out of that stage is zero.
    simp [lowerStupidTruncationComparison, lowerStupidTruncationComparisonF, hti]

/-- Helper for Chap12 Lemma 12 26 4: the stage-to-stage truncation comparisons assemble into a
natural transformation between the rowwise lower-truncation functors. -/
private noncomputable def lowerStupidTruncationComparisonNatTrans
    (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂) :
    (ComplexShape.embeddingUpIntGE t₂).stupidTruncFunctor AddCommGrpCatᵒᵖ ⟶
      (ComplexShape.embeddingUpIntGE t₁).stupidTruncFunctor AddCommGrpCatᵒᵖ where
  app K := lowerStupidTruncationComparison K t₁ t₂ ht
  naturality := by
    intro K L f
    simpa [ComplexShape.Embedding.stupidTruncFunctor] using
      lowerStupidTruncationMapCompComparison f t₁ t₂ ht

/-- Helper for Lemma 12.26.4: below the cutoff, the lower brutal truncation term vanishes. -/
private theorem lowerStupidTruncationXIsZeroOfLt
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (t q : ℤ) (hqt : q < t) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X q) := by
  -- This is the owner vanishing statement for discarded degrees of the brutal truncation.
  exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) q
    (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hqt)

/-- Helper for Lemma 12.26.4: if an entire row is zero, then every term of its lower brutal
truncation is still zero. -/
private theorem lowerStupidTruncationXIsZeroOfRowIsZero
    (K : CochainComplex AddCommGrpCatᵒᵖ ℤ) (hK : IsZero K) (t q : ℤ) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X q) := by
  by_cases htq : t ≤ q
  · -- In retained degrees, identify the truncation term with the original zero row term.
    exact
      ((lowerStupidTruncationXIso K t q htq).isZero_iff).2
        ((HomologicalComplex.eval AddCommGrpCatᵒᵖ (up ℤ) q).map_isZero hK)
  · -- In discarded degrees, the truncation kills the term for formal reasons.
    exact lowerStupidTruncationXIsZeroOfLt K t q (lt_of_not_ge htq)

/-- The opposite bicomplex whose coproduct total models `Tot_π(A)`. -/
private abbrev productTotalOppositeBicomplex
    (A : AbCochainResolution) :
    HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ) :=
  HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)

/-- The rowwise lower brutal truncation of the opposite bicomplex in the vertical degree. -/
private noncomputable abbrev lowerStupidTruncationProductTotalOppositeBicomplex
    (A : AbCochainResolution) (t : ℤ) :
    HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ) :=
  (((ComplexShape.embeddingUpIntGE t).stupidTruncFunctor AddCommGrpCatᵒᵖ).mapHomologicalComplex
    (up ℤ)).obj (productTotalOppositeBicomplex A)

/-- The rowwise lower-truncated source complex on the opposite side. -/
private noncomputable abbrev lowerStupidTruncationProductTotalTargetOp
    (M : AbCochainComplex) (t : ℤ) :
    CochainComplex AddCommGrpCatᵒᵖ ℤ :=
  (productTotalTargetOp M).stupidTrunc (ComplexShape.embeddingUpIntGE t)

/-- Helper for Lemma 12.26.4: the rowwise lower-truncated opposite bicomplex maps canonically to
the full opposite bicomplex. -/
private noncomputable def lowerStupidTruncationProductTotalOppositeBicomplexInclusion
    (A : AbCochainResolution) (t : ℤ) :
    lowerStupidTruncationProductTotalOppositeBicomplex A t ⟶ productTotalOppositeBicomplex A :=
  (NatTrans.mapHomologicalComplex
    (lowerStupidTruncationInclusionNatTrans t) (up ℤ)).app
      (productTotalOppositeBicomplex A)

/-- Helper for Lemma 12.26.4: the stage zero-column comparison is the lower truncation of the
already-constructed zero-column map. -/
private noncomputable abbrev lowerStupidTruncationProductTotalTargetZeroColumnMap
    (A : AbCochainResolution) {M : AbCochainComplex}
    (π : A.X 0 ⟶ M) (t : ℤ) :
    lowerStupidTruncationProductTotalTargetOp M t ⟶
      (lowerStupidTruncationProductTotalOppositeBicomplex A t).X 0 :=
  HomologicalComplex.stupidTruncMap
    (product_total_target_zero_column_map A π)
    (ComplexShape.embeddingUpIntGE t)

/-- Helper for Chap12 Lemma 12 26 4: the lower-truncated zero-column comparison still lands in
the cycles of the first horizontal differential. -/
private theorem lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
    (A : AbCochainResolution) {M : AbCochainComplex}
    (π : A.X 0 ⟶ M) (hπ : A.d 1 0 ≫ π = 0) (t q : ℤ) :
    (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t).f q ≫
        ((lowerStupidTruncationProductTotalOppositeBicomplex A t).d 0 1).f q = 0 := by
  by_cases htq : t ≤ q
  · let hq : (ComplexShape.embeddingUpIntGE t).f (Int.toNat (q - t)) = q :=
      embeddingUpIntGE_toNat_sub_eq t q htq
    let eSrc := lowerStupidTruncationXIso (productTotalTargetOp M) t q htq
    let e₀ := lowerStupidTruncationXIso ((productTotalOppositeBicomplex A).X 0) t q htq
    let e₁ := lowerStupidTruncationXIso ((productTotalOppositeBicomplex A).X 1) t q htq
    have hα :
        (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t).f q ≫ e₀.hom =
          eSrc.hom ≫ (product_total_target_zero_column_map A π).f q := by
      -- The stage map is the functorial truncation of the original zero-column comparison.
      simpa [lowerStupidTruncationProductTotalTargetZeroColumnMap,
        lowerStupidTruncationProductTotalTargetOp,
        lowerStupidTruncationProductTotalOppositeBicomplex,
        productTotalOppositeBicomplex, eSrc, e₀, hq] using
        (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
          (K := productTotalTargetOp M)
          (L := (productTotalOppositeBicomplex A).X 0)
          (φ := product_total_target_zero_column_map A π)
          (e := ComplexShape.embeddingUpIntGE t) hq)
    have hd :
        ((lowerStupidTruncationProductTotalOppositeBicomplex A t).d 0 1).f q ≫ e₁.hom =
          e₀.hom ≫ ((productTotalOppositeBicomplex A).d 0 1).f q := by
      -- The retained horizontal differential is the truncation of the original `0 ⟶ 1` row map.
      simpa [lowerStupidTruncationProductTotalOppositeBicomplex,
        productTotalOppositeBicomplex, e₀, e₁, hq] using
        (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
          (K := (productTotalOppositeBicomplex A).X 0)
          (L := (productTotalOppositeBicomplex A).X 1)
          (φ := (productTotalOppositeBicomplex A).d 0 1)
          (e := ComplexShape.embeddingUpIntGE t) hq)
    apply (cancel_mono e₁.hom).1
    -- After identifying retained terms with the original row, the claim is the old cycle relation.
    calc
      (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t).f q ≫
          ((lowerStupidTruncationProductTotalOppositeBicomplex A t).d 0 1).f q ≫
          e₁.hom =
        (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t).f q ≫
          (e₀.hom ≫ ((productTotalOppositeBicomplex A).d 0 1).f q) := by
            rw [Category.assoc, hd]
      _ =
        ((lowerStupidTruncationProductTotalTargetZeroColumnMap A π t).f q ≫ e₀.hom) ≫
          ((productTotalOppositeBicomplex A).d 0 1).f q := by
            simp [Category.assoc]
      _ =
        (eSrc.hom ≫ (product_total_target_zero_column_map A π).f q) ≫
          ((productTotalOppositeBicomplex A).d 0 1).f q := by
            rw [hα]
      _ =
        eSrc.hom ≫
          ((product_total_target_zero_column_map A π).f q ≫
            ((productTotalOppositeBicomplex A).d 0 1).f q) := by
            simp [Category.assoc]
      _ = 0 := by
            simp [product_total_target_zero_column_map_cycles (A := A) (π := π) hπ q]
  · have hX :
        IsZero ((lowerStupidTruncationProductTotalTargetOp M t).X q) :=
      lowerStupidTruncationXIsZeroOfLt (productTotalTargetOp M) t q (lt_of_not_ge htq)
    -- Below the cutoff the source term vanishes, so every outgoing morphism is zero.
    exact hX.eq_of_src _ _

/-- Helper for Lemma 12.26.4: postcomposing a zero-row comparison with a bicomplex map preserves
the row-cycle relation. -/
private theorem productTotalZeroRow_comp_map_cycles
    {K : CochainComplex AddCommGrpCatᵒᵖ ℤ}
    {B₁ B₂ : HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)}
    (α : K ⟶ ((HomologicalComplex.eval AddCommGrpCatᵒᵖ (up ℤ) (0 : ℤ)).mapHomologicalComplex
      (up ℤ)).obj B₁)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (B₁.X p).d 0 1 = 0)
    (β : B₁ ⟶ B₂) :
    ∀ p : ℤ,
      (α ≫ ((HomologicalComplex.eval AddCommGrpCatᵒᵖ (up ℤ) (0 : ℤ)).mapHomologicalComplex
          (up ℤ)).map β).f p ≫ (B₂.X p).d 0 1 = 0 := by
  intro p
  -- Move the vertical differential across the row map `β.f p`.
  calc
    (α ≫ ((HomologicalComplex.eval AddCommGrpCatᵒᵖ (up ℤ) (0 : ℤ)).mapHomologicalComplex
          (up ℤ)).map β).f p ≫
        (B₂.X p).d 0 1 =
      α.f p ≫ (β.f p).f 0 ≫ (B₂.X p).d 0 1 := by
        rfl
    _ = α.f p ≫ (B₁.X p).d 0 1 ≫ (β.f p).f 1 := by
      rw [Category.assoc, (β.f p).comm 0 1 (by simp)]
    _ = 0 := by
      rw [hαcycles p, zero_comp]

/-- Helper for Lemma 12.26.4: the zero-row comparison into the product total is functorial in the
target bicomplex, with comparison morphism `total.map β`. -/
private theorem productTotalZeroRowToTotal_comp_map
    {K : CochainComplex AddCommGrpCatᵒᵖ ℤ}
    {B₁ B₂ : HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)}
    [B₁.HasTotal (up ℤ)] [B₂.HasTotal (up ℤ)]
    (α : K ⟶ ((HomologicalComplex.eval AddCommGrpCatᵒᵖ (up ℤ) (0 : ℤ)).mapHomologicalComplex
      (up ℤ)).obj B₁)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (B₁.X p).d 0 1 = 0)
    (β : B₁ ⟶ B₂) :
    product_total_zero_row_to_total
        (α ≫ ((HomologicalComplex.eval AddCommGrpCatᵒᵖ (up ℤ) (0 : ℤ)).mapHomologicalComplex
            (up ℤ)).map β)
        (productTotalZeroRow_comp_map_cycles α hαcycles β) =
      product_total_zero_row_to_total α hαcycles ≫ total.map β (up ℤ) := by
  ext n
  -- Both maps are the same inclusion of the `(n,0)` summand followed by `β`.
  simp [product_total_zero_row_to_total, product_total_zero_row_to_total_component, Category.assoc]

/-- Helper for Lemma 12.26.4: the flip symmetry of total complexes is natural in bicomplex maps.
This is the owner-level transport needed to compare stage totalization with the ambient
totalization. -/
private theorem productTotalFlipIso_hom_map_eq
    {B₁ B₂ : HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)}
    [B₁.HasTotal (up ℤ)] [B₂.HasTotal (up ℤ)]
    (φ : B₁ ⟶ B₂) :
    total.map ((flipFunctor AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)).map φ) (up ℤ) ≫
        (B₂.totalFlipIso (up ℤ)).hom =
      (B₁.totalFlipIso (up ℤ)).hom ≫ total.map φ (up ℤ) := by
  -- Compare the two composites on each antidiagonal summand of the flipped total complex.
  ext n
  apply total.hom_ext
  intro q p h
  calc
    B₁.flip.ιTotal (up ℤ) q p n h ≫
        (total.map ((flipFunctor AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)).map φ) (up ℤ)).f n ≫
          (B₂.totalFlipIso (up ℤ)).hom.f n =
      (φ.f p).f q ≫
        (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
          B₂.ιTotal (up ℤ) p q n
            (by rw [← ComplexShape.π_symm (up ℤ) (up ℤ) (up ℤ) p q, h])) := by
      rw [ιTotal_map_assoc, ιTotal_totalFlipIso_f_hom]
      rfl
    _ =
        ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
          ((φ.f p).f q ≫
            B₂.ιTotal (up ℤ) p q n
              (by rw [← ComplexShape.π_symm (up ℤ) (up ℤ) (up ℤ) p q, h])) := by
      rw [Linear.comp_units_smul]
    _ =
        B₁.flip.ιTotal (up ℤ) q p n h ≫
          (B₁.totalFlipIso (up ℤ)).hom.f n ≫ (total.map φ (up ℤ)).f n := by
      rw [ιTotal_totalFlipIso_f_hom_assoc, ιTotal_map]

/-- Helper for Lemma 12.26.4: postcomposing the zero-column comparison with a bicomplex map agrees
with postcomposing the induced total map by `total.map`. -/
private theorem productTotalZeroColumnToTotal_comp_total_map
    {K : CochainComplex AddCommGrpCatᵒᵖ ℤ}
    {B₁ B₂ : HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)}
    [B₁.HasTotal (up ℤ)] [B₂.HasTotal (up ℤ)]
    (α : K ⟶ B₁.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (B₁.d 0 1).f q = 0)
    (φ : B₁ ⟶ B₂)
    (hcompcycles : ∀ q : ℤ, (α ≫ φ.f 0).f q ≫ (B₂.d 0 1).f q = 0) :
    product_total_zero_column_to_total (α ≫ φ.f 0) hcompcycles =
      product_total_zero_column_to_total α hαcycles ≫ total.map φ (up ℤ) := by
  let φflip := (flipFunctor AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)).map φ
  have hflip_map :
      product_total_zero_column_to_zero_row_flip (α ≫ φ.f 0) =
        product_total_zero_column_to_zero_row_flip α ≫
          ((HomologicalComplex.eval AddCommGrpCatᵒᵖ (up ℤ) (0 : ℤ)).mapHomologicalComplex
            (up ℤ)).map φflip := by
    -- On the flipped zero row, the comparison is just postcomposition by the row map.
    ext q
    simp [product_total_zero_column_to_zero_row_flip, φflip, Category.assoc]
  have hrow :
      product_total_zero_row_to_total
          (product_total_zero_column_to_zero_row_flip (α ≫ φ.f 0))
          (product_total_zero_column_to_zero_row_flip_comp_d (α ≫ φ.f 0) hcompcycles) =
        product_total_zero_row_to_total
          (product_total_zero_column_to_zero_row_flip α ≫
            ((HomologicalComplex.eval AddCommGrpCatᵒᵖ (up ℤ) (0 : ℤ)).mapHomologicalComplex
              (up ℤ)).map φflip)
          (productTotalZeroRow_comp_map_cycles
            (product_total_zero_column_to_zero_row_flip α)
            (product_total_zero_column_to_zero_row_flip_comp_d α hαcycles)
            φflip) := by
    rw [hflip_map]
    ext n
    rfl
  -- Rewrite through the flipped zero-row comparison, use row functoriality there, and then
  -- transport back with the naturality of `totalFlipIso`.
  calc
    product_total_zero_column_to_total (α ≫ φ.f 0) hcompcycles =
        product_total_zero_row_to_total
            (product_total_zero_column_to_zero_row_flip α ≫
              ((HomologicalComplex.eval AddCommGrpCatᵒᵖ (up ℤ) (0 : ℤ)).mapHomologicalComplex
                (up ℤ)).map φflip)
            (productTotalZeroRow_comp_map_cycles
              (product_total_zero_column_to_zero_row_flip α)
              (product_total_zero_column_to_zero_row_flip_comp_d α hαcycles)
              φflip) ≫
          (B₂.totalFlipIso (up ℤ)).hom := by
      simp [product_total_zero_column_to_total, hrow]
    _ =
        product_total_zero_row_to_total
            (product_total_zero_column_to_zero_row_flip α)
            (product_total_zero_column_to_zero_row_flip_comp_d α hαcycles) ≫
          total.map φflip (up ℤ) ≫ (B₂.totalFlipIso (up ℤ)).hom := by
      rw [productTotalZeroRowToTotal_comp_map]
    _ =
        product_total_zero_row_to_total
            (product_total_zero_column_to_zero_row_flip α)
            (product_total_zero_column_to_zero_row_flip_comp_d α hαcycles) ≫
          (B₁.totalFlipIso (up ℤ)).hom ≫ total.map φ (up ℤ) := by
      rw [Category.assoc, productTotalFlipIso_hom_map_eq, ← Category.assoc]
    _ = product_total_zero_column_to_total α hαcycles ≫ total.map φ (up ℤ) := by
      rfl

/-- Helper for Lemma 12.26.4: the cutoff-stage opposite comparison commutes with the canonical
inclusions into the full source and full opposite bicomplex total. -/
private theorem productTotalToTargetOpStageCompare
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (t : ℤ) :
    product_total_zero_column_to_total
        (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t)
        (by
          -- The stage zero-column comparison inherits the cycle relation from the full one.
          intro q
          exact lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
            (A := A) (π := π) hπ t q) ≫
      total.map (lowerStupidTruncationProductTotalOppositeBicomplexInclusion A t) (up ℤ) =
        lowerStupidTruncationInclusion (productTotalTargetOp M) t ≫ productTotalToTargetOp A π hπ := by
  have hcol :
      lowerStupidTruncationProductTotalTargetZeroColumnMap A π t ≫
          (lowerStupidTruncationProductTotalOppositeBicomplexInclusion A t).f 0 =
        lowerStupidTruncationInclusion (productTotalTargetOp M) t ≫
          product_total_target_zero_column_map A π := by
    -- The degree-zero row of the outer naturality square is exactly the desired comparison.
    simpa [lowerStupidTruncationProductTotalTargetZeroColumnMap,
      lowerStupidTruncationProductTotalOppositeBicomplexInclusion,
      lowerStupidTruncationProductTotalOppositeBicomplex] using
      lowerStupidTruncationMapCompInclusion
        (K := productTotalTargetOp M)
        (L := (productTotalOppositeBicomplex A).X 0)
        (product_total_target_zero_column_map A π) t
  have hcompcycles :
      ∀ q : ℤ,
        ((lowerStupidTruncationProductTotalTargetZeroColumnMap A π t) ≫
          (lowerStupidTruncationProductTotalOppositeBicomplexInclusion A t).f 0).f q ≫
            ((productTotalOppositeBicomplex A).d 0 1).f q = 0 := by
    intro q
    -- After identifying the stage zero-column map with the ambient one, the cycle relation is the
    -- original zero-column relation precomposed with the source inclusion.
    rw [hcol]
    simp [Category.assoc, product_total_target_zero_column_map_cycles (A := A) (π := π) hπ q]
  -- Apply the owner-level functoriality of zero-column totalization to the rowwise inclusion.
  simpa [productTotalToTargetOp] using
    productTotalZeroColumnToTotal_comp_total_map
      (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t)
      (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
        (A := A) (π := π) hπ t)
      (lowerStupidTruncationProductTotalOppositeBicomplexInclusion A t)
      hcompcycles

/-- Helper for Lemma 12.26.4: negative columns of the opposite bicomplex vanish because the
reindexed augmented row only has rows in nonpositive horizontal degree. -/
private theorem productTotalOppositeColumnIsZeroOfNeg
    (A : AbCochainResolution) (p q : ℤ) (hp : p < 0) :
    IsZero (((productTotalOppositeBicomplex A).X p).X q) := by
  let hrow :
      IsZero ((augmentedRowBicomplex A).X (-p)) := by
    -- Positive horizontal degrees are outside the image of `embeddingDownNat`.
    exact (A.isZero_extend_X embeddingDownNat (-p)) (fun j hj ↦ by
      have hnonpos : (ComplexShape.embeddingDownNat.f j : ℤ) ≤ 0 := by
        simp [ComplexShape.embeddingDownNat]
      rw [hj] at hnonpos
      omega)
  let hterm :
      IsZero (((augmentedRowBicomplex A).X (-p)).X (-q)) :=
    (HomologicalComplex.eval AddCommGrpCat (up ℤ) (-q)).map_isZero hrow
  -- Transport the zero term across the explicit opposite-side degree identification.
  exact
    ((eqToIso (productTotalColumn_objEq A p q)).isZero_iff).2
      (by simpa using hterm.op)

/-- Helper for Lemma 12.26.4: every lower-truncated opposite stage has finite antidiagonal
support. Only columns `0 ≤ p ≤ n - t` can contribute in total degree `n`. -/
private theorem lowerStupidTruncationProductTotalOppositeBicomplexHasFiniteAntidiagonalSupport
    (A : AbCochainResolution) (t : ℤ) :
    doubleComplexHasFiniteAntidiagonalSupport
      (lowerStupidTruncationProductTotalOppositeBicomplex A t) := by
  intro n
  let B := lowerStupidTruncationProductTotalOppositeBicomplex A t
  have hsubset :
      {p : ℤ | ¬ IsZero ((B.X p).X (n - p))} ⊆ Set.Icc 0 (n - t) := by
    intro p hp
    constructor
    · by_contra hpneg
      have hterm :
          IsZero ((B.X p).X (n - p)) := by
        -- Negative columns are already zero before truncation, so they remain zero afterwards.
        exact lowerStupidTruncationXIsZeroOfRowIsZero
          ((productTotalOppositeBicomplex A).X p)
          (productTotalOppositeColumnIsZeroOfNeg A p (n - p) (lt_of_not_ge hpneg))
          t (n - p)
      exact hp hterm
    · by_contra hple
      have hqt : n - p < t := by
        omega
      have hterm :
          IsZero ((B.X p).X (n - p)) := by
        -- Once the vertical degree drops below the cutoff, rowwise truncation kills the summand.
        exact lowerStupidTruncationXIsZeroOfLt
          ((productTotalOppositeBicomplex A).X p) t (n - p) hqt
      exact hp hterm
  -- The nonzero antidiagonal summands lie in a finite interval of columns.
  exact (Set.finite_Icc 0 (n - t)).subset hsubset

/-- Helper for Chap12 Lemma 12 26 4: below the cutoff, every object of the flipped truncated row
vanishes, so the row is split exact. -/
private theorem discardedTruncatedOppositeRowExactAt
    (A : AbCochainResolution) (t q p : ℤ) (hqt : q < t) (hp : 0 < p) :
    ((lowerStupidTruncationProductTotalOppositeBicomplex A t).flip.X q).ExactAt p := by
  let S : ShortComplex AddCommGrpCatᵒᵖ :=
    (((lowerStupidTruncationProductTotalOppositeBicomplex A t).flip.X q).sc' (p - 1) p (p + 1))
  have h₁ : IsZero S.X₁ := by
    -- The discarded vertical degree kills the left object of the row short complex.
    simpa [S] using
      lowerStupidTruncationXIsZeroOfLt ((productTotalOppositeBicomplex A).X (p - 1)) t q hqt
  have h₂ : IsZero S.X₂ := by
    -- The same discarded-degree argument kills the middle object.
    simpa [S] using
      lowerStupidTruncationXIsZeroOfLt ((productTotalOppositeBicomplex A).X p) t q hqt
  have h₃ : IsZero S.X₃ := by
    -- The right object also vanishes below the cutoff.
    simpa [S] using
      lowerStupidTruncationXIsZeroOfLt ((productTotalOppositeBicomplex A).X (p + 1)) t q hqt
  let e₁₂ : S.X₁ ≅ S.X₂ := h₁.iso h₂
  have hf : S.f = e₁₂.hom := by
    -- Any map out of the zero source agrees with the canonical zero-object isomorphism.
    exact h₁.eq_of_src _ _
  haveI : IsIso S.f := by
    rw [hf]
    infer_instance
  have hshort : S.ShortExact :=
    (ShortComplex.Splitting.ofIsIsoOfIsZero S inferInstance h₃).shortExact
  -- A split short exact sequence gives exactness at the middle object.
  simpa [S, HomologicalComplex.exactAt_iff] using hshort.exact

/-- Helper for Chap12 Lemma 12 26 4: below the cutoff, the stage zero-column cycles map is an
isomorphism because its defining short complex is split by zero objects. -/
private theorem discardedTruncatedZeroColumnCyclesIsIso
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (t q : ℤ) (hqt : q < t) :
    IsIso
      (doubleComplexZeroColumnCyclesMap
        (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t)
        (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
          (A := A) (π := π) hπ t)
        q) := by
  let B := lowerStupidTruncationProductTotalOppositeBicomplex A t
  let α := lowerStupidTruncationProductTotalTargetZeroColumnMap A π t
  let S : ShortComplex AddCommGrpCatᵒᵖ :=
    ShortComplex.mk
      ((doubleComplexZeroColumnToZeroRowFlip α).f q)
      ((B.flip.X q).d 0 1)
      (doubleComplexZeroColumnToZeroRowFlip_comp_d α
        (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
          (A := A) (π := π) hπ t)
        q)
  have h₁ : IsZero S.X₁ := by
    -- The truncated source already vanishes below the cutoff.
    simpa [S, α, B] using
      lowerStupidTruncationXIsZeroOfLt (productTotalTargetOp M) t q hqt
  have h₂ : IsZero S.X₂ := by
    -- The zeroth-column object vanishes in the discarded degree.
    simpa [S, α, B] using
      lowerStupidTruncationXIsZeroOfLt ((productTotalOppositeBicomplex A).X 0) t q hqt
  have h₃ : IsZero S.X₃ := by
    -- The first-column object vanishes for the same reason.
    simpa [S, α, B] using
      lowerStupidTruncationXIsZeroOfLt ((productTotalOppositeBicomplex A).X 1) t q hqt
  let e₁₂ : S.X₁ ≅ S.X₂ := h₁.iso h₂
  have hf : S.f = e₁₂.hom := by
    -- Any map out of the zero source is forced to be the canonical isomorphism.
    exact h₁.eq_of_src _ _
  haveI : IsIso S.f := by
    rw [hf]
    infer_instance
  have hshort : S.ShortExact :=
    (ShortComplex.Splitting.ofIsIsoOfIsZero S inferInstance h₃).shortExact
  have hS : S.Exact := hshort.exact
  -- The stage cycles map is the `toCycles` map of this split short complex.
  simpa [doubleComplexZeroColumnCyclesMap, doubleComplexZeroRowCyclesMap, S, α, B] using
    (shortComplex_toCycles_isIso_of_exact_of_mono S hS)

/-- Helper for Lemma 12.26.4: evaluating the outer chain differential in degree `q` still gives a
short-complex relation. -/
private theorem augmentedOuterRowCompZeroEval
    (A : AbCochainResolution) (n : ℕ) (q : ℤ) :
    ((A.d (n + 2) (n + 1)).f q) ≫ ((A.d (n + 1) n).f q) = 0 := by
  -- Degreewise evaluation of `d ≫ d = 0` gives the needed short-complex relation.
  simpa using congrArg (fun f ↦ f.f q) (A.d_comp_d (n + 2) (n + 1) n)

/-- Helper for Lemma 12.26.4: the degree-`q` outer row
`A_{n + 2}^q ⟶ A_{n + 1}^q ⟶ A_n^q` as a short complex. -/
private noncomputable abbrev augmentedOuterRowShortComplex
    (A : AbCochainResolution) (n : ℕ) (q : ℤ) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk
    ((A.d (n + 2) (n + 1)).f q)
    ((A.d (n + 1) n).f q)
    (augmentedOuterRowCompZeroEval A n q)

/-- Helper for Lemma 12.26.4: evaluating an exact outer row of the resolution at a fixed vertical
degree gives an exact short complex of abelian groups. -/
private theorem augmentedOuterRowExactEval
    (A : AbCochainResolution)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (n : ℕ) (q : ℤ) :
    (augmentedOuterRowShortComplex A n q).Exact := by
  let F := HomologicalComplex.eval AddCommGrpCat (up ℤ) q
  -- Reuse exactness of the outer chain row and evaluate it degreewise.
  simpa [augmentedOuterRowShortComplex, HomologicalComplex.ExactAt,
    HomologicalComplex.exactAt_iff, F, Nat.add_assoc] using
    (hExact n).map F

/-- Helper for Lemma 12.26.4: the positive row of the opposite bicomplex is the opposite of the
evaluated outer row of the original resolution. -/
private noncomputable def productTotalOppositeRowShortComplexIso
    (A : AbCochainResolution) (q : ℤ) (n : ℕ) :
    (((productTotalOppositeBicomplex A).flip.X q).sc' n (n + 1) (n + 2)) ≅
      (augmentedOuterRowShortComplex A n (-q)).op := by
  let e (m : ℕ) :
      (((productTotalOppositeBicomplex A).flip.X q).X m) ≅ op ((A.X m).X (-q)) :=
    (eqToIso (productTotalColumn_objEq A (m : ℤ) q)) ≪≫
      (Iso.op ((HomologicalComplex.eval AddCommGrpCat (up ℤ) (-q)).mapIso
        (augmentedRowBicomplexNegIso A m)))
  have hcomm :
      ∀ m : ℕ,
        (((productTotalOppositeBicomplex A).flip.X q).d m (m + 1)) ≫ (e (m + 1)).hom =
          (e m).hom ≫ ((A.d (m + 1) m).f (-q)).op := by
    intro m
    have hcol :
        eqToHom (productTotalColumn_objEq A (m : ℤ) q) ≫
            (((productTotalOppositeBicomplex A).flip.X q).d m (m + 1)) ≫
            eqToHom (productTotalColumn_objEq A ((m + 1 : ℕ) : ℤ) q).symm =
          (((augmentedRowBicomplex A).d (-((m + 1 : ℕ) : ℤ)) (-(m : ℕ) : ℤ)).f (-q)).op := by
      simpa using
        (productTotalColumn_d_eq A (p := (m : ℤ)) (p' := ((m + 1 : ℕ) : ℤ))
          (q := q) (by simp))
    have hrow :
        (((augmentedRowBicomplex A).d (-((m + 1 : ℕ) : ℤ)) (-(m : ℕ) : ℤ)).f (-q)).op =
          (((HomologicalComplex.eval AddCommGrpCat (up ℤ) (-q)).mapIso
              (augmentedRowBicomplexNegIso A m)).inv).op ≫
            ((A.d (m + 1) m).f (-q)).op ≫
            (((HomologicalComplex.eval AddCommGrpCat (up ℤ) (-q)).mapIso
              (augmentedRowBicomplexNegIso A (m + 1))).hom).op := by
      -- Evaluate the row identification and then pass to opposites so the arrow points in the
      -- same direction as the flipped row differential.
      simpa [Category.assoc] using
        congrArg Quiver.Hom.op
          (congrArg (fun f ↦ f.f (-q)) (augmentedRowBicomplex_d_eq A (m + 1) m))
    -- Route correction: rewrite the flipped-row differential through the explicit opposite-row
    -- identification instead of unfolding the full product-total/opposite definitions.
    calc
      (((productTotalOppositeBicomplex A).flip.X q).d m (m + 1)) ≫ (e (m + 1)).hom =
          (((productTotalOppositeBicomplex A).flip.X q).d m (m + 1)) ≫
            eqToHom (productTotalColumn_objEq A ((m + 1 : ℕ) : ℤ) q).symm ≫
            (((HomologicalComplex.eval AddCommGrpCat (up ℤ) (-q)).mapIso
              (augmentedRowBicomplexNegIso A (m + 1))).hom).op := by
            simp [e, Category.assoc]
      _ =
          eqToHom (productTotalColumn_objEq A (m : ℤ) q).symm ≫
            (((augmentedRowBicomplex A).d (-((m + 1 : ℕ) : ℤ)) (-(m : ℕ) : ℤ)).f (-q)).op ≫
            (((HomologicalComplex.eval AddCommGrpCat (up ℤ) (-q)).mapIso
              (augmentedRowBicomplexNegIso A (m + 1))).hom).op := by
            rw [← Category.assoc, hcol]
            simp [Category.assoc]
      _ =
          eqToHom (productTotalColumn_objEq A (m : ℤ) q).symm ≫
            (((HomologicalComplex.eval AddCommGrpCat (up ℤ) (-q)).mapIso
              (augmentedRowBicomplexNegIso A m)).inv).op ≫
            ((A.d (m + 1) m).f (-q)).op ≫
            (((HomologicalComplex.eval AddCommGrpCat (up ℤ) (-q)).mapIso
              (augmentedRowBicomplexNegIso A (m + 1))).hom).op := by
            rw [hrow]
      _ = (e m).hom ≫ ((A.d (m + 1) m).f (-q)).op := by
            simp [e, Category.assoc]
  refine ShortComplex.isoMk (e n) (e (n + 1)) (e (n + 2)) ?_ ?_
  · -- The first square compares the `n → n + 1` differential in the opposite row with the
    -- opposite of the evaluated outer differential.
    simpa [augmentedOuterRowShortComplex] using hcomm n
  · -- The second square is the same comparison one step further along the row.
    simpa [augmentedOuterRowShortComplex] using hcomm (n + 1)

/-- Helper for Lemma 12.26.4: every positive row of the full opposite bicomplex is exact. -/
private theorem productTotalOppositeRowExactAt
    (A : AbCochainResolution)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (q p : ℤ) (hp : 0 < p) :
    ((productTotalOppositeBicomplex A).flip.X q).ExactAt p := by
  let n : ℕ := Int.toNat (p - 1)
  have hp_eq : (n : ℤ) + 1 = p := by
    dsimp [n]
    omega
  let S :
      ShortComplex AddCommGrpCatᵒᵖ :=
    (((productTotalOppositeBicomplex A).flip.X q).sc' n (n + 1) (n + 2))
  have hS : S.Exact := by
    -- Transport exactness of the evaluated outer row back to the opposite-row short complex.
    exact
      (ShortComplex.exact_iff_of_iso (productTotalOppositeRowShortComplexIso A q n)).2
        (augmentedOuterRowExactEval A hExact n (-q)).op
  simpa [S, hp_eq, HomologicalComplex.exactAt_iff] using hS

/-- Helper for Lemma 12.26.4: in a retained vertical degree, the truncated opposite row is the
original opposite row after cancelling the truncation isomorphisms. -/
private noncomputable def retainedTruncatedOppositeRowShortComplexIso
    (A : AbCochainResolution) (t q : ℤ) (n : ℕ) (htq : t ≤ q) :
    (((lowerStupidTruncationProductTotalOppositeBicomplex A t).flip.X q).sc' n (n + 1) (n + 2)) ≅
      (((productTotalOppositeBicomplex A).flip.X q).sc' n (n + 1) (n + 2)) := by
  let hq : (ComplexShape.embeddingUpIntGE t).f (Int.toNat (q - t)) = q :=
    embeddingUpIntGE_toNat_sub_eq t q htq
  let e (m : ℕ) :
      (((lowerStupidTruncationProductTotalOppositeBicomplex A t).flip.X q).X m) ≅
        (((productTotalOppositeBicomplex A).flip.X q).X m) :=
    lowerStupidTruncationXIso ((productTotalOppositeBicomplex A).X (m : ℤ)) t q htq
  have hcomm :
      ∀ m : ℕ,
        (((lowerStupidTruncationProductTotalOppositeBicomplex A t).flip.X q).d m (m + 1)) ≫
            (e (m + 1)).hom =
          (e m).hom ≫ (((productTotalOppositeBicomplex A).flip.X q).d m (m + 1)) := by
    intro m
    -- The retained row differential is the truncation of the original opposite-row differential.
    simpa [lowerStupidTruncationProductTotalOppositeBicomplex, productTotalOppositeBicomplex,
      e, hq] using
      (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
        (K := (productTotalOppositeBicomplex A).X (m : ℤ))
        (L := (productTotalOppositeBicomplex A).X ((m + 1 : ℕ) : ℤ))
        (φ := (productTotalOppositeBicomplex A).d (m : ℤ) ((m + 1 : ℕ) : ℤ))
        (e := ComplexShape.embeddingUpIntGE t) hq)
  refine ShortComplex.isoMk (e n) (e (n + 1)) (e (n + 2)) ?_ ?_
  · simpa using hcomm n
  · simpa using hcomm (n + 1)

/-- Helper for Lemma 12.26.4: in a retained vertical degree, row exactness is inherited from the
full opposite bicomplex. -/
private theorem retainedTruncatedOppositeRowExactAt
    (A : AbCochainResolution)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (t q p : ℤ) (htq : t ≤ q) (hp : 0 < p) :
    ((lowerStupidTruncationProductTotalOppositeBicomplex A t).flip.X q).ExactAt p := by
  let n : ℕ := Int.toNat (p - 1)
  have hp_eq : (n : ℤ) + 1 = p := by
    dsimp [n]
    omega
  let S :
      ShortComplex AddCommGrpCatᵒᵖ :=
    (((lowerStupidTruncationProductTotalOppositeBicomplex A t).flip.X q).sc' n (n + 1) (n + 2))
  have hS : S.Exact := by
    -- Transport the retained stage row to the already-normalized untruncated opposite row.
    exact
      (ShortComplex.exact_iff_of_iso
        (retainedTruncatedOppositeRowShortComplexIso A t q n htq)).2
        (by
          have hfull :
              ((productTotalOppositeBicomplex A).flip.X q).ExactAt ((n : ℤ) + 1) :=
            productTotalOppositeRowExactAt A hExact q ((n : ℤ) + 1) (by positivity)
          simpa [HomologicalComplex.exactAt_iff] using hfull)
  simpa [S, hp_eq, HomologicalComplex.exactAt_iff] using hS

/-- Helper for Lemma 12.26.4: the original zero-column row short complex is exact. -/
private theorem product_total_target_zero_column_exact
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (q : ℤ) :
    (product_total_target_zero_column_shortComplex A π hπ q).Exact := by
  let S₁ : ShortComplex AddCommGrpCatᵒᵖ :=
    product_total_target_zero_column_shortComplex A π hπ q
  let S₂ : ShortComplex AddCommGrpCat :=
    ShortComplex.mk
      (((augmentedRowBicomplex A).d (-1) 0).f (-q))
      ((augmentedRowBicomplexZeroIso A).hom.f (-q) ≫ π.f (-q))
      (by
        -- This is the degreewise form of the augmentation relation on the reindexed row.
        simpa [Category.assoc] using
          congrArg (fun f : (augmentedRowBicomplex A).X (-1) ⟶ M ↦ f.f (-q))
            (product_total_target_prev_column_comp_zero A π hπ))
  have hIso : S₁ ≅ S₂.op := by
    refine ShortComplex.isoMk
      (eqToIso (productTotalTargetOp_objEq M q))
      (eqToIso (productTotalZeroRow_objEq A q))
      (eqToIso (productTotalColumn_objEq A 1 q))
      ?_ ?_
    · -- The first map is literally the opposite of the reindexed augmentation component.
      simp [S₁, S₂, product_total_target_zero_column_shortComplex,
        product_total_target_zero_column_component, Category.assoc]
    · -- The second map is the transported `0 → 1` horizontal differential of the opposite
      -- bicomplex.
      simpa [S₁, S₂, product_total_target_zero_column_shortComplex] using
        (productTotalColumn_d_eq A (p := (0 : ℤ)) (p' := (1 : ℤ)) (q := q) (by simp))
  -- Transport the exact reindexed augmented row to the opposite zero-column model.
  exact
    (ShortComplex.exact_iff_of_iso hIso).2
      (augmented_row_reindexed_degreewise_exact (A := A) (π := π) hπ hExact₀ (-q)).op

/-- Helper for Lemma 12.26.4: the original zero-column row short complex is monic on the left
because it is the opposite of an epimorphic augmentation component. -/
private theorem product_total_target_zero_column_mono
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hEpi : Epi π)
    (q : ℤ) :
    Mono (product_total_target_zero_column_shortComplex A π hπ q).f := by
  letI : Epi ((augmentedRowBicomplexZeroIso A).hom.f (-q) ≫ π.f (-q)) :=
    augmented_row_reindexed_degreewise_epi (A := A) (π := π) hEpi (-q)
  -- Opposites turn the degree-`-q` augmentation epimorphism into monicity of the stage left map.
  simpa [product_total_target_zero_column_shortComplex,
    product_total_target_zero_column_component, Category.assoc] using
    (show Mono (((augmentedRowBicomplexZeroIso A).hom.f (-q) ≫ π.f (-q)).op) by
      infer_instance)

/-- Helper for Lemma 12.26.4: in a retained vertical degree, the stage zero-column row short
complex is canonically identified with the original exact zero-column row. -/
private noncomputable def retainedStageZeroColumnShortComplexIso
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (t q : ℤ) (htq : t ≤ q) :
    let B := lowerStupidTruncationProductTotalOppositeBicomplex A t
    let α := lowerStupidTruncationProductTotalTargetZeroColumnMap A π t
    ShortComplex.mk
      ((doubleComplexZeroColumnToZeroRowFlip α).f q)
      ((B.flip.X q).d 0 1)
      (doubleComplexZeroColumnToZeroRowFlip_comp_d α
        (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
          (A := A) (π := π) hπ t)
        q) ≅
      product_total_target_zero_column_shortComplex A π hπ q := by
  let B := lowerStupidTruncationProductTotalOppositeBicomplex A t
  let α := lowerStupidTruncationProductTotalTargetZeroColumnMap A π t
  let hq : (ComplexShape.embeddingUpIntGE t).f (Int.toNat (q - t)) = q :=
    embeddingUpIntGE_toNat_sub_eq t q htq
  let e₁ := lowerStupidTruncationXIso (productTotalTargetOp M) t q htq
  let e₂ := lowerStupidTruncationXIso ((productTotalOppositeBicomplex A).X 0) t q htq
  let e₃ := lowerStupidTruncationXIso ((productTotalOppositeBicomplex A).X 1) t q htq
  have hα :
      ((doubleComplexZeroColumnToZeroRowFlip α).f q) ≫ e₂.hom =
        e₁.hom ≫ (product_total_target_zero_column_map A π).f q := by
    have hα' :
        α.f q ≫ e₂.hom = e₁.hom ≫ (product_total_target_zero_column_map A π).f q := by
      -- The stage map is the functorial truncation of the original zero-column comparison.
      simpa [lowerStupidTruncationProductTotalTargetZeroColumnMap,
        lowerStupidTruncationProductTotalTargetOp,
        lowerStupidTruncationProductTotalOppositeBicomplex,
        productTotalOppositeBicomplex, e₁, e₂, hq] using
        (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
          (K := productTotalTargetOp M)
          (L := (productTotalOppositeBicomplex A).X 0)
          (φ := product_total_target_zero_column_map A π)
          (e := ComplexShape.embeddingUpIntGE t) hq)
    -- The zero-column/zero-row flip identification is componentwise the identity.
    simpa [α, doubleComplexZeroColumnToZeroRowFlip,
      product_total_zero_column_iso_zero_row_flip, Category.assoc] using hα'
  have hd :
      ((B.flip.X q).d 0 1) ≫ e₃.hom =
        e₂.hom ≫ ((productTotalOppositeBicomplex A).d 0 1).f q := by
    -- The retained horizontal differential is the truncation of the original `0 ⟶ 1` row map.
    simpa [lowerStupidTruncationProductTotalOppositeBicomplex,
      productTotalOppositeBicomplex, e₂, e₃, hq] using
      (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
        (K := (productTotalOppositeBicomplex A).X 0)
        (L := (productTotalOppositeBicomplex A).X 1)
        (φ := (productTotalOppositeBicomplex A).d 0 1)
        (e := ComplexShape.embeddingUpIntGE t) hq)
  -- Route correction: normalize the retained stage row first, then reuse the original
  -- zero-column short complex instead of reproving exactness from scratch.
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · simpa [B, α, product_total_target_zero_column_shortComplex] using hα
  · simpa [B, α, product_total_target_zero_column_shortComplex] using hd

/-- Helper for Lemma 12.26.4: in a retained degree, the stage zero-column row short complex is
exact because it is isomorphic to the original exact zero-column row. -/
private theorem retainedStageZeroColumnExact
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (t q : ℤ) (htq : t ≤ q) :
    let B := lowerStupidTruncationProductTotalOppositeBicomplex A t
    let α := lowerStupidTruncationProductTotalTargetZeroColumnMap A π t
    (ShortComplex.mk
      ((doubleComplexZeroColumnToZeroRowFlip α).f q)
      ((B.flip.X q).d 0 1)
      (doubleComplexZeroColumnToZeroRowFlip_comp_d α
        (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
          (A := A) (π := π) hπ t)
        q)).Exact := by
  -- Transport exactness of the original zero-column row back to the retained stage model.
  exact
    (ShortComplex.exact_iff_of_iso
      (retainedStageZeroColumnShortComplexIso (A := A) (M := M) π hπ t q htq)).2
      (product_total_target_zero_column_exact (A := A) (π := π) hπ hExact₀ q)

/-- Helper for Lemma 12.26.4: in a retained degree, the stage zero-column left map is monic
because it is conjugate to the original zero-column comparison. -/
private theorem retainedStageZeroColumnMono
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hEpi : Epi π)
    (t q : ℤ) (htq : t ≤ q) :
    let B := lowerStupidTruncationProductTotalOppositeBicomplex A t
    let α := lowerStupidTruncationProductTotalTargetZeroColumnMap A π t
    Mono
      (ShortComplex.mk
        ((doubleComplexZeroColumnToZeroRowFlip α).f q)
        ((B.flip.X q).d 0 1)
        (doubleComplexZeroColumnToZeroRowFlip_comp_d α
          (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
            (A := A) (π := π) hπ t)
          q)).f := by
  let B := lowerStupidTruncationProductTotalOppositeBicomplex A t
  let α := lowerStupidTruncationProductTotalTargetZeroColumnMap A π t
  let e :=
    retainedStageZeroColumnShortComplexIso (A := A) (M := M) π hπ t q htq
  have hOrig : Mono (product_total_target_zero_column_shortComplex A π hπ q).f :=
    product_total_target_zero_column_mono (A := A) (π := π) hπ hEpi q
  have hf :
      (ShortComplex.mk
        ((doubleComplexZeroColumnToZeroRowFlip α).f q)
        ((B.flip.X q).d 0 1)
        (doubleComplexZeroColumnToZeroRowFlip_comp_d α
          (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
            (A := A) (π := π) hπ t)
          q)).f =
        e.hom.τ₁ ≫ (product_total_target_zero_column_shortComplex A π hπ q).f ≫ e.inv.τ₂ := by
    -- Solve for the stage left map from the first commutative square of the short-complex
    -- isomorphism.
    calc
      (ShortComplex.mk
        ((doubleComplexZeroColumnToZeroRowFlip α).f q)
        ((B.flip.X q).d 0 1)
        (doubleComplexZeroColumnToZeroRowFlip_comp_d α
          (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
            (A := A) (π := π) hπ t)
          q)).f =
          (ShortComplex.mk
            ((doubleComplexZeroColumnToZeroRowFlip α).f q)
            ((B.flip.X q).d 0 1)
            (doubleComplexZeroColumnToZeroRowFlip_comp_d α
              (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
                (A := A) (π := π) hπ t)
              q)).f ≫ e.hom.τ₂ ≫ e.inv.τ₂ := by
              simp [Category.assoc]
      _ = e.hom.τ₁ ≫ (product_total_target_zero_column_shortComplex A π hπ q).f ≫ e.inv.τ₂ := by
            rw [← Category.assoc, ← e.hom.comm₁₂]
            simp [Category.assoc]
  -- The stage left map is a composite of two isomorphisms with the monic original left map.
  simpa [hf]

/-- Helper for Lemma 12.26.4: in a retained vertical degree, the stage zero-column cycles map is
an isomorphism because it is the `toCycles` map of the transported exact stage row. -/
private theorem retainedTruncatedZeroColumnCyclesIsIso
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (t q : ℤ) (htq : t ≤ q) :
    IsIso
      (doubleComplexZeroColumnCyclesMap
        (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t)
        (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
          (A := A) (π := π) hπ t)
        q) := by
  let B := lowerStupidTruncationProductTotalOppositeBicomplex A t
  let α := lowerStupidTruncationProductTotalTargetZeroColumnMap A π t
  let S : ShortComplex AddCommGrpCatᵒᵖ :=
    ShortComplex.mk
      ((doubleComplexZeroColumnToZeroRowFlip α).f q)
      ((B.flip.X q).d 0 1)
      (doubleComplexZeroColumnToZeroRowFlip_comp_d α
        (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
          (A := A) (π := π) hπ t)
        q)
  have hS : S.Exact := by
    simpa [S, B, α] using
      retainedStageZeroColumnExact (A := A) (M := M) π hπ hExact₀ t q htq
  haveI : Mono S.f := by
    simpa [S, B, α] using
      retainedStageZeroColumnMono (A := A) (M := M) π hπ hEpi t q htq
  -- The retained stage cycles map is exactly the `toCycles` map of the transported short
  -- complex above.
  simpa [doubleComplexZeroColumnCyclesMap, doubleComplexZeroRowCyclesMap, S, α, B] using
    (shortComplex_toCycles_isIso_of_exact_of_mono S hS)

/-- Helper for Lemma 12.26.4: each cutoff stage should be a quasi-isomorphism by applying
Lemma `12.25.4` to the lower-truncated opposite bicomplex. -/
private theorem lowerStupidTruncationProductTotalToTargetOpQuasiIso
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (t : ℤ) :
    QuasiIso
      (product_total_zero_column_to_total
        (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t)
        (by
          -- The stage zero-column map is the truncation of the original comparison, so the cycle
          -- relation is inherited degreewise.
          intro q
          exact lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
            (A := A) (π := π) hπ t q)) := by
  let B := lowerStupidTruncationProductTotalOppositeBicomplex A t
  let α := lowerStupidTruncationProductTotalTargetZeroColumnMap A π t
  let hαcycles :
      ∀ q : ℤ, α.f q ≫ (B.d 0 1).f q = 0 := by
    -- Reuse the functorial truncation compatibility proved once above.
    intro q
    exact lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
      (A := A) (π := π) hπ t q
  let hvanish : ∀ p q : ℤ, p < 0 → IsZero ((B.X p).X q) := by
    intro p q hp
    -- Negative columns vanish before and after the rowwise truncation.
    exact lowerStupidTruncationXIsZeroOfRowIsZero
      ((productTotalOppositeBicomplex A).X p)
      (productTotalOppositeColumnIsZeroOfNeg A p q hp)
      t q
  let hexact : ∀ p q : ℤ, 0 < p → (B.flip.X q).ExactAt p := by
    -- Split into retained and discarded vertical degrees; only the retained transport remains.
    intro p q hp
    by_cases htq : t ≤ q
    · exact retainedTruncatedOppositeRowExactAt A hExact t q p htq hp
    · exact discardedTruncatedOppositeRowExactAt A t q p (lt_of_not_ge htq) hp
  let hαiso :
      ∀ q : ℤ, IsIso (doubleComplexZeroColumnCyclesMap α hαcycles q) := by
    -- Split into retained and discarded vertical degrees; the discarded branch is already split.
    intro q
    by_cases htq : t ≤ q
    · exact retainedTruncatedZeroColumnCyclesIsIso
        (A := A) (M := M) π hπ hExact₀ hEpi t q htq
    · exact discardedTruncatedZeroColumnCyclesIsIso (A := A) (M := M) π hπ t q
        (lt_of_not_ge htq)
  -- Route correction: the stage theorem now packages the exact hypotheses required by
  -- `zeroColumnToTotal_quasiIso_of_exact_rows_and_cycles`.
  simpa [B, α, hαcycles] using
    (zeroColumnToTotal_quasiIso_of_exact_rows_and_cycles
      (A := B)
      (K := lowerStupidTruncationProductTotalTargetOp M t)
      (hfin := lowerStupidTruncationProductTotalOppositeBicomplexHasFiniteAntidiagonalSupport A t)
      hvanish
      hexact
      α
      hαcycles
      hαiso)

/-- Helper for Chap12 Lemma 12 26 4: every cutoff-stage comparison map has acyclic mapping cone,
because the previous theorem already proves it is a quasi-isomorphism. -/
private theorem lowerStupidTruncationProductTotalToTargetOp_mappingConeAcyclic
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (t : ℤ) :
    (CochainComplex.mappingCone
        (product_total_zero_column_to_total
          (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t)
          (by
            -- The cutoff zero-column comparison inherits the row-cycle relation from the full map.
            intro q
            exact lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
              (A := A) (π := π) hπ t q))).Acyclic := by
  -- Repackage the already-proved stage quasi-isomorphism through the standard mapping-cone
  -- criterion; this is the stagewise acyclicity input for the intended inverse-limit descent.
  exact mappingCone_acyclic_of_quasiIso _
    (lowerStupidTruncationProductTotalToTargetOpQuasiIso
      (A := A) (π := π) hπ hExact₀ hEpi hExact t)

/-- Helper for Chap12 Lemma 12 26 4: after unop, each cutoff-stage comparison map still has an
acyclic mapping cone. -/
private theorem lowerStupidTruncationProductTotalToTarget_mappingConeAcyclic_unop
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (t : ℤ) :
    ((CochainComplex.mappingCone
        (product_total_zero_column_to_total
          (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t)
          (by
            -- The cutoff zero-column comparison inherits the row-cycle relation from the full
            -- map before passing to the opposite category.
            intro q
            exact lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
              (A := A) (π := π) hπ t q))).unop.Acyclic := by
  -- Route correction: the eventual full-cone argument works on the unopped product-total side,
  -- so record the stage acyclicity once in that spelling world.
  simpa using
    (lowerStupidTruncationProductTotalToTargetOp_mappingConeAcyclic
      (A := A) (π := π) hπ hExact₀ hEpi hExact t).unop

/-- Helper for Chap12 Lemma 12 26 4: the cutoff stage indexed by `n` is the lower truncation at
`-(n : ℤ)`. This is the source-facing indexing used for the inverse-limit descent. -/
private abbrev productTotalToTargetCutoff (n : ℕ) : ℤ :=
  -(n : ℤ)

/-- Helper for Chap12 Lemma 12 26 4: consecutive cutoff indices satisfy the monotonicity needed
for the stage-comparison maps. -/
private theorem productTotalToTargetCutoff_succ_le (n : ℕ) :
    productTotalToTargetCutoff (n + 1) ≤ productTotalToTargetCutoff n := by
  -- Consecutive cutoffs move one step farther toward `-∞`.
  omega

/-- Helper for Chap12 Lemma 12 26 4: the opposite-side cutoff-stage comparison map is the generic
zero-column-to-total owner applied to the truncated augmentation data. -/
private noncomputable abbrev productTotalToTargetOpStageMap
    (A : AbCochainResolution)
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (t : ℤ) :
    lowerStupidTruncationProductTotalTargetOp M t ⟶
      HomologicalComplex₂.productTotalOp (lowerStupidTruncationProductTotalOppositeBicomplex A t) :=
  product_total_zero_column_to_total
    (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t)
    (by
      -- The truncated zero-column map still lands in row cycles.
      intro q
      exact lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
        (A := A) (π := π) hπ t q)

/-- Helper for Chap12 Lemma 12 26 4: the rowwise stage-to-stage truncation comparison on the
opposite bicomplex is the natural transformation induced by the owner truncation comparisons. -/
private noncomputable abbrev productTotalToTargetOppositeBicomplexStageComparison
    (A : AbCochainResolution) (t₁ t₂ : ℤ) (ht : t₁ ≤ t₂) :
    lowerStupidTruncationProductTotalOppositeBicomplex A t₂ ⟶
      lowerStupidTruncationProductTotalOppositeBicomplex A t₁ :=
  (NatTrans.mapHomologicalComplex
    (lowerStupidTruncationComparisonNatTrans t₁ t₂ ht) (up ℤ)).app
      (productTotalOppositeBicomplex A)

/-- Helper for Chap12 Lemma 12 26 4: on each total degree, the opposite-side cutoff-stage
comparison has a retraction obtained by applying the rowwise truncation retraction on every
antidiagonal summand and then reassembling the product total. -/
private noncomputable def productTotalToTargetOppositeStageTotalComponentRetraction
    (A : AbCochainResolution) (n : ℕ) (q : ℤ) :
    (HomologicalComplex₂.total
        (lowerStupidTruncationProductTotalOppositeBicomplex A
          (productTotalToTargetCutoff (n + 1))) (up ℤ)).X q ⟶
      (HomologicalComplex₂.total
        (lowerStupidTruncationProductTotalOppositeBicomplex A
          (productTotalToTargetCutoff n)) (up ℤ)).X q := by
  let t₁ := productTotalToTargetCutoff (n + 1)
  let t₂ := productTotalToTargetCutoff n
  let B₁ := lowerStupidTruncationProductTotalOppositeBicomplex A t₁
  let B₂ := lowerStupidTruncationProductTotalOppositeBicomplex A t₂
  -- Each total-degree coordinate is sent back by the degreewise truncation retraction in its row.
  exact B₁.totalDesc (c₁₂ := up ℤ) (i₁₂ := q)
    (fun p r hpr ↦
      lowerStupidTruncationComparisonFRetraction
          ((productTotalOppositeBicomplex A).X p) t₁ t₂
          (productTotalToTargetCutoff_succ_le n) r ≫
        B₂.ιTotal (up ℤ) p r q hpr)

/-- Helper for Chap12 Lemma 12 26 4: the rowwise truncation retractions assemble to a right
inverse for the degree-`q` total map of consecutive opposite-side cutoff stages. -/
private theorem productTotalToTargetOppositeStageTotalComponent_comp_retraction
    (A : AbCochainResolution) (n : ℕ) (q : ℤ) :
    (total.map
        (productTotalToTargetOppositeBicomplexStageComparison A
          (productTotalToTargetCutoff (n + 1))
          (productTotalToTargetCutoff n)
          (productTotalToTargetCutoff_succ_le n))
        (up ℤ)).f q ≫
      productTotalToTargetOppositeStageTotalComponentRetraction A n q =
        𝟙 ((HomologicalComplex₂.total
          (lowerStupidTruncationProductTotalOppositeBicomplex A
            (productTotalToTargetCutoff n)) (up ℤ)).X q) := by
  let t₁ := productTotalToTargetCutoff (n + 1)
  let t₂ := productTotalToTargetCutoff n
  let ht := productTotalToTargetCutoff_succ_le n
  let B₂ := lowerStupidTruncationProductTotalOppositeBicomplex A t₂
  let φ := productTotalToTargetOppositeBicomplexStageComparison A t₁ t₂ ht
  -- Compare the would-be split identity after every antidiagonal summand inclusion.
  apply total.hom_ext
  intro p r hpr
  rw [Category.assoc, ιTotal_map, ι_totalDesc, Category.id_comp]
  -- In each row, the stage comparison followed by its retraction is already the identity.
  have hsplit :
      (φ.f p).f r ≫
          lowerStupidTruncationComparisonFRetraction
            ((productTotalOppositeBicomplex A).X p) t₁ t₂ ht r =
        𝟙 (((B₂.X p).X r)) := by
    simpa [φ, productTotalToTargetOppositeBicomplexStageComparison,
      lowerStupidTruncationComparison] using
      (lowerStupidTruncationComparisonF_comp_retraction
        ((productTotalOppositeBicomplex A).X p) t₁ t₂ ht r)
  simpa [Category.assoc] using congrArg (fun f ↦ f ≫ B₂.ιTotal (up ℤ) p r q hpr) hsplit

/-- Helper for Chap12 Lemma 12 26 4: after unop, the degree-`q` component of the consecutive
opposite-side cutoff-stage total comparison is surjective on the underlying abelian groups. -/
private theorem productTotalToTargetOppositeStageTotalComponent_unop_surjective
    (A : AbCochainResolution) (n : ℕ) (q : ℤ) :
    Function.Surjective
      ((Quiver.Hom.unop
        ((total.map
          (productTotalToTargetOppositeBicomplexStageComparison A
            (productTotalToTargetCutoff (n + 1))
            (productTotalToTargetCutoff n)
            (productTotalToTargetCutoff_succ_le n))
          (up ℤ)).f q)).hom) := by
  intro x
  refine ⟨((Quiver.Hom.unop
      (productTotalToTargetOppositeStageTotalComponentRetraction A n q)).hom x), ?_⟩
  -- Unop reverses the split identity above, so the assembled retraction gives a preimage of `x`.
  have hsplit := congrArg Quiver.Hom.unop
    (productTotalToTargetOppositeStageTotalComponent_comp_retraction A n q)
  exact congrArg (fun f ↦ f.hom x) hsplit

/-- Helper for Chap12 Lemma 12 26 4: precomposing the zero-column comparison by a source complex
map simply precomposes the resulting total map. -/
private theorem productTotalZeroColumnToTotal_precomp
    {K₁ K₂ : CochainComplex AddCommGrpCatᵒᵖ ℤ}
    {B : HomologicalComplex₂ AddCommGrpCatᵒᵖ (up ℤ) (up ℤ)}
    [B.HasTotal (up ℤ)]
    (γ : K₁ ⟶ K₂)
    (α : K₂ ⟶ B.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (B.d 0 1).f q = 0)
    (hcompcycles : ∀ q : ℤ, (γ ≫ α).f q ≫ (B.d 0 1).f q = 0) :
    product_total_zero_column_to_total (γ ≫ α) hcompcycles =
      γ ≫ product_total_zero_column_to_total α hαcycles := by
  ext n
  -- Both maps have the same `(0,n)` summand formula, so compare those components directly.
  simp [product_total_zero_column_to_total_component_on_zero_summand, Category.assoc]

/-- Helper for Chap12 Lemma 12 26 4: cutoff-stage comparison maps commute directly with the
stage-to-stage rowwise truncation morphisms on the opposite side. -/
private theorem productTotalToTargetOpStageToStageCompare
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (t₁ t₂ : ℤ)
    (ht : t₁ ≤ t₂) :
    productTotalToTargetOpStageMap A π hπ t₂ ≫
        total.map
          (productTotalToTargetOppositeBicomplexStageComparison A t₁ t₂ ht)
          (up ℤ) =
      lowerStupidTruncationComparison (productTotalTargetOp M) t₁ t₂ ht ≫
        productTotalToTargetOpStageMap A π hπ t₁ := by
  have hcol :
      lowerStupidTruncationProductTotalTargetZeroColumnMap A π t₂ ≫
          (productTotalToTargetOppositeBicomplexStageComparison A t₁ t₂ ht).f 0 =
        lowerStupidTruncationComparison (productTotalTargetOp M) t₁ t₂ ht ≫
          lowerStupidTruncationProductTotalTargetZeroColumnMap A π t₁ := by
    -- The truncation comparison is functorial on the zeroth column before totalization.
    simpa [productTotalToTargetOppositeBicomplexStageComparison,
      lowerStupidTruncationProductTotalTargetZeroColumnMap,
      lowerStupidTruncationProductTotalTargetOp,
      lowerStupidTruncationProductTotalOppositeBicomplex] using
      (lowerStupidTruncationMapCompComparison
        (f := product_total_target_zero_column_map A π)
        t₁ t₂ ht)
  have hcompcycles :
      ∀ q : ℤ,
        ((lowerStupidTruncationProductTotalTargetZeroColumnMap A π t₂) ≫
            (productTotalToTargetOppositeBicomplexStageComparison A t₁ t₂ ht).f 0).f q ≫
              ((lowerStupidTruncationProductTotalOppositeBicomplex A t₁).d 0 1).f q = 0 := by
    intro q
    -- After rewriting the zero-column comparison square, the target cycle relation is the stage-`t₁`
    -- cycle relation precomposed by the source truncation comparison.
    rw [hcol]
    simp [Category.assoc,
      lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles (A := A) (π := π) hπ t₁ q]
  calc
    productTotalToTargetOpStageMap A π hπ t₂ ≫
        total.map
          (productTotalToTargetOppositeBicomplexStageComparison A t₁ t₂ ht)
          (up ℤ) =
      product_total_zero_column_to_total
        ((lowerStupidTruncationProductTotalTargetZeroColumnMap A π t₂) ≫
          (productTotalToTargetOppositeBicomplexStageComparison A t₁ t₂ ht).f 0)
        hcompcycles := by
      -- First move the stage comparison through the owner zero-column totalization map.
      simpa [productTotalToTargetOpStageMap] using
        (productTotalZeroColumnToTotal_comp_total_map
          (lowerStupidTruncationProductTotalTargetZeroColumnMap A π t₂)
          (lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
            (A := A) (π := π) hπ t₂)
          (productTotalToTargetOppositeBicomplexStageComparison A t₁ t₂ ht)
          hcompcycles).symm
    _ =
      product_total_zero_column_to_total
        (lowerStupidTruncationComparison (productTotalTargetOp M) t₁ t₂ ht ≫
          lowerStupidTruncationProductTotalTargetZeroColumnMap A π t₁)
        hcompcycles := by
      rw [hcol]
    _ =
      lowerStupidTruncationComparison (productTotalTargetOp M) t₁ t₂ ht ≫
        productTotalToTargetOpStageMap A π hπ t₁ := by
      -- Then use the source-side naturality of the zero-column owner map.
      simpa [productTotalToTargetOpStageMap] using
        (productTotalZeroColumnToTotal_precomp
          (γ := lowerStupidTruncationComparison (productTotalTargetOp M) t₁ t₂ ht)
          (α := lowerStupidTruncationProductTotalTargetZeroColumnMap A π t₁)
          (hαcycles := lowerStupidTruncationProductTotalTargetZeroColumnMap_cycles
            (A := A) (π := π) hπ t₁)
          (hcompcycles := hcompcycles))

/-- Helper for Chap12 Lemma 12 26 4: after unop, the cutoff-stage cone at index `n` is acyclic.
This packages the already-proved stage quasi-isomorphism in the staircase indexing `t n = -n`. -/
private theorem productTotalToTargetStageConeAcyclic
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (n : ℕ) :
    ((CochainComplex.mappingCone
        (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))).unop).Acyclic := by
  -- This is exactly the stagewise acyclicity theorem specialized to the staircase cutoff.
  simpa [productTotalToTargetCutoff, productTotalToTargetOpStageMap] using
    (lowerStupidTruncationProductTotalToTarget_mappingConeAcyclic_unop
      (A := A) (π := π) hπ hExact₀ hEpi hExact (productTotalToTargetCutoff n))

/-- Helper for Chap12 Lemma 12 26 4: unopping the consecutive stage-comparison square yields the
predecessor map between neighboring cutoff-stage cones in the inverse system. -/
private noncomputable def productTotalToTargetStageConePredecessorMap
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (n : ℕ) :
    ((CochainComplex.mappingCone
        (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1)))).unop) ⟶
      ((CochainComplex.mappingCone
        (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))).unop) :=
  -- The opposite-side direct system becomes the desired inverse-system predecessor map after unop.
  (CochainComplex.mappingCone.map
      (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))
      (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1)))
      (lowerStupidTruncationComparison (productTotalTargetOp M)
        (productTotalToTargetCutoff (n + 1))
        (productTotalToTargetCutoff n)
        (productTotalToTargetCutoff_succ_le n))
      (total.map
        (productTotalToTargetOppositeBicomplexStageComparison A
          (productTotalToTargetCutoff (n + 1))
          (productTotalToTargetCutoff n)
          (productTotalToTargetCutoff_succ_le n))
        (up ℤ))
      (productTotalToTargetOpStageToStageCompare
        (A := A) (M := M) π hπ
        (productTotalToTargetCutoff (n + 1))
        (productTotalToTargetCutoff n)
        (productTotalToTargetCutoff_succ_le n))).unop

/-- Helper for Chap12 Lemma 12 26 4: the left cone coordinate sits in degree `q + 1`, so the
mapping-cone inclusion uses the standard identity `(q + 1) + (-1) = q`. -/
private theorem productTotalToTargetStageConeInl_degree_eq (q : ℤ) :
    q + 1 + (-1) = q := by
  omega

/-- Helper for Chap12 Lemma 12 26 4: degreewise, the opposite-side stage predecessor map on
mapping cones has a canonical retraction obtained by gluing the source truncation retraction and
the total-stage retraction along the two cone coordinates. -/
private noncomputable def productTotalToTargetStageConePredecessorMapComponentRetraction
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (n : ℕ) (q : ℤ) :
    (CochainComplex.mappingCone
        (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1)))).X q ⟶
      (CochainComplex.mappingCone
        (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))).X q :=
  let φ₁ := productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n)
  let φ₂ := productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1))
  -- The source coordinate retracts through the lower-truncation comparison, while the target
  -- coordinate retracts through the total-stage comparison.
  (CochainComplex.mappingCone.fst φ₂).1.v q (q + 1) rfl ≫
      lowerStupidTruncationComparisonFRetraction
        (productTotalTargetOp M)
        (productTotalToTargetCutoff (n + 1))
        (productTotalToTargetCutoff n)
        (productTotalToTargetCutoff_succ_le n)
        (q + 1) ≫
    (CochainComplex.mappingCone.inl φ₁).v (q + 1) q
      (productTotalToTargetStageConeInl_degree_eq q) +
    (CochainComplex.mappingCone.snd φ₂).v q q (add_zero q) ≫
      productTotalToTargetOppositeStageTotalComponentRetraction A n q ≫
        (CochainComplex.mappingCone.inr φ₁).f q

/-- Helper for Chap12 Lemma 12 26 4: the degree-`q` component of the opposite-side stage
predecessor map is split mono, with the coordinatewise retraction above as a right inverse. -/
private theorem productTotalToTargetStageConePredecessorMapComponent_comp_retraction
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (n : ℕ) (q : ℤ) :
    ((CochainComplex.mappingCone.map
        (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))
        (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1)))
        (lowerStupidTruncationComparison (productTotalTargetOp M)
          (productTotalToTargetCutoff (n + 1))
          (productTotalToTargetCutoff n)
          (productTotalToTargetCutoff_succ_le n))
        (total.map
          (productTotalToTargetOppositeBicomplexStageComparison A
            (productTotalToTargetCutoff (n + 1))
            (productTotalToTargetCutoff n)
            (productTotalToTargetCutoff_succ_le n))
          (up ℤ))
        (productTotalToTargetOpStageToStageCompare
          (A := A) (M := M) π hπ
          (productTotalToTargetCutoff (n + 1))
          (productTotalToTargetCutoff n)
          (productTotalToTargetCutoff_succ_le n))).f q) ≫
      productTotalToTargetStageConePredecessorMapComponentRetraction
        (A := A) (M := M) π hπ n q =
      𝟙
        ((CochainComplex.mappingCone
          (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))).X q) := by
  let φ₁ := productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n)
  let φ₂ := productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1))
  let a :=
    lowerStupidTruncationComparison (productTotalTargetOp M)
      (productTotalToTargetCutoff (n + 1))
      (productTotalToTargetCutoff n)
      (productTotalToTargetCutoff_succ_le n)
  let b :=
    total.map
      (productTotalToTargetOppositeBicomplexStageComparison A
        (productTotalToTargetCutoff (n + 1))
        (productTotalToTargetCutoff n)
        (productTotalToTargetCutoff_succ_le n))
      (up ℤ)
  let u :=
    CochainComplex.mappingCone.map φ₁ φ₂ a b
      (productTotalToTargetOpStageToStageCompare
        (A := A) (M := M) π hπ
        (productTotalToTargetCutoff (n + 1))
        (productTotalToTargetCutoff n)
        (productTotalToTargetCutoff_succ_le n))
  -- Compare the would-be split identity after the two canonical cone-coordinate inclusions.
  rw [CochainComplex.mappingCone.ext_from_iff φ₁ (q + 1) q rfl]
  constructor
  · -- The `inl` coordinate only sees the source truncation comparison and its chosen retraction.
    simp [u, a, b, φ₁, φ₂,
      productTotalToTargetStageConePredecessorMapComponentRetraction, Category.assoc,
      lowerStupidTruncationComparisonF_comp_retraction]
  · -- The `inr` coordinate only sees the total-stage comparison and its chosen retraction.
    simp [u, a, b, φ₁, φ₂,
      productTotalToTargetStageConePredecessorMapComponentRetraction, Category.assoc,
      productTotalToTargetOppositeStageTotalComponent_comp_retraction]

/-- Helper for Chap12 Lemma 12 26 4: after unop, each degree component of the cutoff-stage
predecessor map is surjective on the underlying abelian groups. -/
private theorem productTotalToTargetStageConePredecessorMap_unop_surjective
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (n : ℕ) (q : ℤ) :
    Function.Surjective
      (((productTotalToTargetStageConePredecessorMap
          (A := A) (M := M) π hπ n).f q).hom) := by
  intro x
  refine ⟨((Quiver.Hom.unop
      (productTotalToTargetStageConePredecessorMapComponentRetraction
        (A := A) (M := M) π hπ n q)).hom x), ?_⟩
  -- Unop reverses the split identity above, so the chosen retraction gives the required preimage.
  have hsplit := congrArg Quiver.Hom.unop
    (productTotalToTargetStageConePredecessorMapComponent_comp_retraction
      (A := A) (M := M) π hπ n q)
  exact congrArg (fun f ↦ f.hom x) hsplit

/-- Helper for Chap12 Lemma 12 26 4: the stage-to-stage comparison on the opposite bicomplex
followed by the later-stage inclusion is the earlier-stage inclusion. -/
private theorem productTotalToTargetOppositeBicomplexStageComparisonCompInclusion
    {A : AbCochainResolution}
    (n : ℕ) :
    productTotalToTargetOppositeBicomplexStageComparison A
        (productTotalToTargetCutoff (n + 1))
        (productTotalToTargetCutoff n)
        (productTotalToTargetCutoff_succ_le n) ≫
      lowerStupidTruncationProductTotalOppositeBicomplexInclusion A
        (productTotalToTargetCutoff (n + 1)) =
        lowerStupidTruncationProductTotalOppositeBicomplexInclusion A
          (productTotalToTargetCutoff n) := by
  ext q
  -- Evaluate the rowwise stage comparison at degree `q`, where it is exactly the owner
  -- lower-truncation comparison followed by the corresponding inclusion.
  simpa [productTotalToTargetOppositeBicomplexStageComparison,
    lowerStupidTruncationProductTotalOppositeBicomplexInclusion] using
    (lowerStupidTruncationComparisonCompInclusion
      ((productTotalOppositeBicomplex A).X q)
      (productTotalToTargetCutoff (n + 1))
      (productTotalToTargetCutoff n)
      (productTotalToTargetCutoff_succ_le n))

/-- Helper for Chap12 Lemma 12 26 4: the full mapping cone projects canonically to each
cutoff-stage cone by the stage/full comparison square. -/
private noncomputable def productTotalToTargetFullConeToStageCone
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (n : ℕ) :
    ((CochainComplex.mappingCone (productTotalToTargetOp A π hπ)).unop) ⟶
      ((CochainComplex.mappingCone
        (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))).unop) :=
  -- The full comparison square points from the stage cone into the full cone on the opposite
  -- side, so unopping it yields the required projection toward the cutoff stage.
  (CochainComplex.mappingCone.map
      (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))
      (productTotalToTargetOp A π hπ)
      (lowerStupidTruncationInclusion (productTotalTargetOp M)
        (productTotalToTargetCutoff n))
      (total.map
        (lowerStupidTruncationProductTotalOppositeBicomplexInclusion A
          (productTotalToTargetCutoff n))
        (up ℤ))
      (productTotalToTargetOpStageCompare
        (A := A) (M := M) π hπ (productTotalToTargetCutoff n))).unop

/-- Helper for Chap12 Lemma 12 26 4: the full-cone projections form a compatible family with
respect to the predecessor maps of the cutoff-stage tower. -/
private theorem productTotalToTargetFullConeToStageCone_compatible
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (n : ℕ) :
    productTotalToTargetFullConeToStageCone π hπ (n + 1) ≫
        productTotalToTargetStageConePredecessorMap π hπ n =
      productTotalToTargetFullConeToStageCone π hπ n := by
  have hSource :
      lowerStupidTruncationComparison (productTotalTargetOp M)
          (productTotalToTargetCutoff (n + 1))
          (productTotalToTargetCutoff n)
          (productTotalToTargetCutoff_succ_le n) ≫
        lowerStupidTruncationInclusion (productTotalTargetOp M)
          (productTotalToTargetCutoff (n + 1)) =
          lowerStupidTruncationInclusion (productTotalTargetOp M)
            (productTotalToTargetCutoff n) := by
    -- On the source complex, the owner lower-truncation comparison composes with the later-stage
    -- inclusion to the earlier-stage inclusion.
    simpa using
      (lowerStupidTruncationComparisonCompInclusion
        (productTotalTargetOp M)
        (productTotalToTargetCutoff (n + 1))
        (productTotalToTargetCutoff n)
        (productTotalToTargetCutoff_succ_le n))
  have hTarget :
      total.map
          (productTotalToTargetOppositeBicomplexStageComparison A
            (productTotalToTargetCutoff (n + 1))
            (productTotalToTargetCutoff n)
            (productTotalToTargetCutoff_succ_le n))
          (up ℤ) ≫
        total.map
          (lowerStupidTruncationProductTotalOppositeBicomplexInclusion A
            (productTotalToTargetCutoff (n + 1)))
          (up ℤ) =
          total.map
            (lowerStupidTruncationProductTotalOppositeBicomplexInclusion A
              (productTotalToTargetCutoff n))
            (up ℤ) := by
    -- On the target bicomplex total, apply totalization to the rowwise inclusion identity.
    simpa [Functor.map_comp] using
      congrArg (fun φ ↦ total.map φ (up ℤ))
        (productTotalToTargetOppositeBicomplexStageComparisonCompInclusion
          (A := A) n)
  apply Quiver.Hom.op_inj
  -- After op, the compatibility statement becomes the owner composition law for `mappingCone.map`
  -- with both composite comparison maps collapsed to the stage-`n` inclusions.
  simpa [productTotalToTargetFullConeToStageCone,
    productTotalToTargetStageConePredecessorMap, op_comp, hSource, hTarget, Category.assoc] using
    (CochainComplex.mappingCone.map_comp
      (φ₁ := productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))
      (φ₂ := productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1)))
      (φ₃ := productTotalToTargetOp A π hπ)
      (a := lowerStupidTruncationComparison (productTotalTargetOp M)
        (productTotalToTargetCutoff (n + 1))
        (productTotalToTargetCutoff n)
        (productTotalToTargetCutoff_succ_le n))
      (b := total.map
        (productTotalToTargetOppositeBicomplexStageComparison A
          (productTotalToTargetCutoff (n + 1))
          (productTotalToTargetCutoff n)
          (productTotalToTargetCutoff_succ_le n))
        (up ℤ))
      (a' := lowerStupidTruncationInclusion (productTotalTargetOp M)
        (productTotalToTargetCutoff (n + 1)))
      (b' := total.map
        (lowerStupidTruncationProductTotalOppositeBicomplexInclusion A
          (productTotalToTargetCutoff (n + 1)))
        (up ℤ))
      (comm := productTotalToTargetOpStageToStageCompare
        (A := A) (M := M) π hπ
        (productTotalToTargetCutoff (n + 1))
        (productTotalToTargetCutoff n)
        (productTotalToTargetCutoff_succ_le n))
      (comm' := productTotalToTargetOpStageCompare
        (A := A) (M := M) π hπ (productTotalToTargetCutoff (n + 1))))

/-- Helper for Chap12 Lemma 12 26 4: the cutoff-stage cones form a sequential inverse system
indexed by `ℕᵒᵖ`. -/
private noncomputable abbrev productTotalToTargetStageConeTowerSeq
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    ℕᵒᵖ ⥤ AbCochainComplex :=
  CategoryTheory.Functor.ofOpSequence
    (fun n ↦
      productTotalToTargetStageConePredecessorMap
        (A := A) (M := M) π hπ n)

/-- Helper for Chap12 Lemma 12 26 4: the `OrderDual ℕ` tower is the canonical reindexing of the
sequential `ℕᵒᵖ` tower used by `Functor.ofOpSequence`. -/
private noncomputable abbrev productTotalToTargetStageConeTower
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    OrderDual ℕ ⥤ AbCochainComplex :=
  ((CategoryTheory.orderDualEquivalence ℕ).inverse) ⋙
    productTotalToTargetStageConeTowerSeq (A := A) (M := M) π hπ

/-- Helper for Chap12 Lemma 12 26 4: the sequential tower map on the successor morphism is the
stored predecessor map between consecutive cutoff cones. -/
private theorem productTotalToTargetStageConeTowerSeq_map_succ
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (n : ℕ) :
    (productTotalToTargetStageConeTowerSeq (A := A) (M := M) π hπ).map
        (homOfLE (Nat.le_add_right n 1)).op =
      productTotalToTargetStageConePredecessorMap
        (A := A) (M := M) π hπ n := by
  -- `Functor.ofOpSequence` is built precisely so that the successor map is definitionally the
  -- chosen predecessor morphism.
  simpa [productTotalToTargetStageConeTowerSeq] using
    (CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ
      (X := fun n : ℕ ↦
        ((CochainComplex.mappingCone
            (productTotalToTargetOpStageMap A π hπ
              (productTotalToTargetCutoff n))).unop))
      (f := fun n : ℕ ↦
        productTotalToTargetStageConePredecessorMap
          (A := A) (M := M) π hπ n)
      n)

/-- Helper for Chap12 Lemma 12 26 4: the compatible full-cone projections assemble to a natural
transformation from the constant full cone into the sequential cutoff-stage tower. -/
private theorem productTotalToTargetFullConeToStageConeSeq_naturality
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (n : ℕ) :
    (Functor.const ℕᵒᵖ
        ((CochainComplex.mappingCone (productTotalToTargetOp A π hπ)).unop)).map
        (homOfLE (Nat.le_add_right n 1)).op ≫
      productTotalToTargetFullConeToStageCone (A := A) (M := M) π hπ n =
        productTotalToTargetFullConeToStageCone (A := A) (M := M) π hπ (n + 1) ≫
          (productTotalToTargetStageConeTowerSeq (A := A) (M := M) π hπ).map
            (homOfLE (Nat.le_add_right n 1)).op := by
  -- On the constant source tower the transition map is the identity, so naturality is exactly the
  -- previously proved compatibility with the predecessor map.
  simpa [productTotalToTargetStageConeTowerSeq_map_succ] using
    (productTotalToTargetFullConeToStageCone_compatible
      (A := A) (M := M) π hπ n).symm

/-- Helper for Chap12 Lemma 12 26 4: the full-cone projections define a natural transformation to
the sequential cutoff-stage tower. -/
private noncomputable abbrev productTotalToTargetFullConeToStageConeNatTransSeq
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    Functor.const ℕᵒᵖ
        ((CochainComplex.mappingCone (productTotalToTargetOp A π hπ)).unop) ⟶
      productTotalToTargetStageConeTowerSeq (A := A) (M := M) π hπ :=
  CategoryTheory.NatTrans.ofOpSequence
    (fun n ↦ productTotalToTargetFullConeToStageCone (A := A) (M := M) π hπ n)
    (productTotalToTargetFullConeToStageConeSeq_naturality
      (A := A) (M := M) π hπ)

/-- Helper for Chap12 Lemma 12 26 4: reindexing the sequential compatible family along
`OrderDual ℕ ≌ ℕᵒᵖ` gives the source-facing tower map into the cutoff-stage inverse system. -/
private noncomputable abbrev productTotalToTargetFullConeToStageConeNatTrans
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    Functor.const (OrderDual ℕ)
        ((CochainComplex.mappingCone (productTotalToTargetOp A π hπ)).unop) ⟶
      productTotalToTargetStageConeTower (A := A) (M := M) π hπ :=
  Functor.whiskerLeft ((CategoryTheory.orderDualEquivalence ℕ).inverse)
    (productTotalToTargetFullConeToStageConeNatTransSeq (A := A) (M := M) π hπ)

/-- Helper for Chap12 Lemma 12 26 4: the compatible full-cone projections induce the canonical
comparison from the full mapping cone to the inverse limit of the cutoff-stage tower. -/
private noncomputable abbrev productTotalToTargetFullConeToStageConeLimitMap
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    ((CochainComplex.mappingCone (productTotalToTargetOp A π hπ)).unop) ⟶
      limit (productTotalToTargetStageConeTower (A := A) (M := M) π hπ) :=
  limit.lift _ <|
    Cone.mk
      ((CochainComplex.mappingCone (productTotalToTargetOp A π hπ)).unop)
      (productTotalToTargetFullConeToStageConeNatTrans (A := A) (M := M) π hπ)

/-- Helper for Chap12 Lemma 12 26 4: after projecting the canonical full-cone-to-limit map to a
fixed stage, the `fst` coordinate is exactly the lower-truncation inclusion on the source side. -/
private theorem productTotalToTargetFullConeToStageConeLimitMap_fst_π
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (j : OrderDual ℕ) (q : ℤ) :
    ((productTotalToTargetFullConeToStageConeLimitMap
        (A := A) (M := M) π hπ).f q) ≫
        (limit.π (productTotalToTargetStageConeTower (A := A) (M := M) π hπ) j).f q ≫
          (CochainComplex.mappingCone.fst
            ((productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff j)).unop)).1.v
            q (q + 1) rfl =
      (CochainComplex.mappingCone.fst
        ((productTotalToTargetOp A π hπ).unop)).1.v q (q + 1) rfl ≫
          ((lowerStupidTruncationInclusion
            (productTotalTargetOp M)
            (productTotalToTargetCutoff j)).unop).f (q + 1) := by
  -- First collapse the limit map to the stage-`j` projection, then read off the `fst`
  -- coordinate of the explicit mapping-cone comparison.
  simp [productTotalToTargetFullConeToStageConeLimitMap,
    productTotalToTargetFullConeToStageConeNatTrans,
    productTotalToTargetFullConeToStageConeNatTransSeq,
    productTotalToTargetFullConeToStageCone, Category.assoc]

/-- Helper for Chap12 Lemma 12 26 4: after projecting the canonical full-cone-to-limit map to a
fixed stage, the `snd` coordinate is exactly the stage/full comparison on the total side. -/
private theorem productTotalToTargetFullConeToStageConeLimitMap_snd_π
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (j : OrderDual ℕ) (q : ℤ) :
    ((productTotalToTargetFullConeToStageConeLimitMap
        (A := A) (M := M) π hπ).f q) ≫
        (limit.π (productTotalToTargetStageConeTower (A := A) (M := M) π hπ) j).f q ≫
          (CochainComplex.mappingCone.snd
            ((productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff j)).unop)).v
            q q (add_zero q) =
      (CochainComplex.mappingCone.snd
        ((productTotalToTargetOp A π hπ).unop)).v q q (add_zero q) ≫
          ((total.map
            (lowerStupidTruncationProductTotalOppositeBicomplexInclusion A
              (productTotalToTargetCutoff j))
            (up ℤ)).unop).f q := by
  -- First collapse the limit map to the stage-`j` projection, then read off the `snd`
  -- coordinate of the explicit mapping-cone comparison.
  simp [productTotalToTargetFullConeToStageConeLimitMap,
    productTotalToTargetFullConeToStageConeNatTrans,
    productTotalToTargetFullConeToStageConeNatTransSeq,
    productTotalToTargetFullConeToStageCone, Category.assoc]

/-- Helper for Lemma 12.26.4: acyclicity transports across an isomorphism of cochain complexes. -/
private theorem acyclic_of_iso
    {K L : AbCochainComplex} (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Acyclicity is exactness degreewise, and exactness transports across isomorphic complexes.
  rw [HomologicalComplex.acyclic_iff] at hK ⊢
  intro n
  exact (hK n).of_iso e

/-- Helper for Lemma 12.26.4: the inverse limit of the cutoff-stage mapping-cone tower is
acyclic once compatible primitives are constructed degreewise. -/
/-- Helper for Chap12 Lemma 12 26 4: a primitive in stage `n` lifts one step up the cutoff
tower after correcting by a boundary coming from the predecessor mismatch. -/
private theorem liftPrimitiveAlongStagePredecessor
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (n : ℕ) (q : ℤ)
    (xNext :
      ((CochainComplex.mappingCone
        (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1)))).unop).X q)
    (hxNext :
      (((CochainComplex.mappingCone
          (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1)))).unop).d
        q (q + 1)) xNext = 0)
    (yPrev :
      ((CochainComplex.mappingCone
        (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))).unop).X (q - 1))
    (hyPrev :
      (((CochainComplex.mappingCone
          (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))).unop).d
        (q - 1) q) yPrev =
          (((productTotalToTargetStageConePredecessorMap
              (A := A) (M := M) π hπ n).f q).hom xNext)) :
    ∃ yNext :
        ((CochainComplex.mappingCone
          (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1)))).unop).X
          (q - 1),
      (((CochainComplex.mappingCone
          (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1)))).unop).d
        (q - 1) q) yNext = xNext ∧
        (((productTotalToTargetStageConePredecessorMap
            (A := A) (M := M) π hπ n).f (q - 1)).hom yNext) = yPrev := by
  let stagePrev :=
    ((CochainComplex.mappingCone
      (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff n))).unop)
  let stageNext :=
    ((CochainComplex.mappingCone
      (productTotalToTargetOpStageMap A π hπ (productTotalToTargetCutoff (n + 1)))).unop)
  let pred := productTotalToTargetStageConePredecessorMap (A := A) (M := M) π hπ n
  let predQ : stageNext.X q →+ stagePrev.X q := (pred.f q).hom
  let predQMinusOne : stageNext.X (q - 1) →+ stagePrev.X (q - 1) := (pred.f (q - 1)).hom
  let predQMinusTwo : stageNext.X (q - 2) →+ stagePrev.X (q - 2) := (pred.f (q - 2)).hom
  have hStageNextAcyclic : stageNext.Acyclic :=
    productTotalToTargetStageConeAcyclic
      (A := A) (M := M) π hπ hExact₀ hEpi hExact (n + 1)
  have hStagePrevAcyclic : stagePrev.Acyclic :=
    productTotalToTargetStageConeAcyclic
      (A := A) (M := M) π hπ hExact₀ hEpi hExact n
  have hStageNextExact : stageNext.ExactAt q := by
    rw [HomologicalComplex.acyclic_iff] at hStageNextAcyclic
    exact hStageNextAcyclic q
  have hStagePrevExact : stagePrev.ExactAt (q - 1) := by
    rw [HomologicalComplex.acyclic_iff] at hStagePrevAcyclic
    exact hStagePrevAcyclic (q - 1)
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_of_hasForget] at hStageNextExact
  obtain ⟨yRaw, hyRaw⟩ := hStageNextExact xNext hxNext
  let mismatch : stagePrev.X (q - 1) := predQMinusOne yRaw - yPrev
  have hPredDifferential :
      (stagePrev.d (q - 1) q) (predQMinusOne yRaw) = predQ xNext := by
    -- Evaluate the chain-map commutativity of the predecessor morphism on the chosen primitive.
    have hcomm :=
      congrArg (fun f ↦ f.hom yRaw) (pred.comm (q - 1) q)
    simpa [stagePrev, stageNext, predQ, predQMinusOne, hyRaw] using hcomm
  have hMismatchCocycle :
      (stagePrev.d (q - 1) q) mismatch = 0 := by
    -- The mismatch is a cocycle because both terms differentiate to the same predecessor image.
    simp [mismatch, hPredDifferential, hyPrev]
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_of_hasForget] at hStagePrevExact
  obtain ⟨zPrev, hzPrev⟩ := hStagePrevExact mismatch hMismatchCocycle
  obtain ⟨zNext, hzNext⟩ :=
    productTotalToTargetStageConePredecessorMap_unop_surjective
      (A := A) (M := M) π hπ n (q - 2) zPrev
  let yNext : stageNext.X (q - 1) := yRaw - (stageNext.d (q - 2) (q - 1)) zNext
  refine ⟨yNext, ?_, ?_⟩
  · -- Subtracting a boundary preserves the primitive equation because `d ≫ d = 0`.
    have hdSquared :
        (stageNext.d (q - 2) (q - 1)) ((stageNext.d (q - 1) q) zNext) = 0 := by
      simpa using congrArg (fun f ↦ f.hom zNext) (stageNext.d_comp_d (q - 2) (q - 1) q)
    simp [yNext, hyRaw, hdSquared]
  · -- The chosen boundary correction kills the predecessor mismatch by construction.
    have hPredBoundary :
        predQMinusOne ((stageNext.d (q - 2) (q - 1)) zNext) =
          (stagePrev.d (q - 2) (q - 1)) zPrev := by
      have hcomm :=
        congrArg (fun f ↦ f.hom zNext) (pred.comm (q - 2) (q - 1))
      simpa [stagePrev, stageNext, predQMinusOne, predQMinusTwo, hzNext] using hcomm.symm
    simp [yNext, mismatch, hPredBoundary, hzPrev]

/-- Helper for Lemma 12.26.4: the inverse limit of the cutoff-stage mapping-cone tower is
acyclic once compatible primitives are constructed degreewise. -/
private theorem productTotalToTargetStageConeTowerLimitAcyclic
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1)) :
    (limit (productTotalToTargetStageConeTower (A := A) (M := M) π hπ)).Acyclic := by
  classical
  -- Route correction: the hard part is no longer producing one successor primitive, but packaging
  -- the recursively corrected primitives into a genuine section of the evaluated limit tower.
  refine limitAcyclicOfCocyclePrimitives _ ?_
  intro q x hx
  let F := productTotalToTargetStageConeTower (A := A) (M := M) π hπ
  let xSection :
      ((F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) q) ⋙
        forget AddCommGrpCat).sections :=
    underlyingSectionsOfLimit
      (F := (F ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) q))
      ((limitDegreeIso F q).hom x)
  -- TODO: build compatible degree-`q - 1` primitives by finite-prefix recursion, using
  -- `liftPrimitiveAlongStagePredecessor` at each successor step, then package the resulting
  -- section with `limitOfUnderlyingSections` and check `d y = x` via `limitDegree_ext`.
  sorry

/-- Helper for Lemma 12.26.4: the canonical map from the full mapping cone to the inverse limit
of cutoff-stage cones is an isomorphism. -/
private theorem productTotalToTargetFullConeToStageConeLimitMap_isIso
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    IsIso (productTotalToTargetFullConeToStageConeLimitMap (A := A) (M := M) π hπ) := by
  -- Route correction: it is enough to prove that every degree component is an isomorphism in
  -- `AddCommGrpCat`, because `HomologicalComplex.isIso_of_components` then upgrades the result.
  apply HomologicalComplex.isIso_of_components
  intro q
  -- TODO: recover the source coordinate from any retained stage, recover the total coordinate
  -- antidiagonal-by-antidiagonal, prove both are independent of the chosen retained stages, and
  -- combine the resulting degreewise bijection with `ConcreteCategory.isIso_iff_bijective`.
  sorry

/-- Helper for Lemma 12.26.4: the full opposite-side comparison follows from the cutoff-stage
mapping-cone tower once the inverse-limit acyclicity and full-cone comparison are available. -/
private theorem productTotalToTargetOp_quasiIso
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1)) :
    QuasiIso (productTotalToTargetOp A π hπ) := by
  -- Route correction: a fixed cutoff stage is not degreewise equal to the full product total.
  -- In total degree `q`, the stage at cutoff `t` only retains columns `0 ≤ p ≤ q - t`, while the
  -- full product total can still have infinitely many coordinates in rows `q - p < t`.
  -- Hence the attempted retained-degree lemma
  -- `productTotalOppositeStageTotalComponent_isIso_of_ge` is false without extra vanishing
  -- hypotheses, so the proof must return to the genuine inverse-limit comparison.
  -- The sound remaining route is already mostly packaged:
  -- `productTotalToTargetStageConeTower` gives the cutoff-stage inverse system,
  -- `productTotalToTargetFullConeToStageConeLimitMap` is the canonical map from the full cone to
  -- its stage tower limit, and `limitAcyclicOfCocyclePrimitives` reduces acyclicity of that limit
  -- to degreewise primitive lifting. The new generic helpers
  -- `underlyingSectionsOfLimit_injective` and
  -- `orderDualNat_limitProjection_surjective_of_surjective`
  -- now package the basic inverse-limit bookkeeping needed for that descent.
  have hLimitAcyclic :
      (limit (productTotalToTargetStageConeTower (A := A) (M := M) π hπ)).Acyclic :=
    productTotalToTargetStageConeTowerLimitAcyclic
      (A := A) (M := M) π hπ hExact₀ hEpi hExact
  have hLimitMapIso :
      IsIso (productTotalToTargetFullConeToStageConeLimitMap (A := A) (M := M) π hπ) :=
    productTotalToTargetFullConeToStageConeLimitMap_isIso (A := A) (M := M) π hπ
  have hFullConeAcyclic :
      ((CochainComplex.mappingCone (productTotalToTargetOp A π hπ)).unop).Acyclic := by
    -- Transport acyclicity from the inverse limit back to the full mapping cone.
    exact
      acyclic_of_iso
        (asIso (productTotalToTargetFullConeToStageConeLimitMap (A := A) (M := M) π hπ)).symm
        hLimitAcyclic
  have hConeAcyclic :
      (CochainComplex.mappingCone (productTotalToTargetOp A π hπ)).Acyclic := by
    -- Return to the opposite-side cone spelling expected by `quasiIso_of_mappingCone_acyclic`.
    simpa using hFullConeAcyclic.op
  -- Once the full mapping cone is acyclic, the standard mapping-cone criterion gives the result.
  exact quasiIso_of_mappingCone_acyclic _ hConeAcyclic

/-- Lemma 12.26.4: if
`\cdots \to A_2^\bullet \to A_1^\bullet \to A_0^\bullet \to M^\bullet \to 0`
is an exact complex of complexes of abelian groups, then the induced map from the product total
complex `Tot_π(A)` of the associated double complex to `M^\bullet` is a quasi-isomorphism. -/
@[stacks 0E1R]
theorem productTotalToTarget_quasiIso
    {A : AbCochainResolution}
    {M : AbCochainComplex}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1)) :
    QuasiIso (productTotalToTarget A π hπ) := by
  -- Route correction: use the opposite-side cutoff stages first, then transport back with the
  -- already-verified opposite/unop comparison.
  have hOp : QuasiIso (productTotalToTargetOp A π hπ) :=
    productTotalToTargetOp_quasiIso π hπ hExact₀ hEpi hExact
  -- Once the opposite-side map is handled, the source-facing theorem is immediate by transport.
  exact productTotalToTarget_quasiIso_of_op π hπ hOp

end
