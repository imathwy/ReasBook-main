import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import StacksProject_2024.stacks_project.Chap12.Lemma_12_13_9
import StacksProject_2024.stacks_project.Chap12.Lemma_12_26_ProductTotalAPI

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
private theorem product_total_zero_row_to_total_comm
    {K : CochainComplex Cᵒᵖ ℤ} {B : HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ)} [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀ᵒᵖ).mapHomologicalComplex (up ℤ)).obj B)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (B.X p).d 0 1 = 0)
    (n n' : ℤ) (_ : (up ℤ).Rel n n') :
    product_total_zero_row_to_total_component α n ≫ (B.total (up ℤ)).d n n' =
      K.d n n' ≫ product_total_zero_row_to_total_component α n' := by
  -- TODO: replay the `D₁ + D₂` calculation from Lemma 12.25.4 locally, in the opposite-side
  -- orientation used here, so the row-zero owner becomes a packaged chain map without importing
  -- the broken Chapter 12 dependency chain behind `Lemma_12_25_4`.
  sorry

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
  eqToHom (productTotalTargetOp_objEq M n) ≫
    (π.f (-n)).op ≫
      ((augmentedRowBicomplexZeroIso A).hom.f (-n)).op ≫
        eqToHom (productTotalZeroRow_objEq A n).symm ≫
          (HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).ιTotal
            (up ℤ) 0 n n (product_total_zero_column_total_degree n)

/-- Helper for Lemma 12.26.4: the zero-column comparison map is the component family underlying
`productTotalToTargetOpComponent` before inserting the total inclusion. -/
private noncomputable def product_total_target_zero_column_component
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M) (n : ℤ) :
    (productTotalTargetOp M).X n ⟶
      ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).X 0).X n :=
  eqToHom (productTotalTargetOp_objEq M n) ≫
    (π.f (-n)).op ≫
      ((augmentedRowBicomplexZeroIso A).hom.f (-n)).op ≫
        eqToHom (productTotalZeroRow_objEq A n).symm

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

/-- Helper for Lemma 12.26.4: the raw zero-column component family is the transported opposite of
the augmentation morphism from the zeroth row to the target. -/
private theorem product_total_target_zero_column_map_f
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M) (n : ℤ) :
    (((CochainComplex.opEquivalence C).functor.map
        (Quiver.Hom.op ((augmentedRowBicomplexZeroIso A).hom ≫ π))).f n) =
      product_total_target_zero_column_component A π n := by
  -- Route correction: the remaining mismatch is a pure codomain transport created by
  -- `CochainComplex.opEquivalence`; the source side already matches the explicit component family.
  -- TODO: normalize the remaining codomain `eqToHom` inserted by `CochainComplex.opEquivalence`
  -- so the functorial component is literally the explicit zero-column family.
  sorry

/-- Helper for Lemma 12.26.4: the zero-column comparison into the opposite bicomplex is the
transported opposite of the augmentation morphism `A₀^\bullet ⟶ M^\bullet`. -/
private noncomputable def product_total_target_zero_column_map
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M) :
    productTotalTargetOp M ⟶
      ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).X 0) :=
  (CochainComplex.opEquivalence C).functor.map
    (Quiver.Hom.op ((augmentedRowBicomplexZeroIso A).hom ≫ π))

/-- Helper for Lemma 12.26.4: the packaged zero-column comparison has the expected degreewise
components. -/
private theorem product_total_target_zero_column_map_eq_component
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M) (n : ℤ) :
    (product_total_target_zero_column_map A π).f n =
      product_total_target_zero_column_component A π n := by
  -- The owner map was chosen precisely so that its degreewise components are the explicit
  -- opposite-side augmentation components.
  simpa [product_total_target_zero_column_map] using
    product_total_target_zero_column_map_f (C := C) A π n

/-- Helper for Lemma 12.26.4: the packaged zero-column comparison lands in the cycles of the
first horizontal differential. -/
private theorem product_total_target_zero_column_map_cycles
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (q : ℤ) :
    (product_total_target_zero_column_map A π).f q ≫
        ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).d 0 1).f q = 0 := by
  -- Route correction: the evaluated source relation
  -- `product_total_target_prev_column_comp_zero A π hπ` already supplies the vanishing composite
  -- on degree `-q`. The remaining missing ingredient is a transport-stable rewrite identifying
  -- the opposite horizontal differential on the zeroth column with the explicit expression that
  -- follows `product_total_target_zero_column_component A π q`.
  -- TODO: add that oriented transport lemma, then replay the short calculation that rewrites the
  -- packaged zero-column map into the evaluated opposite composite and kills it by the source
  -- relation.
  sorry

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
  -- The packaged zero-column owner already lands on the literal `(0,n)` summand; only the
  -- explicit description of the underlying zero-column family remains to be substituted.
  rw [product_total_zero_column_to_total_component_on_zero_summand]
  rw [product_total_target_zero_column_map_eq_component]
  -- Unfolding both owners shows that they are the same explicit component family followed by the
  -- canonical inclusion of the `(0,n)` summand.
  simpa [product_total_target_zero_column_component, productTotalToTargetOpComponent,
    Category.assoc]

/-- The opposite-side comparison morphism from the transported target complex into the coproduct
total. -/
private noncomputable def productTotalToTargetOp
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    productTotalTargetOp M ⟶ HomologicalComplex₂.productTotalOp (augmentedRowBicomplex A) :=
  product_total_zero_column_to_total
    (product_total_target_zero_column_map A π)
    (product_total_target_zero_column_map_cycles (A := A) (π := π) hπ)

/-- Helper for Lemma 12.26.4: after packaging the zero-column comparison through the generic
owner from Lemma 12.25.4, the old explicit component family is recovered degreewise. -/
private theorem productTotalToTargetOp_comm_unop
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
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

/-- The canonical comparison map from `Tot_π(A)` to the augmented target complex. -/
def productTotalToTarget
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    Tot_π(A) ⟶ M :=
  (((CochainComplex.opEquivalence C).inverse.map
    (productTotalToTargetOp A π hπ))).unop ≫
      (((CochainComplex.opEquivalence C).unitIso.app (op M)).unop).hom

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasCountableProducts 𝒜]

local notation "CochainComplex₀" => CochainComplex 𝒜 ℤ
local notation "CochainResolution" => ChainComplex CochainComplex₀ ℕ

/-- Helper for Lemma 12.26.4: exactness of the augmented row of cochain complexes can be checked
degreewise, so every vertical degree yields an exact short complex of objects. -/
private theorem augmented_row_degreewise_exact
    {A : CochainResolution}
    {M : CochainComplex₀}
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
    {A : CochainResolution}
    {M : CochainComplex₀}
    (π : A.X 0 ⟶ M)
    (hEpi : Epi π)
    (q : ℤ) :
    Epi (π.f q) := by
  -- Reduce the complex-level epimorphism to degreewise epimorphy via the Chapter 12 bridge.
  letI : Epi π := hEpi
  exact (cochainComplex_epi_iff_degreewise_epi π).1 inferInstance q

-- Proof sketch: pass to the opposite category, where countable products in `𝒜` become countable
-- coproducts in `𝒜ᵒᵖ` and the product total complex becomes the unop of the canonical coproduct
-- total of the opposite bicomplex. The exact augmented row then becomes a coaugmented exact row
-- in the opposite category, and the product-total quasi-isomorphism follows from the
-- corresponding coproduct-total result by transporting back across opposites.
/-- Lemma 12.26.4: if
`\cdots \to A_2^\bullet \to A_1^\bullet \to A_0^\bullet \to M^\bullet \to 0`
is an exact augmented row of cochain complexes in an abelian category, then the induced map from
the product total complex `Tot_π(A)` of the associated double complex to `M^\bullet` is a
quasi-isomorphism. The ambient abelian category is assumed to have countable products so that the
product total exists. -/
theorem productTotalToTarget_quasiIso
    {A : CochainResolution}
    {M : CochainComplex₀}
    (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hEpi : Epi π)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1)) :
    QuasiIso (productTotalToTarget A π hπ) := by
  -- Route correction: do not force this through Lemma 12.26.2, whose proof route asks for exact
  -- kernel rows not present in the statement here. The source proof instead shifts the augmented
  -- row, identifies the shifted product total with an extension of `M^\bullet` by `Tot_π(A)[1]`,
  -- and reduces to the zero-target case by a staircase lifting argument.
  --
  -- TODO: the opposite-side comparison map is now isolated from the broken `Lemma_12_26_2`
  -- import chain. The remaining source-faithful work is to build the shifted short exact sequence
  -- `0 ⟶ M ⟶ S ⟶ Tot_π(A)⟦1⟧ ⟶ 0`, prove the zero-target staircase acyclicity lemma, and finish
  -- by the long exact cohomology sequence. The verified local inputs for that staircase are now:
  -- `augmented_row_degreewise_exact π hπ hExact₀ q`, giving exactness in each vertical degree,
  -- and `augmentation_degreewise_epi π hEpi q`, giving the base-step surjectivity onto `M^q`.
  sorry

end
