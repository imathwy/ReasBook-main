import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import stacks_project.Chap12.Lemma_12_26_2

open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂ Opposite

noncomputable section

universe v u

/-
Domain-style sampling for Lemma 12.26.4 in the product-total domain:
- primary domain: product total complexes attached to an augmented row
  `⋯ ⟶ A₂^• ⟶ A₁^• ⟶ A₀^• ⟶ M^•`;
- sampled owner abstractions:
  * `HomologicalComplex₂.productTotal` from `Lemma_12_26_2` as the shared bicomplex-level owner
    on
    bicomplexes;
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

variable [HasZeroObject C]

/-- The reindexed bicomplex obtained by placing outer degree `n` in horizontal degree `-n`. -/
private abbrev augmentedRowBicomplex (A : CochainResolution) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  A.extend embeddingDownNat

/-- The canonical identification of the horizontal degree-zero row in the reindexed bicomplex with
the original complex `A₀^\bullet`. -/
private abbrev augmentedRowBicomplexZeroIso
    (A : CochainResolution) :
    (augmentedRowBicomplex A).X 0 ≅ A.X 0 :=
  A.extendXIso embeddingDownNat (by simp)

local notation "Tot_π(" A ")" => HomologicalComplex₂.productTotal (augmentedRowBicomplex A)

/-- The zeroth row of the opposite-side bicomplex in degree `n` is the opposite of
`A₀^{-n}`. -/
private theorem productTotalZeroRow_objEq
    (A : CochainResolution) (n : ℤ) :
    ((HomologicalComplex₂.productTotalOpBicomplex (augmentedRowBicomplex A)).X 0).X n =
      op (((augmentedRowBicomplex A).X 0).X (-n)) := by
  simp [HomologicalComplex₂.productTotalOpBicomplex, HomologicalComplex₂.productTotalCochainOp,
    CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
    HomologicalComplex.opEquivalence]

variable [HasCountableProducts C]

variable (A : CochainResolution)
variable {M : CochainComplex₀} (π : A.X 0 ⟶ M)

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
            (up ℤ) 0 n n (show ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (0, n) = n by simp)

/-- The opposite-side comparison morphism from the transported target complex into the coproduct
total. -/
private def productTotalToTargetOp
    (A : CochainResolution) {M : CochainComplex₀} (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    productTotalTargetOp M ⟶ HomologicalComplex₂.productTotalOp (augmentedRowBicomplex A) where
  f := productTotalToTargetOpComponent A π
  comm' := by
    intro i j hij
    sorry

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
    QuasiIso (productTotalToTarget A π hπ) := sorry

end
