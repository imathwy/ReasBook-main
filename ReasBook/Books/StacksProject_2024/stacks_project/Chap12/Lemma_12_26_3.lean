import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import StacksProject_2024.Chap12.Lemma_12_26_1
import StacksProject_2024.Chap12.Lemma_12_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂ Opposite

noncomputable section

universe v u

/-
Domain-style sampling for Lemma 12.26.3 in the product-total domain:
- primary domain: coaugmented rows of cochain complexes, their rowwise cokernels, and the
  associated product total complexes;
- sampled owner abstractions:
  * `coaugmentedColumnBicomplex` and `coaugmentedColumnBicomplexZeroIso` from `Lemma_12_26_1` for
    the canonical reindexed bicomplex and its degree-zero-row comparison;
  * `HomologicalComplex₂.productTotal` from `Lemma_12_26_2` as the shared bicomplex-level
    product-total owner;
  * `HomologicalComplex.opcyclesFunctor` and `HomologicalComplex.opcyclesMap` for the canonical
    rowwise owners of the cokernels `Coker(d^q)` after the standard shift `q ↦ q + 1`;
  * `ShortComplex.Exact` together with explicit `Mono` data as the canonical owner for a source
    hypothesis of the form `0 ⟶ X₁ ⟶ X₂ ⟶ X₃`, which is exact at `X₂` and left exact at `X₁`
    without forcing a terminal-zero `Epi` hypothesis;
  * `HomologicalComplex.opcyclesOpIso` for the opposite-side identification between those
    shifted opcycles rows and the corresponding cycles rows on the opposite complexes;
  * `HomologicalComplex₂.productTotalOp` and `HomologicalComplex₂.ιTotal` for the opposite-side
    total and its canonical summand inclusions;
  * `CochainComplex.opEquivalence` and `ChainComplex.cochainComplexEquivalence` for transporting
    the opposite bicomplex back to a cochain complex.

Layer triage:
- `source-facing`: the rowwise cokernel exactness assumptions from the source, the local notation
  `Tot_π(A)`, and the
  comparison `coaugmentedToProductTotal A ι hι : M ⟶ Tot_π(A)`;
- `core/canonical`: `HomologicalComplex₂.productTotal (coaugmentedColumnBicomplex A)` together
  with the shifted row owner
  `((opcyclesFunctor 𝒜 (up ℤ) (q + 1)).mapHomologicalComplex (up ℕ)).obj A`;
- `bridge/view`: the degree-zero row inclusion in that opposite total and the standard
  `Coker(d^q) ≅ opcycles(q + 1)` identification built into `opcyclesFunctor`.

Primitive data are only the row `A` and the coaugmentation `ι : M ⟶ A.X 0`. The rowwise cokernel
complexes are derived API from the shifted `opcycles` owner. The leading `0 ⟶` exactness in the
source is not a new wrapper object: it is canonical `ShortComplex.Exact` data plus the
corresponding `Mono` hypothesis on the first map. This file should therefore reuse the shared
Chapter 12 bicomplex owner, the canonical rowwise cokernel owner, and the standard
`Exact`-plus-`Mono` interface rather than rebuilding local copies of those declarations.
-/

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

local notation "CochainComplex₀" => CochainComplex C ℤ
local notation "CochainComplexSequence" => CochainComplex CochainComplex₀ ℕ

variable (A : CochainComplexSequence)
variable {M : CochainComplex₀} (ι : M ⟶ A.X 0)

/-- The opposite-side source complex corresponding to `M^\bullet`. -/
private abbrev productTotalSourceOp
    (M : CochainComplex₀) :
    CochainComplex Cᵒᵖ ℤ :=
  (CochainComplex.opEquivalence C).functor.obj (op M)

local notation "Tot_π(" A ")" =>
  HomologicalComplex₂.productTotal
    (coaugmentedColumnBicomplex A : HomologicalComplex₂ C (up ℤ) (up ℤ))

section

omit [HasZeroObject C]

/-- The degree-`n` term of the opposite-side source identifies with `M^{-n}` in
`𝒜ᵒᵖ`. -/
private theorem productTotalSourceOp_objEq
    (M : CochainComplex₀) (n : ℤ) :
    (productTotalSourceOp M).X n = op (M.X (-n)) := by
  simp [productTotalSourceOp, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence]

end

/-- The zeroth row of the opposite-side bicomplex in degree `n` is the opposite of `A₀^{-n}`. -/
private theorem productTotalZeroRow_objEq
    (A : CochainComplexSequence) (n : ℤ) :
    ((HomologicalComplex₂.productTotalOpBicomplex
        (coaugmentedColumnBicomplex A : HomologicalComplex₂ C (up ℤ) (up ℤ))).X 0).X n =
      op (((coaugmentedColumnBicomplex A : HomologicalComplex₂ C (up ℤ) (up ℤ)).X 0).X (-n)) := by
  simp [HomologicalComplex₂.productTotalOpBicomplex, HomologicalComplex₂.productTotalCochainOp,
    CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
    HomologicalComplex.opEquivalence]

variable [HasCountableProducts C]

/-- Helper for Lemma 12.26.3: under the degree identifications
`(productTotalSourceOp M).X n = op (M.X (-n))`, the transported opposite differential is exactly
the opposite of the original cochain differential on `M^\bullet`. -/
private theorem productTotalSourceOp_d_eq
    (M : CochainComplex₀) {n n' : ℤ} (hn : (up ℤ).Rel n n') :
    eqToHom (productTotalSourceOp_objEq M n) ≫ (productTotalSourceOp M).d n n' ≫
      eqToHom (productTotalSourceOp_objEq M n').symm =
        (M.d (-n') (-n)).op := by
  -- Reindexing through the opposite/cochain equivalences only reverses the degree labels, so the
  -- differential is the original cochain differential viewed in the opposite category.
  have hnn' : n + 1 = n' := by
    simpa [ComplexShape.up, ComplexShape.up'] using hn
  subst hnn'
  simp [productTotalSourceOp, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence]

/-- Helper for Lemma 12.26.3: under the degree identifications for the zeroth row of the opposite
product-total bicomplex, the transported differential is the opposite of the original cochain
differential on `A.X 0`. -/
private theorem productTotalZeroRow_d_eq
    (A : CochainComplexSequence) {n n' : ℤ} (hn : (up ℤ).Rel n n') :
    eqToHom (productTotalZeroRow_objEq A n) ≫
      ((HomologicalComplex₂.productTotalOpBicomplex
          (coaugmentedColumnBicomplex A : HomologicalComplex₂ C (up ℤ) (up ℤ))).X 0).d n n' ≫
        eqToHom (productTotalZeroRow_objEq A n').symm =
          (((coaugmentedColumnBicomplex A : HomologicalComplex₂ C (up ℤ) (up ℤ)).X 0).d
            (-n') (-n)).op := by
  -- Reindexing the zeroth row through the opposite/cochain equivalences only reverses the degree
  -- labels, so the row differential is the original cochain differential viewed in `Cᵒᵖ`.
  have hnn' : n + 1 = n' := by
    simpa [ComplexShape.up, ComplexShape.up'] using hn
  subst hnn'
  simp [HomologicalComplex₂.productTotalOpBicomplex, HomologicalComplex₂.productTotalCochainOp,
    CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
    HomologicalComplex.opEquivalence]

/-- The degree-`n` component of the canonical bridge map
`M^• ⟶ Tot_π(A)` induced by `M^• ⟶ A₀^•`. -/
private noncomputable def productTotalToSourceOpComponent
    (A : CochainComplexSequence) {M : CochainComplex₀} (ι : M ⟶ A.X 0) (n : ℤ) :
    (HomologicalComplex₂.productTotalOp
      (coaugmentedColumnBicomplex A : HomologicalComplex₂ C (up ℤ) (up ℤ))).X n ⟶
      (productTotalSourceOp M).X n :=
  (HomologicalComplex₂.productTotalOpBicomplex
    (coaugmentedColumnBicomplex A : HomologicalComplex₂ C (up ℤ) (up ℤ))).totalDesc
    fun p q h ↦
    if hp : p = 0 then
      let hq : q = n := by simpa [hp] using h
      (HomologicalComplex₂.XXIsoOfEq Cᵒᵖ (up ℤ) (up ℤ)
          (HomologicalComplex₂.productTotalOpBicomplex
            (coaugmentedColumnBicomplex A : HomologicalComplex₂ C (up ℤ) (up ℤ)))
          hp (rfl : q = q)).hom ≫
        eqToHom (productTotalZeroRow_objEq A q) ≫
          ((coaugmentedColumnBicomplexZeroIso A).inv.f (-q)).op ≫
            (ι.f (-q)).op ≫
              eqToHom (congrArg (fun i : ℤ ↦ op (M.X (-i))) hq) ≫
                eqToHom (productTotalSourceOp_objEq M n).symm
    else
      0

-- Proof sketch: project to each total-degree-`n + 1` factor. The `p = 0` component uses the
-- cochain-map relation for `ι`, the `p = 1` horizontal contribution is zero by
-- `hι : ι ≫ A.d 0 1 = 0`, and the other components vanish because the source map lands in the
-- single horizontal degree-zero factor of the product.
/-- The opposite-side comparison morphism from the canonical coproduct total to the transported
source complex. -/
private def productTotalToSourceOp
    (A : CochainComplexSequence) {M : CochainComplex₀} (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) :
    HomologicalComplex₂.productTotalOp
        (coaugmentedColumnBicomplex A : HomologicalComplex₂ C (up ℤ) (up ℤ)) ⟶
      productTotalSourceOp M where
  f := productTotalToSourceOpComponent A ι
  comm' := by
    -- TODO: precompose with each summand inclusion `ιTotal (up ℤ) p q n h`, split on `p = 0`,
    -- use `productTotalSourceOp_d_eq` and the cochain-map relation for `ι` on the `p = 0`
    -- branch, and use `hι` to kill the unique `p = 1` horizontal contribution.
    intro n n' hn
    sorry

/-- The canonical bridge map from the coaugmented source complex to the project owner
`Tot_π(A)`, defined when the coaugmentation satisfies
`ι ≫ A.d 0 1 = 0`. -/
noncomputable def coaugmentedToProductTotal
    (A : CochainComplexSequence) {M : CochainComplex₀} (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) :
    M ⟶ Tot_π(A) :=
  (((CochainComplex.opEquivalence C).unitIso.app (op M)).unop).inv ≫
    (((CochainComplex.opEquivalence C).inverse.map
      (productTotalToSourceOp A ι hι))).unop

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasCountableProducts 𝒜]

local notation "CochainComplex₀" => CochainComplex 𝒜 ℤ
local notation "CochainComplexSequence" => CochainComplex CochainComplex₀ ℕ

variable (A : CochainComplexSequence)
variable {M : CochainComplex₀} (ι : M ⟶ A.X 0)

private abbrev coaugmentedRowShortComplex
    {M : CochainComplex₀} (A : CochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) :=
  ShortComplex.mk ι (A.d 0 1) hι

private abbrev rowOpcyclesComplex
    (A : CochainComplexSequence) (q : ℤ) :=
  ((opcyclesFunctor 𝒜 (up ℤ) (q + 1)).mapHomologicalComplex (up ℕ)).obj A

-- Proof sketch: the first cokernel-row differential is induced by `A₀^• ⟶ A₁^•`; composing it
-- with the row coaugmentation gives zero because the coaugmentation `ι` satisfies
-- `ι ≫ A.d 0 1 = 0`.
/-- The induced map on each shifted opcycles row, i.e. on the canonical rowwise cokernel complex,
annihilates the first row differential. -/
private theorem rowOpcyclesMap_comp_zero
    {M : CochainComplex₀} (A : CochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (q : ℤ) :
    opcyclesMap ι (q + 1) ≫
      (rowOpcyclesComplex A q).d 0 1 = 0 := by
  -- The first row differential is the image of `A.d 0 1` under `opcyclesFunctor`.
  simp only [rowOpcyclesComplex, CategoryTheory.Functor.mapHomologicalComplex_obj_d]
  -- Functoriality of `opcyclesMap` reduces the claim to the vanishing coaugmentation relation.
  rw [← opcyclesMap_comp]
  simpa [hι]

private abbrev rowOpcyclesShortComplex
    {M : CochainComplex₀} (A : CochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (q : ℤ) :=
  ShortComplex.mk (opcyclesMap ι (q + 1)) ((rowOpcyclesComplex A q).d 0 1)
    (rowOpcyclesMap_comp_zero A ι hι q)

-- Proof sketch: the assumptions give exactness of the augmented row of complexes and of all
-- cokernel rows. Filtering the product total complex by horizontal degree and repeating the
-- dévissage from the proof of Lemma 12.26.2 yields that the canonical map from `M^•` to the
-- product total complex induces isomorphisms on cohomology in every degree.
/-- Lemma 12.26.3: if `0 ⟶ M^• ⟶ A₀^• ⟶ A₁^• ⟶ A₂^• ⟶ ⋯` is an exact coaugmented cochain complex
of cochain complexes in an abelian category, and for every vertical degree `q` the induced
coaugmented sequence on cokernels
`0 ⟶ \operatorname{Coker}(d_M^q) ⟶ \operatorname{Coker}(d_{A_0}^q) ⟶
\operatorname{Coker}(d_{A_1}^q) ⟶ ⋯`
is exact, then the canonical map from `M^•` to the product total complex of the associated double
complex `A^{p,q} = A_p^q` is a quasi-isomorphism. The ambient abelian category is assumed to have
countable products so that the product total exists. -/
theorem coaugmented_productTotal_quasiIso_of_exact_row_and_cokernel_rows
    (hι : ι ≫ A.d 0 1 = 0)
    (hMonoι : Mono ι)
    (hExact₀ : (coaugmentedRowShortComplex A ι hι).Exact)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (hCokernelMono : ∀ q : ℤ, Mono (opcyclesMap ι (q + 1)))
    (hCokernelExact₀ : ∀ q : ℤ, (rowOpcyclesShortComplex A ι hι q).Exact)
    (hCokernelExact : ∀ q : ℤ, ∀ n : ℕ,
      (rowOpcyclesComplex A q).ExactAt (n + 1)) :
    QuasiIso (coaugmentedToProductTotal A ι hι) := by
  -- Route correction: stay on the opposite-category transport route from Lemma 12.26.2. The
  -- remaining work is to identify `productTotalToSourceOp` with the opposite-side
  -- `augmentedTotalTo`, transport the augmented-row and cokernel-row exactness hypotheses across
  -- `opcyclesOpIso`, and then transport the resulting quasi-isomorphism back through
  -- `CochainComplex.opEquivalence`.
  sorry

end
