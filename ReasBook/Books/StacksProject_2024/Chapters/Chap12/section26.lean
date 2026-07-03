import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_12_26_1 (from Chap12) -/
open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂
open scoped HomologicalComplex₂

noncomputable section

universe v u

/-
Domain-style sampling for Lemma 12.26.1 in the bicomplex-total/quasi-isomorphism domain:
- primary domain: a coaugmented cochain complex of cochain complexes, viewed as a bicomplex, and
  the induced map from the coaugmentation source into the coproduct total complex;
- sampled owner abstractions:
  * `HomologicalComplex₂.total` / `Tot(_)` for the canonical total-complex owner;
  * `doubleComplexZeroColumnToTotal` from `Lemma_12_25_4` for the canonical map from a zero
    column into a total complex;
  * `HomologicalComplex.extend` and `extendXIso` for the reindexing from outer degree `ℕ` to `ℤ`.
- layer triage:
  * `source-facing`: `coaugmentedColumnBicomplex`, `coaugmentedToTotal`, and the quasi-isomorphism
    theorem below;
  * `core/canonical`: `Tot(_)` and `doubleComplexZeroColumnToTotal`;
  * `bridge/view`: the extended bicomplex and the degree-zero column identification.

Primitive data are only the coaugmented row `A` and the coaugmentation `ι : M ⟶ A.X 0`. The map
to the total complex is derived owner API: it should be built from the canonical zero-column
comparison on the associated bicomplex, not by keeping a second parallel flip-based
implementation in this file.
-/

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The cohomological double complex obtained from a coaugmented cochain complex of cochain
complexes by extending the outer degree from `ℕ` to `ℤ`. -/
abbrev coaugmentedColumnBicomplex
    (A : CochainComplex (CochainComplex C ℤ) ℕ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  A.extend embeddingUpNat

/-- The canonical identification of the horizontal degree-zero column in the extended bicomplex
with the original complex `A₀^\bullet`. -/
abbrev coaugmentedColumnBicomplexZeroIso
    (A : CochainComplex (CochainComplex C ℤ) ℕ) :
    (coaugmentedColumnBicomplex A).X 0 ≅ A.X 0 :=
  A.extendXIso embeddingUpNat rfl

end

section

local notation "AbCochainComplex" => CochainComplex AddCommGrpCat ℤ
local notation "AbCochainComplexSequence" => CochainComplex AbCochainComplex ℕ

private abbrev coaugmentedToZeroColumn
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0) :
    M ⟶ (coaugmentedColumnBicomplex A).X 0 :=
  ι ≫ (coaugmentedColumnBicomplexZeroIso A).inv

-- Proof sketch: under the degree-zero column identification, the horizontal differential of the
-- bicomplex is exactly the outer differential `A.d 0 1`, so the vanishing is the componentwise
-- form of `hι`.
private theorem coaugmentedToZeroColumn_comp_d
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) :
    ∀ p : ℤ,
      (coaugmentedToZeroColumn A ι).f p ≫ ((coaugmentedColumnBicomplex A).d 0 1).f p = 0 :=
  sorry

/-- The canonical map `M^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})` induced by the
coaugmentation `M^\bullet ⟶ A₀^\bullet`. -/
noncomputable def coaugmentedToTotal
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) :
    M ⟶ Tot(coaugmentedColumnBicomplex A) :=
  doubleComplexZeroColumnToTotal
      (coaugmentedToZeroColumn A ι)
      (coaugmentedToZeroColumn_comp_d A ι hι)

-- Proof sketch: apply the zero-column form of Lemma `12.25.4` to the extended bicomplex.
-- The exact coaugmented sequence `0 ⟶ M^\bullet ⟶ A₀^\bullet ⟶ A₁^\bullet ⟶ ⋯` gives the
-- exactness of the rows away from the zeroth column, and `Mono ι` together with exactness at
-- `A₀^\bullet` identifies each `M^q` with the row cycles in column `0`. The resulting
-- quasi-isomorphism is exactly the canonical map `coaugmentedToTotal A ι`.
/-- Lemma 12.26.1: if
`0 \to M^\bullet \to A_0^\bullet \to A_1^\bullet \to A_2^\bullet \to \cdots`
is an exact coaugmented cochain complex of cochain complexes of abelian groups, and
`A^{p,q} = A_p^q` is the associated double complex, then the canonical map
`M^\bullet \to \mathrm{Tot}(A^{\bullet,\bullet})` induced by `M^\bullet \to A_0^\bullet`
is a quasi-isomorphism. -/
theorem coaugmentedToTotal_quasiIso_of_exact_complex_of_complexes
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) [Mono ι]
    (hExact₀ : (ShortComplex.mk ι (A.d 0 1) hι).Exact)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1)) :
    QuasiIso (coaugmentedToTotal A ι hι) := sorry

/-! ### Lemma_12_26_2 (from Chap12) -/
open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂ Opposite
open scoped HomologicalComplex₂

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The opposite of a bicomplex, viewed as a cochain complex of opposite cochain complexes. -/
abbrev productTotalCochainOp
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    CochainComplex (CochainComplex C ℤ)ᵒᵖ ℤ :=
  (ChainComplex.cochainComplexEquivalence ((CochainComplex C ℤ)ᵒᵖ)).functor.obj K.op

/-- The opposite bicomplex whose coproduct total models the product total of `K`. -/
abbrev productTotalOpBicomplex
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ) :=
  (((CochainComplex.opEquivalence C).functor).mapHomologicalComplex (up ℤ)).obj
    (productTotalCochainOp K)

/-- The canonical coproduct total of the opposite bicomplex underlying the product total of `K`. -/
abbrev productTotalOp
    [HasCountableProducts C]
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    CochainComplex Cᵒᵖ ℤ :=
  (productTotalOpBicomplex K).total (up ℤ)

/-- The product total complex of a bicomplex, defined as the unop of the canonical total of the
transported opposite bicomplex. -/
abbrev productTotal
    [HasCountableProducts C]
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    CochainComplex C ℤ :=
  ((CochainComplex.opEquivalence C).inverse.obj (productTotalOp K)).unop

/-- Functoriality of the product total construction on cohomological bicomplexes. -/
abbrev productTotalFunctor
    [HasCountableProducts C] :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ CochainComplex C ℤ :=
  opOp _ ⋙
    ((HomologicalComplex.opFunctor (CochainComplex C ℤ) (up ℤ)) ⋙
      (ChainComplex.cochainComplexEquivalence ((CochainComplex C ℤ)ᵒᵖ)).functor ⋙
      ((CochainComplex.opEquivalence C).functor).mapHomologicalComplex (up ℤ) ⋙
      totalFunctor Cᵒᵖ (up ℤ) (up ℤ) (up ℤ) ⋙
      (CochainComplex.opEquivalence C).inverse).leftOp

end HomologicalComplex₂

scoped[HomologicalComplex₂] notation:max "Tot_π(" K ")" => HomologicalComplex₂.productTotal K

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "CochainComplex₀" => CochainComplex 𝒜 ℤ
local notation "CochainResolution" => ChainComplex CochainComplex₀ ℕ

/- Domain-style sampling for Lemma 12.26.2 in the total-complex/quasi-isomorphism domain:
- primary domain: an augmented row of cochain complexes, reindexed to a bicomplex and compared with
  its total complex;
- sampled owner abstractions:
  * `cyclesFunctor` and `cyclesMap` for rowwise cycles and
  the augmentation they inherit functorially from `π : A.X 0 ⟶ M`;
  * `cyclesIsoKernel` and `extendCyclesIso` as the standard
    kernel/cycles and extension/reindexing comparison bridges;
  * `Tot(A)` / `HomologicalComplex₂.totalDesc` for the canonical map out of the total complex.
- layer triage:
  * `source-facing`: `augmentedTotalTo` and the final quasi-isomorphism theorem;
  * `core/canonical`: the rowwise cycles owner `cyclesMap`, its functoriality, extension, and
    total descent on `Tot(A)`;
  * `bridge/view`: the degree-zero `extendXIso` comparison and the textbook identification of
    cycles with kernels.

Primitive data are just the augmented row `A` and the augmentation `π : A.X 0 ⟶ M`. The row
cycles complexes and their augmentation are derived API and should use the canonical owner
abstractions directly rather than exposing one-off public aliases for those owners.
-/

/-- The reindexed bicomplex obtained by placing outer degree `n` in horizontal degree `-n`. -/
private abbrev augmentedRowBicomplex (A : CochainResolution) :
    HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ) :=
  A.extend embeddingDownNat

/-- The canonical identification of the horizontal degree-zero row in the reindexed bicomplex with
the original complex `A₀^\bullet`. -/
private abbrev augmentedRowBicomplexZeroIso
    (A : CochainResolution) :
    (augmentedRowBicomplex A).X 0 ≅ A.X 0 :=
  A.extendXIso embeddingDownNat (by simp)

private abbrev rowCyclesComplex
    (A : CochainResolution) (p : ℤ) :
    ChainComplex 𝒜 ℕ :=
  ((cyclesFunctor 𝒜 (up ℤ) p).mapHomologicalComplex (down ℕ)).obj A

section

variable [HasCountableCoproducts 𝒜]

/-- The component in total degree `n` of the canonical map from the total complex of the reindexed
double complex to `M^•`, induced by the augmentation `A₀^• ⟶ M^•`. -/
private def augmentedTotalToComponent
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M) (n : ℤ) :
    (Tot(augmentedRowBicomplex A)).X n ⟶ M.X n :=
  (augmentedRowBicomplex A).totalDesc
    (fun p q h ↦
      if hp : p = 0 then
        (HomologicalComplex₂.XXIsoOfEq 𝒜 (up ℤ) (up ℤ)
          (augmentedRowBicomplex A) hp (rfl : q = q)).hom ≫
          ((augmentedRowBicomplexZeroIso A).hom.f q) ≫
          π.f q ≫
            (M.XIsoOfEq (by simpa [hp] using h)).hom
      else
        0)

-- Proof sketch: precompose with each summand inclusion into the total complex. For horizontal
-- degree `0` this is exactly the cochain-map commutativity of `π`; for the other horizontal
-- degrees the component is zero by definition.
/-- The degreewise components of the canonical total-to-augmentation map commute with the
differentials. -/
private theorem augmentedTotalToComponent_comm
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M)
    (n n' : ℤ) (_ : (up ℤ).Rel n n') :
    augmentedTotalToComponent A π n ≫ M.d n n' =
      (Tot(augmentedRowBicomplex A)).d n n' ≫
        augmentedTotalToComponent A π n' := sorry

/-- The canonical cochain map `\mathrm{Tot}(A^{\bullet,\bullet}) ⟶ M^\bullet` induced by the
augmentation `A₀^\bullet ⟶ M^\bullet`. -/
def augmentedTotalTo
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M) :
    Tot(A.extend embeddingDownNat) ⟶ M where
  f := augmentedTotalToComponent A π
  comm' := augmentedTotalToComponent_comm A π

-- Proof sketch: the first differential in the kernel row is induced from `A₁^• ⟶ A₀^•`; after
-- composing with the induced map to `ker(d_M^p)`, the result vanishes because the augmentation
-- satisfies `A₁^• ⟶ A₀^• ⟶ M^• = 0`.
/-- The induced map on each row of cycles annihilates the first kernel-row differential. -/
private theorem rowCyclesMap_comp_zero
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) (p : ℤ) :
    (rowCyclesComplex A p).d 1 0 ≫ cyclesMap π p = 0 := sorry

-- Proof sketch: exactness of the augmented row and of all augmented kernel rows implies exactness
-- on the image rows and hence on the cohomology rows. The standard dévissage on the highest
-- nonzero horizontal component of a cocycle in the total complex then shows that the canonical
-- total map induces an isomorphism on cohomology in every degree.
/-- Lemma 12.26.2: if an augmented exact row of cochain complexes
`\cdots \to A_2^\bullet \to A_1^\bullet \to A_0^\bullet \to M^\bullet \to 0`
has exact kernel rows in every vertical degree, then the induced map from the total complex of the
reindexed double complex `A^{p,q} = A_{-p}^q` to `M^\bullet` is a quasi-isomorphism. -/
theorem total_quasiIso_of_exact_augmented_row_and_kernel_rows
    {M : CochainComplex₀}
    (A : CochainResolution)
    (π : A.X 0 ⟶ M) (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (hKernelExact₀ : ∀ p : ℤ,
      (ShortComplex.mk ((((cyclesFunctor 𝒜 (up ℤ) p).mapHomologicalComplex (down ℕ)).obj A).d 1 0)
        (cyclesMap π p)
        (rowCyclesMap_comp_zero A π hπ p)).Exact)
    (hKernelExact : ∀ p : ℤ, ∀ n : ℕ,
      (((cyclesFunctor 𝒜 (up ℤ) p).mapHomologicalComplex (down ℕ)).obj A).ExactAt (n + 1)) :
    QuasiIso (augmentedTotalTo A π) := sorry

end

end

/-! ### Lemma_12_26_3 (from Chap12) -/
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
      (rowOpcyclesComplex A q).d 0 1 = 0 := sorry

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
    QuasiIso (coaugmentedToProductTotal A ι hι) := sorry

end

/-! ### Lemma_12_26_4 (from Chap12) -/
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
