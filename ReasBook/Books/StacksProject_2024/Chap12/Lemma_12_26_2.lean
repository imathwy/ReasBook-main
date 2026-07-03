import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import StacksProject_2024.Chap12.Definition_12_18_3

-- Declarations for this item will be appended below by the statement pipeline.

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
