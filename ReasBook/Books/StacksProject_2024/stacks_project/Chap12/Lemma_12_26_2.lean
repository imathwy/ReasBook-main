import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import StacksProject_2024.Chap12.Lemma_12_5_16
import StacksProject_2024.Chap12.Lemma_12_24_13
import StacksProject_2024.Chap12.Lemma_12_25_1
import StacksProject_2024.Chap12.Lemma_12_25_3
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

/-- The canonical identification of the horizontal degree `-1` row in the reindexed bicomplex
with the original complex `A₁^\bullet`. -/
private abbrev augmentedRowBicomplexNegOneIso
    (A : CochainResolution) :
    (augmentedRowBicomplex A).X (-1) ≅ A.X 1 :=
  A.extendXIso embeddingDownNat (by simp)

private abbrev rowCyclesComplex
    (A : CochainResolution) (p : ℤ) :
    ChainComplex 𝒜 ℕ :=
  ((cyclesFunctor 𝒜 (up ℤ) p).mapHomologicalComplex (down ℕ)).obj A

/-- Helper for Lemma 12.26.2: the row of shifted opcycles objects computes the quotients
`A_n^q / \operatorname{im}(d^{q-1})`, i.e. the source-proof boundary row in vertical degree
`q - 1`. -/
private abbrev rowOpcyclesComplex
    (A : CochainResolution) (q : ℤ) :
    ChainComplex 𝒜 ℕ :=
  ((opcyclesFunctor 𝒜 (up ℤ) (q + 1)).mapHomologicalComplex (down ℕ)).obj A

/-- Helper for Lemma 12.26.2: positive horizontal rows of the reindexed bicomplex vanish because
`embeddingDownNat` only hits nonpositive integers. -/
private theorem augmented_row_isZero_X_of_pos
    (A : CochainResolution) {p : ℤ} (hp : 0 < p) :
    IsZero ((augmentedRowBicomplex A).X p) := by
  -- The extension along `embeddingDownNat` is zero away from the image of `n ↦ -n`.
  exact A.isZero_extend_X embeddingDownNat p (fun j hj ↦ by
    have hnonpos : (ComplexShape.embeddingDownNat.f j : ℤ) ≤ 0 := by
      simp [ComplexShape.embeddingDownNat]
    rw [hj] at hnonpos
    omega)

/-- Helper for Lemma 12.26.2: evaluating the augmentation relation
`A_1^\bullet ⟶ A_0^\bullet ⟶ M^\bullet` at a fixed degree still gives zero. -/
private theorem augmented_row_comp_zero_f
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) (q : ℤ) :
    (A.d 1 0).f q ≫ π.f q = 0 := by
  -- Degreewise evaluation turns the chain-map relation into the needed object-level one.
  simpa using congrArg (fun f ↦ f.f q) hπ

/-- Helper for Lemma 12.26.2: evaluating the exact augmented row at a fixed vertical degree gives
an exact short complex of objects. -/
private theorem augmented_row_exact_eval
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact) (q : ℤ) :
    (ShortComplex.mk
      ((A.d 1 0).f q)
      (π.f q)
      (augmented_row_comp_zero_f A π hπ q)).Exact := by
  let F := HomologicalComplex.eval 𝒜 (up ℤ) q
  -- Evaluation is additive, so it preserves exact short complexes.
  simpa [F] using hExact₀.map F

/-- Helper for Lemma 12.26.2: the consecutive outer differentials in the row resolution still
compose to zero after evaluating at a fixed vertical degree. -/
private theorem augmented_outer_row_comp_zero_f
    (A : CochainResolution) (n : ℕ) (q : ℤ) :
    ((A.d (n + 2) (n + 1)).f q) ≫ ((A.d (n + 1) n).f q) = 0 := by
  -- Degreewise evaluation of `d ≫ d = 0` gives the short-complex relation.
  simpa using congrArg (fun f ↦ f.f q) (A.d_comp_d (n + 2) (n + 1) n)

/-- Helper for Lemma 12.26.2: evaluating an exact outer row of complexes at a fixed vertical
degree gives an exact short complex of objects. -/
private theorem augmented_outer_row_exact_eval
    (A : CochainResolution)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (n : ℕ) (q : ℤ) :
    (ShortComplex.mk
      ((A.d (n + 2) (n + 1)).f q)
      ((A.d (n + 1) n).f q)
      (augmented_outer_row_comp_zero_f A n q)).Exact := by
  let F := HomologicalComplex.eval 𝒜 (up ℤ) q
  -- Reuse exactness of the outer chain row and evaluate it degreewise.
  simpa [HomologicalComplex.ExactAt, HomologicalComplex.exactAt_iff, F, Nat.add_assoc] using
    (hExact n).map F

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

/-- The zeroth-row map extracted from the augmentation `A₀^\bullet ⟶ M^\bullet`. -/
private abbrev augmentedTotalToZeroRow
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M) :
    (augmentedRowBicomplex A).X 0 ⟶ M :=
  (augmentedRowBicomplexZeroIso A).hom ≫ π

/-- Helper for Lemma 12.26.2: on each antidiagonal summand, the comparison component is the
expected zeroth-row formula and is zero away from horizontal degree `0`. -/
private theorem ιTotal_comp_augmentedTotalToComponent
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M)
    (p q n : ℤ) (h : p + q = n) :
    (augmentedRowBicomplex A).ιTotal (up ℤ) p q n h ≫ augmentedTotalToComponent A π n =
      if hp : p = 0 then
        (HomologicalComplex₂.XXIsoOfEq 𝒜 (up ℤ) (up ℤ)
          (augmentedRowBicomplex A) hp (rfl : q = q)).hom ≫
            (augmentedTotalToZeroRow A π).f q ≫
              (M.XIsoOfEq (by simpa [hp] using h)).hom
      else
        0 := by
  -- The descended map is defined summandwise, so precomposing with a chosen inclusion exposes
  -- exactly the horizontal-degree-zero branch.
  simp [augmentedTotalToComponent, augmentedTotalToZeroRow]

/-- Helper for Lemma 12.26.2: the unique horizontal differential entering the zeroth row becomes
zero after composing with the augmentation, because it is the original map `A₁^\bullet ⟶ A₀^\bullet`
followed by `π`. -/
private theorem augmentedTotalTo_prev_row_comp_zero
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) :
    (augmentedRowBicomplex A).d (-1) 0 ≫ augmentedTotalToZeroRow A π = 0 := by
  -- Route correction: isolate the `(-1) → 0` horizontal contribution, since it is the only extra
  -- term absent from the overstrong unconditional chain-map statement.
  have hd :
      (augmentedRowBicomplex A).d (-1) 0 =
        (augmentedRowBicomplexNegOneIso A).hom ≫
          A.d 1 0 ≫
            (augmentedRowBicomplexZeroIso A).inv := by
    simpa [augmentedRowBicomplex, augmentedRowBicomplexNegOneIso, augmentedRowBicomplexZeroIso]
      using
        (HomologicalComplex.extend_d_eq
          (K := A) (e := embeddingDownNat) (i := 1) (j := 0)
          (i' := (-1 : ℤ)) (j' := (0 : ℤ)) rfl rfl)
  -- After rewriting the reindexed horizontal differential, the claim is exactly `hπ`.
  rw [hd, augmentedTotalToZeroRow, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hπ,
    zero_comp]

-- Proof sketch: precompose with each summand inclusion into the total complex. On horizontal
-- degree `0`, the vertical part is the cochain-map commutativity of `π`; on horizontal degree
-- `-1`, the only possible surviving horizontal contribution is killed by `hπ`; elsewhere the
-- comparison family vanishes on both pieces of the total differential.
/-- The degreewise components of the canonical total-to-augmentation map commute with the
differentials once the augmentation relation `A₁^\bullet ⟶ A₀^\bullet ⟶ M^\bullet = 0` is
recorded explicitly. -/
private theorem augmentedTotalToComponent_comm_of_augmentation
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (n n' : ℤ) (_ : (up ℤ).Rel n n') :
    augmentedTotalToComponent A π n ≫ M.d n n' =
      (Tot(augmentedRowBicomplex A)).d n n' ≫
        augmentedTotalToComponent A π n' := by
  have hrel01 : (up ℤ).Rel (0 : ℤ) 1 := by
    simp [ComplexShape.up, ComplexShape.up']
  have hnn' : n + 1 = n' := by
    simpa [ComplexShape.up, ComplexShape.up'] using ‹(up ℤ).Rel n n'›
  -- Route correction: follow the source proof summandwise on the antidiagonal, rather than trying
  -- to force an unconditional total-differential commutativity statement.
  apply total.hom_ext
  intro p q hpq
  by_cases hp0 : p = 0
  · subst hp0
    have hq : q = n := by
      simpa using hpq
    subst hq
    -- On the zeroth row, the vertical part is the cochain-map relation for `π`, and the
    -- horizontal part dies because the comparison family is supported only in row `0`.
    calc
      (augmentedRowBicomplex A).ιTotal (up ℤ) 0 n n (Int.add_zero n) ≫
          augmentedTotalToComponent A π n ≫ M.d n n' =
        (augmentedTotalToZeroRow A π).f n ≫ M.d n n' := by
          simp [ιTotal_comp_augmentedTotalToComponent, Category.assoc]
      _ = ((augmentedRowBicomplex A).X 0).d n n' ≫ (augmentedTotalToZeroRow A π).f n' := by
          simpa [augmentedTotalToZeroRow, Category.assoc] using
            (augmentedTotalToZeroRow A π).comm n n' ‹(up ℤ).Rel n n'›
      _ =
          (augmentedRowBicomplex A).ιTotal (up ℤ) 0 n n (Int.add_zero n) ≫
            ((augmentedRowBicomplex A).D₁ (up ℤ) n n' +
              (augmentedRowBicomplex A).D₂ (up ℤ) n n') ≫
                augmentedTotalToComponent A π n' := by
          rw [(augmentedRowBicomplex A).d₁_eq ‹(up ℤ).Rel n n'› 1 n' (by omega),
            (augmentedRowBicomplex A).d₂_eq 0 hrel01 n' (by omega)]
          have hne : (1 : ℤ) ≠ 0 := by omega
          simp [ιTotal_comp_augmentedTotalToComponent, hne, Category.assoc,
            ComplexShape.ε_up_ℤ]
      _ =
          (augmentedRowBicomplex A).ιTotal (up ℤ) 0 n n (Int.add_zero n) ≫
            (Tot(augmentedRowBicomplex A)).d n n' ≫ augmentedTotalToComponent A π n' := by
          rw [(augmentedRowBicomplex A).total_d]
  · by_cases hpneg : p = -1
    · subst hpneg
      have hq : q = n' := by
        have : (-1 : ℤ) + q = n := by
          simpa using hpq
        omega
      subst hq
      have hcomp :
          ((augmentedRowBicomplex A).d (-1) 0).f n' ≫ (augmentedTotalToZeroRow A π).f n' = 0 := by
        simpa [augmentedTotalToZeroRow, Category.assoc] using
          congrArg (fun f : (augmentedRowBicomplex A).X (-1) ⟶ M ↦ f.f n')
            (augmentedTotalTo_prev_row_comp_zero A π hπ)
      -- On the `(-1)`-st row, the only potentially nonzero horizontal term is the map into row
      -- `0`, and `hπ` kills exactly that contribution.
      calc
        (augmentedRowBicomplex A).ιTotal (up ℤ) (-1) n' n hpq ≫
            augmentedTotalToComponent A π n ≫ M.d n n' = 0 := by
          simp [ιTotal_comp_augmentedTotalToComponent, hp0, Category.assoc]
        _ =
            (augmentedRowBicomplex A).ιTotal (up ℤ) (-1) n' n hpq ≫
              ((augmentedRowBicomplex A).D₁ (up ℤ) n n' +
                (augmentedRowBicomplex A).D₂ (up ℤ) n n') ≫
                  augmentedTotalToComponent A π n' := by
            rw [Preadditive.comp_add, Category.assoc, Category.assoc,
              HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
            rw [(augmentedRowBicomplex A).d₁_eq ‹(up ℤ).Rel n n'› 0 n' (Int.add_zero n'),
              (augmentedRowBicomplex A).d₂_eq (-1) hrel01 n' (by omega)]
            have hzero : (((-1 : ℤ) + 1) = 0) := by simp
            simp [ιTotal_comp_augmentedTotalToComponent, hp0, hpneg, hzero, hcomp,
              Category.assoc, ComplexShape.ε_up_ℤ]
        _ =
            (augmentedRowBicomplex A).ιTotal (up ℤ) (-1) n' n hpq ≫
              (Tot(augmentedRowBicomplex A)).d n n' ≫
                augmentedTotalToComponent A π n' := by
            rw [(augmentedRowBicomplex A).total_d]
    · have hp10 : p + 1 ≠ 0 := by
        intro hp10
        apply hpneg
        omega
      -- Away from rows `0` and `-1`, both pieces of the total differential still land in rows
      -- where the comparison family vanishes.
      calc
        (augmentedRowBicomplex A).ιTotal (up ℤ) p q n hpq ≫
            augmentedTotalToComponent A π n ≫ M.d n n' = 0 := by
          simp [ιTotal_comp_augmentedTotalToComponent, hp0, Category.assoc]
        _ =
            (augmentedRowBicomplex A).ιTotal (up ℤ) p q n hpq ≫
              ((augmentedRowBicomplex A).D₁ (up ℤ) n n' +
                (augmentedRowBicomplex A).D₂ (up ℤ) n n') ≫
                  augmentedTotalToComponent A π n' := by
            rw [Preadditive.comp_add, Category.assoc, Category.assoc,
              HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
            rw [(augmentedRowBicomplex A).d₁_eq ‹(up ℤ).Rel n n'› (p + 1) n' (by omega),
              (augmentedRowBicomplex A).d₂_eq p hrel01 n' (by omega)]
            simp [ιTotal_comp_augmentedTotalToComponent, hp0, hp10, Category.assoc,
              ComplexShape.ε_up_ℤ]
        _ =
            (augmentedRowBicomplex A).ιTotal (up ℤ) p q n hpq ≫
              (Tot(augmentedRowBicomplex A)).d n n' ≫
                augmentedTotalToComponent A π n' := by
            rw [(augmentedRowBicomplex A).total_d]

/-- The canonical cochain map `\mathrm{Tot}(A^{\bullet,\bullet}) ⟶ M^\bullet` induced by the
augmentation `A₀^\bullet ⟶ M^\bullet`. -/
def augmentedTotalTo
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M) :
    Tot(A.extend embeddingDownNat) ⟶ M :=
  if hπ : A.d 1 0 ≫ π = 0 then
    { f := augmentedTotalToComponent A π
      comm' := augmentedTotalToComponent_comm_of_augmentation A π hπ }
  else
    0

-- Proof sketch: the first differential in the kernel row is induced from `A₁^• ⟶ A₀^•`; after
-- composing with the induced map to `ker(d_M^p)`, the result vanishes because the augmentation
-- satisfies `A₁^• ⟶ A₀^• ⟶ M^• = 0`.
/-- The induced map on each row of cycles annihilates the first kernel-row differential. -/
private theorem rowCyclesMap_comp_zero
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) (p : ℤ) :
    (rowCyclesComplex A p).d 1 0 ≫ cyclesMap π p = 0 := by
  -- Apply the cycles functor to the augmentation relation `A₁^• ⟶ A₀^• ⟶ M^• = 0`.
  have hcycles : cyclesMap (A.d 1 0 ≫ π) p = 0 := by
    simpa using congrArg (fun f : A.X 1 ⟶ M ↦ (cyclesFunctor 𝒜 (up ℤ) p).map f) hπ
  rw [cyclesMap_comp] at hcycles
  simpa [rowCyclesComplex] using hcycles

-- Proof sketch: this is the quotient-side analogue of `rowCyclesMap_comp_zero`. Applying the
-- shifted `opcyclesFunctor` to `A₁^• ⟶ A₀^• ⟶ M^• = 0` gives the first compatibility needed for
-- the source proof's dévissage from objects/kernels to boundaries/opcycles.
/-- Helper for Lemma 12.26.2: the induced map on each shifted opcycles row annihilates the first
row differential. -/
private theorem rowOpcyclesMap_comp_zero
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0) (q : ℤ) :
    (rowOpcyclesComplex A q).d 1 0 ≫ opcyclesMap π (q + 1) = 0 := by
  -- Functoriality of `opcyclesFunctor` reduces the claim to the vanishing augmentation relation.
  have hopcycles : opcyclesMap (A.d 1 0 ≫ π) (q + 1) = 0 := by
    simpa using
      congrArg (fun f : A.X 1 ⟶ M ↦ (opcyclesFunctor 𝒜 (up ℤ) (q + 1)).map f) hπ
  rw [opcyclesMap_comp] at hopcycles
  simpa [rowOpcyclesComplex] using hopcycles

/-- Helper for Lemma 12.26.2: if the endpoint kernel map in vertical degree `q` is an epimorphism,
then the induced augmented row on shifted opcycles is exact at the `A₀` term. -/
private theorem augmented_row_opcycles_exact_zero_of_epi
    {M : CochainComplex₀}
    (A : CochainResolution) (π : A.X 0 ⟶ M)
    (hπ : A.d 1 0 ≫ π = 0)
    (hExact₀ : (ShortComplex.mk (A.d 1 0) π hπ).Exact)
    (q : ℤ)
    (hKernelExact₀ : (ShortComplex.mk
      (((rowCyclesComplex A q).d 1 0))
      (cyclesMap π q)
      (rowCyclesMap_comp_zero A π hπ q)).Exact)
    [Epi (cyclesMap π q)] :
    (ShortComplex.mk
      ((rowOpcyclesComplex A q).d 1 0)
      (opcyclesMap π (q + 1))
      (rowOpcyclesMap_comp_zero A π hπ q)).Exact := by
  let Sker : ShortComplex 𝒜 :=
    ShortComplex.mk
      ((rowCyclesComplex A q).d 1 0)
      (cyclesMap π q)
      (rowCyclesMap_comp_zero A π hπ q)
  let Sobj : ShortComplex 𝒜 :=
    ShortComplex.mk
      ((A.d 1 0).f q)
      (π.f q)
      (augmented_row_comp_zero_f A π hπ q)
  have hcomm₁ :
      ((rowCyclesComplex A q).d 1 0) ≫ (A.X 0).iCycles q =
        (A.X 1).iCycles q ≫ (A.d 1 0).f q := by
    let ψ :=
      (HomologicalComplex.shortComplexFunctor 𝒜 (up ℤ) q).map (A.d 1 0)
    -- The cycles square is the standard naturality square for `ShortComplex.cyclesMap`.
    simpa [rowCyclesComplex] using (ShortComplex.cyclesMap_i ψ)
  have hcomm₂ :
      cyclesMap π q ≫ M.iCycles q =
        (A.X 0).iCycles q ≫ π.f q := by
    let ψ :=
      (HomologicalComplex.shortComplexFunctor 𝒜 (up ℤ) q).map π
    -- The augmentation square on cycles is the same naturality square evaluated at `π`.
    simpa using (ShortComplex.cyclesMap_i ψ)
  let φ : Sker ⟶ Sobj :=
    ShortComplex.homMk
      ((A.X 1).iCycles q)
      ((A.X 0).iCycles q)
      (M.iCycles q)
      hcomm₁
      hcomm₂
  have hSobj : Sobj.Exact := by
    -- Reuse the evaluated exact augmented object row from the source hypotheses.
    simpa [Sobj] using augmented_row_exact_eval A π hπ hExact₀ q
  letI : Epi Sker.g := by
    simpa [Sker]
  -- Route correction: isolate the degree-zero cokernel transfer. This matches the source proof's
  -- first devissage exactly, and also makes the missing endpoint-epi hypothesis explicit.
  simpa [Sker, Sobj, φ, rowOpcyclesComplex] using
    CategoryTheory.cokernel_sequence_exact_of_exact_of_epi φ hSobj

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
    QuasiIso (augmentedTotalTo A π) := by
  -- TODO: finish the source-faithful spectral-sequence argument. The verified local frontier is:
  -- the comparison map `augmentedTotalTo A π` is now packaged through the corrected helper
  -- `augmentedTotalToComponent_comm_of_augmentation`, and both rowwise augmentation-compatibility
  -- lemmas `rowCyclesMap_comp_zero` and `rowOpcyclesMap_comp_zero` are proved. The remaining work
  -- is the first quotient dévissage `augmented_row_opcycles_exact`, then the induced homology-row
  -- exactness and the source-faithful computation of the `E₂`-page for `augmentedRowBicomplex A`.
  sorry

end

end
