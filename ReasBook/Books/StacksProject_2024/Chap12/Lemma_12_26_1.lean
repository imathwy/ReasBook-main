import Mathlib
import StacksProject_2024.Chap12.Lemma_12_25_5

-- Declarations for this item will be appended below by the statement pipeline.

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
