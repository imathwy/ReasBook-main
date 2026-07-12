import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomologicalComplex
open HomologicalComplex₂

noncomputable section

universe v u

/- Domain-style sampling for Lemma 12.25.1:
- primary domain: cohomological double complexes and the page identifications of the two spectral
  sequences attached to them;
- inspected owner declarations:
  `HomologicalComplex₂.flip`,
  `HomologicalComplex.homologyFunctor`,
  `CochainComplex.of`,
  `ComplexShape.ε_up_ℤ`;
- owner abstraction: the double-complex owner `HomologicalComplex₂`, with row/column and homology
  views derived from `flip` and `HomologicalComplex.homologyFunctor`;
- primitive data: the bicomplex `K` and its owner differentials;
- derived API in this file: the source-facing `E₀`, `E₁`, and `E₂` page terms and differentials,
  together with the canonical first `E₁`-page complex and its signed flipped companion for the
  second `E₁`-page;
- triage:
  `source-facing`: the page-term and differential declarations below;
  `core/canonical`: `HomologicalComplex₂`, `flip`, and `HomologicalComplex.homologyFunctor`;
  `bridge/view`: the first `E₁`-page cochain complex in the horizontal direction, together with
  its sign-twisted flipped variant for the second `E₁`-page; both should use canonical
  `CochainComplex` owners rather than coordinate-only projections.
-/

section SignTwist

variable {C : Type u} [Category.{v} C] [Preadditive C]

-- Proof sketch: `CochainComplex.of` is the canonical owner for an explicitly defined cochain
-- complex, so it is enough to verify square-zero on consecutive differentials.
private theorem cochainComplexUnitsSMul_sq
    (L : CochainComplex C ℤ) (ε : ℤˣ) (p : ℤ) :
    (ε • L.d p (p + 1)) ≫ (ε • L.d (p + 1) ((p + 1) + 1)) = 0 := by
  calc
    (ε • L.d p (p + 1)) ≫ (ε • L.d (p + 1) ((p + 1) + 1)) =
        ε • (ε • (L.d p (p + 1) ≫ L.d (p + 1) ((p + 1) + 1))) := by
      simp [Linear.units_smul_comp, Linear.comp_units_smul]
    _ = 0 := by simp [L.d_comp_d p (p + 1) ((p + 1) + 1)]

end SignTwist

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
local notation "DoubleComplex" => HomologicalComplex₂ C (up ℤ) (up ℤ)

/-- Lemma 12.25.1 (1): the first spectral sequence attached to a cohomological double complex has
term `{}'E_0^{p,q} = K^{p,q}`. -/
abbrev firstDoubleComplexPageZero
    (K : DoubleComplex) (p q : ℤ) : C :=
  (K.X p).X q

/-- Lemma 12.25.1 (2): the differential on the first `E₀`-page is
`{}'d_0^{p,q} = (-1)^p d_2^{p,q} : K^{p,q} ⟶ K^{p,q + 1}`. -/
abbrev firstDoubleComplexPageZeroDifferential
    (K : DoubleComplex) (p q : ℤ) :
    firstDoubleComplexPageZero K p q ⟶ firstDoubleComplexPageZero K p (q + 1) :=
  p.negOnePow • (K.X p).d q (q + 1)

/-- Lemma 12.25.1 (3): the second spectral sequence attached to a cohomological double complex has
term `{}''E_0^{p,q} = K^{q,p}`. -/
abbrev secondDoubleComplexPageZero
    (K : DoubleComplex) (p q : ℤ) : C :=
  (K.flip.X p).X q

-- Proof sketch: this is the defining abbreviation of the second `E₀`-page term.
/-- The second `E₀`-page object is definitionally the transposed `(q,p)`-entry of the double
complex. -/
theorem secondDoubleComplexPageZero_def
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageZero K p q = (K.X q).X p := rfl

/-- Lemma 12.25.1 (4): the differential on the second `E₀`-page is
`{}''d_0^{p,q} = d_1^{q,p} : K^{q,p} ⟶ K^{q + 1,p}`. -/
abbrev secondDoubleComplexPageZeroDifferential
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageZero K p q ⟶ secondDoubleComplexPageZero K p (q + 1) :=
  (K.flip.X p).d q (q + 1)

-- Proof sketch: unfold the abbreviation for the second `E₀`-page differential.
/-- The second `E₀`-page differential is definitionally the horizontal differential of the double
complex. -/
theorem secondDoubleComplexPageZeroDifferential_def
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageZeroDifferential K p q = (K.d q (q + 1)).f p := rfl

variable [CategoryWithHomology C]
local notation "homologyFunctor" => HomologicalComplex.homologyFunctor C (up ℤ)

/-- The first `E₁`-page cochain complex obtained by taking vertical homology in degree `q` along
the columns of a cohomological double complex. -/
abbrev firstDoubleComplexPageOneComplex
    (K : DoubleComplex) (q : ℤ) : CochainComplex C ℤ :=
  ((homologyFunctor q).mapHomologicalComplex (up ℤ)).obj K

/-- The `p`-th object of the first `E₁`-page complex is the vertical homology of the `p`-th
column. -/
@[simp] theorem firstDoubleComplexPageOneComplex_X
    (K : DoubleComplex) (p q : ℤ) :
    (firstDoubleComplexPageOneComplex K q).X p = (K.X p).homology q := rfl

/-- The differential of the first `E₁`-page complex is the homology map induced by the horizontal
differential. -/
@[simp] theorem firstDoubleComplexPageOneComplex_d
    (K : DoubleComplex) (p q : ℤ) :
    (firstDoubleComplexPageOneComplex K q).d p (p + 1) =
      homologyMap (K.d p (p + 1)) q := rfl

/-- The second `E₁`-page cochain complex: its objects are the horizontal homology groups
`H^q(K^{\bullet,p})`, and its differential is the sign-twisted map
`(-1)^q H^q(d_2^{\bullet,p})`. Equivalently, it is the sign twist of
`firstDoubleComplexPageOneComplex K.flip q`. -/
abbrev secondDoubleComplexPageOneComplex
    (K : DoubleComplex) (q : ℤ) : CochainComplex C ℤ :=
  CochainComplex.of
    (firstDoubleComplexPageOneComplex K.flip q).X
    (fun p ↦ q.negOnePow • (firstDoubleComplexPageOneComplex K.flip q).d p (p + 1))
    (cochainComplexUnitsSMul_sq (firstDoubleComplexPageOneComplex K.flip q) q.negOnePow)

/-- The `p`-th object of the second `E₁`-page complex is the horizontal homology of the `p`-th
row. -/
@[simp] theorem secondDoubleComplexPageOneComplex_X
    (K : DoubleComplex) (p q : ℤ) :
    (secondDoubleComplexPageOneComplex K q).X p = (K.flip.X p).homology q := rfl

/-- The differential of the second `E₁`-page complex is the signed homology map induced by the
vertical differential on the flipped double complex. -/
@[simp] theorem secondDoubleComplexPageOneComplex_d
    (K : DoubleComplex) (q p : ℤ) :
    (secondDoubleComplexPageOneComplex K q).d p (p + 1) =
      q.negOnePow • (firstDoubleComplexPageOneComplex K.flip q).d p (p + 1) := by
  exact
    CochainComplex.of_d
      (firstDoubleComplexPageOneComplex K.flip q).X
      (fun p ↦ q.negOnePow • (firstDoubleComplexPageOneComplex K.flip q).d p (p + 1))
      (cochainComplexUnitsSMul_sq (firstDoubleComplexPageOneComplex K.flip q) q.negOnePow)
      p

/-- Lemma 12.25.1 (5): the first `E₁`-page is the vertical homology
`{}'E_1^{p,q} = H^q(K^{p,\bullet})`. -/
abbrev firstDoubleComplexPageOne
    (K : DoubleComplex) (p q : ℤ) : C :=
  (firstDoubleComplexPageOneComplex K q).X p

/-- The first `E₁`-page object is definitionally the vertical homology of the `p`-th column. -/
theorem firstDoubleComplexPageOne_def
    (K : DoubleComplex) (p q : ℤ) :
    firstDoubleComplexPageOne K p q = (K.X p).homology q := by
  simpa [firstDoubleComplexPageOne] using firstDoubleComplexPageOneComplex_X K p q

/-- Lemma 12.25.1 (6): the differential on the first `E₁`-page is
`{}'d_1^{p,q} = H^q(d_1^{p,\bullet})`. -/
abbrev firstDoubleComplexPageOneDifferential
    (K : DoubleComplex) (p q : ℤ) :
    firstDoubleComplexPageOne K p q ⟶ firstDoubleComplexPageOne K (p + 1) q :=
  (firstDoubleComplexPageOneComplex K q).d p (p + 1)

/-- The first `E₁`-page differential is definitionally the homology map induced by the horizontal
differential. -/
theorem firstDoubleComplexPageOneDifferential_def
    (K : DoubleComplex) (p q : ℤ) :
    firstDoubleComplexPageOneDifferential K p q =
      homologyMap (K.d p (p + 1)) q := by
  simpa [firstDoubleComplexPageOneDifferential] using firstDoubleComplexPageOneComplex_d K p q

/-- Lemma 12.25.1 (7): the second `E₁`-page is the horizontal homology
`{}''E_1^{p,q} = H^q(K^{\bullet,p})`. -/
abbrev secondDoubleComplexPageOne
    (K : DoubleComplex) (p q : ℤ) : C :=
  (secondDoubleComplexPageOneComplex K q).X p

/-- The second `E₁`-page object is definitionally the horizontal homology of the `p`-th row. -/
theorem secondDoubleComplexPageOne_def
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageOne K p q = (K.flip.X p).homology q := by
  simpa [secondDoubleComplexPageOne] using secondDoubleComplexPageOneComplex_X K p q

/-- Lemma 12.25.1 (8): the differential on the second `E₁`-page is
`{}''d_1^{p,q} = (-1)^q H^q(d_2^{\bullet,p})`. -/
abbrev secondDoubleComplexPageOneDifferential
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageOne K p q ⟶ secondDoubleComplexPageOne K (p + 1) q :=
  (secondDoubleComplexPageOneComplex K q).d p (p + 1)

/-- The second `E₁`-page differential is definitionally the signed homology map induced by the
vertical differential on the flipped double complex. -/
theorem secondDoubleComplexPageOneDifferential_def
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageOneDifferential K p q =
      q.negOnePow • homologyMap (K.flip.d p (p + 1)) q := by
  rw [secondDoubleComplexPageOneDifferential, secondDoubleComplexPageOneComplex_d]
  rfl

/-- Lemma 12.25.1 (9): the first `E₂`-page is the horizontal homology of the vertical homology
complex, namely `{}'E_2^{p,q} = H_I^p(H_{II}^q(K^{\bullet,\bullet}))`. -/
abbrev firstDoubleComplexPageTwo
    (K : DoubleComplex) (p q : ℤ) : C :=
  (firstDoubleComplexPageOneComplex K q).homology p

/-- The first `E₂`-page object is definitionally the horizontal homology of the vertical homology
complex. -/
theorem firstDoubleComplexPageTwo_def
    (K : DoubleComplex) (p q : ℤ) :
    firstDoubleComplexPageTwo K p q =
      (firstDoubleComplexPageOneComplex K q).homology p := rfl

/-- Lemma 12.25.1 (10): the second `E₂`-page is the vertical homology of the horizontal homology
complex, namely `{}''E_2^{p,q} = H_{II}^p(H_I^q(K^{\bullet,\bullet}))`. -/
abbrev secondDoubleComplexPageTwo
    (K : DoubleComplex) (p q : ℤ) : C :=
  (secondDoubleComplexPageOneComplex K q).homology p

-- Proof sketch: this is the defining abbreviation of the second `E₂`-page term.
/-- The second `E₂`-page object is definitionally the vertical homology of the horizontal
homology complex. -/
theorem secondDoubleComplexPageTwo_def
    (K : DoubleComplex) (p q : ℤ) :
    secondDoubleComplexPageTwo K p q = (secondDoubleComplexPageOneComplex K q).homology p := rfl

end
