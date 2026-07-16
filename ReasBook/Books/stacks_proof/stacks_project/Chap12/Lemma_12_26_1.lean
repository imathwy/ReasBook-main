import Mathlib
import stacks_proof.stacks_project.Chap12.Lemma_12_25_4

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
  by
    intro p
    -- The horizontal differential in columns `0 → 1` is the original outer differential.
    have hd :
        (coaugmentedColumnBicomplex A).d 0 1 =
          (coaugmentedColumnBicomplexZeroIso A).hom ≫
            A.d 0 1 ≫
            (A.extendXIso embeddingUpNat
              (show (ComplexShape.embeddingUpNat.f 1 : ℤ) = 1 by rfl)).inv := by
      simpa [coaugmentedColumnBicomplex, coaugmentedColumnBicomplexZeroIso] using
        (HomologicalComplex.extend_d_eq
          (K := A) (e := embeddingUpNat) (i := 0) (j := 1)
          (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl)
    -- After rewriting, the claim is just the componentwise form of `hι`.
    have hcomp : coaugmentedToZeroColumn A ι ≫ (coaugmentedColumnBicomplex A).d 0 1 = 0 := by
      rw [coaugmentedToZeroColumn, hd, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hι, zero_comp]
    simpa using congrArg (fun f ↦ f.f p) hcomp

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

/-- Helper for Lemma 12.26.1: finite antidiagonal support means that for each total degree only
finitely many horizontal indices contribute nonzero summands. -/
private abbrev doubleComplexHasFiniteAntidiagonalSupport
    (K : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ)) : Prop :=
  CategoryTheory.doubleComplexHasFiniteAntidiagonalSupport K

/-- Helper for Lemma 12.26.1: a map into the zero row of a bicomplex induces a map to the
corresponding cycles object. -/
private noncomputable def doubleComplexZeroRowCyclesMap
    {K : AbCochainComplex} {B : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ)}
    (α : K ⟶ ((HomologicalComplex.eval AddCommGrpCat (up ℤ) (0 : ℤ)).mapHomologicalComplex
      (up ℤ)).obj B)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (B.X p).d 0 1 = 0) (p : ℤ) :
    K.X p ⟶ (B.X p).cycles 0 :=
  (B.X p).liftCycles' (α.f p) 1 rfl (hαcycles p)

/-- Helper for Lemma 12.26.1: a map into the zero column of a bicomplex induces a map to the
row-cycles object after flipping. -/
private noncomputable def doubleComplexZeroColumnCyclesMap
    {K : AbCochainComplex} {B : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ)}
    (α : K ⟶ B.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (B.d 0 1).f q = 0) (q : ℤ) :
    K.X q ⟶ (B.flip.X q).cycles 0 :=
  doubleComplexZeroRowCyclesMap
    (doubleComplexZeroColumnToZeroRowFlip α)
    (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) q

/-- Helper for Lemma 12.26.1: if `t ≤ i`, then the retained degree `i` lies in the image of the
embedding `n ↦ t + n` used in the lower brutal truncation. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (t i : ℤ) (hti : t ≤ i) :
    (ComplexShape.embeddingUpIntGE t).f (Int.toNat (i - t)) = i := by
  -- The retained-range witness is exactly the nonnegative difference `i - t`.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 12.26.1: in a retained degree, the lower brutal truncation term is
canonically identified with the original term. -/
private noncomputable def lower_stupid_truncation_x_iso
    (K : AbCochainComplex) (t i : ℤ) (hti : t ≤ i) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X i ≅ K.X i :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntGE t)
    (embeddingUpIntGE_toNat_sub_eq t i hti)

/-- Helper for Lemma 12.26.1: after transporting along the retained-degree identifications, the
differential of the lower brutal truncation is the original differential. -/
private theorem lower_stupid_truncation_d_via_x_iso
    (K : AbCochainComplex) (t : ℤ) {i j : ℤ}
    (hti : t ≤ i) (htj : t ≤ j) :
    (lower_stupid_truncation_x_iso K t i hti).inv ≫
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
      (lower_stupid_truncation_x_iso K t j htj).hom =
        K.d i j := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntGE t
  let i₀ : ℕ := Int.toNat (i - t)
  let j₀ : ℕ := Int.toNat (j - t)
  have hi₀ : e.f i₀ = i := embeddingUpIntGE_toNat_sub_eq t i hti
  have hj₀ : e.f j₀ = j := embeddingUpIntGE_toNat_sub_eq t j htj
  -- Rewrite once through `extend`, then through `restriction`, to expose the original
  -- differential on `K`.
  change (lower_stupid_truncation_x_iso K t i hti).inv ≫
      ((K.restriction e).extend e).d i j ≫
      (lower_stupid_truncation_x_iso K t j htj).hom =
        K.d i j
  rw [HomologicalComplex.extend_d_eq (K := K.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := K) (e := e) hi₀ hj₀]
  simp [lower_stupid_truncation_x_iso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso, e, i₀, j₀]

/-- Helper for Lemma 12.26.1: the degreewise components of the canonical map from the lower brutal
truncation into the original complex. -/
private noncomputable def lower_stupid_truncation_inclusion_f
    (K : AbCochainComplex) (t i : ℤ) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X i ⟶ K.X i :=
  if hti : t ≤ i then
    (lower_stupid_truncation_x_iso K t i hti).hom
  else
    0

/-- Helper for Lemma 12.26.1: in retained degrees, the lower-truncation inclusion component is the
canonical identification with the original term. -/
private theorem lower_stupid_truncation_inclusion_f_of_ge
    (K : AbCochainComplex) (t : ℤ) {i : ℤ} (hti : t ≤ i) :
    lower_stupid_truncation_inclusion_f K t i =
      (lower_stupid_truncation_x_iso K t i hti).hom := by
  -- The active branch of the component definition is exactly the retained-degree isomorphism.
  simp [lower_stupid_truncation_inclusion_f, hti]

/-- Helper for Chap12 Lemma 12 26 1: every retained source term comes from the corresponding
lower brutal truncation term. -/
private theorem lower_stupid_truncation_element_lift_of_ge
    (K : AbCochainComplex) (t i : ℤ) (hti : t ≤ i) (x : K.X i) :
    ∃ y : (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X i,
      lower_stupid_truncation_inclusion_f K t i y = x := by
  -- Use the retained-degree isomorphism to pull the element back to the truncation stage.
  refine ⟨(lower_stupid_truncation_x_iso K t i hti).inv x, ?_⟩
  rw [lower_stupid_truncation_inclusion_f_of_ge K t hti]
  simp

/-- Helper for Lemma 12.26.1: the componentwise lower-truncation inclusion is a chain map. -/
private theorem lower_stupid_truncation_inclusion_comm
    (K : AbCochainComplex) (t : ℤ) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      lower_stupid_truncation_inclusion_f K t i ≫ K.d i j =
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
          lower_stupid_truncation_inclusion_f K t j := by
  intro i j hij
  by_cases hti : t ≤ i
  · have htj : t ≤ j := by
      have hj : j = i + 1 := by
        simpa [ComplexShape.up, eq_comm] using hij
      omega
    -- On retained degrees, both truncation terms identify with the original ones.
    rw [lower_stupid_truncation_inclusion_f_of_ge K t hti,
      lower_stupid_truncation_inclusion_f_of_ge K t htj]
    calc
      (lower_stupid_truncation_x_iso K t i hti).hom ≫ K.d i j =
          (lower_stupid_truncation_x_iso K t i hti).hom ≫
            ((lower_stupid_truncation_x_iso K t i hti).inv ≫
              (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
                (lower_stupid_truncation_x_iso K t j htj).hom) := by
              rw [lower_stupid_truncation_d_via_x_iso K t hti htj]
      _ = (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
            (lower_stupid_truncation_x_iso K t j htj).hom := by
              simp [Category.assoc]
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
      simp [lower_stupid_truncation_inclusion_f, hti, htj, hsrczero]
    · -- If both degrees are discarded, every term in the square is already zero.
      simp [lower_stupid_truncation_inclusion_f, hti, htj]

/-- Helper for Lemma 12.26.1: the lower brutal truncation has a canonical inclusion into the
original complex. -/
private noncomputable def lower_stupid_truncation_inclusion
    (K : AbCochainComplex) (t : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE t) ⟶ K :=
  { f := fun i ↦ lower_stupid_truncation_inclusion_f K t i
    comm' := lower_stupid_truncation_inclusion_comm K t }

/-- Helper for Lemma 12.26.1: the functorial map induced on lower brutal truncations. -/
private noncomputable abbrev lower_stupid_truncation_map
    {K L : AbCochainComplex} (f : K ⟶ L) (t : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE t) ⟶
      L.stupidTrunc (ComplexShape.embeddingUpIntGE t) :=
  HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE t)

/-- Helper for Lemma 12.26.1: the lower-truncation inclusion is natural in the complex. -/
private theorem lower_stupid_truncation_map_comp_inclusion
    {K L : AbCochainComplex} (f : K ⟶ L) (t : ℤ) :
    lower_stupid_truncation_map f t ≫ lower_stupid_truncation_inclusion L t =
      lower_stupid_truncation_inclusion K t ≫ f := by
  ext i
  by_cases hti : t ≤ i
  · -- On retained degrees, both inclusions are the canonical identifications with degree `i`.
    let hi : (ComplexShape.embeddingUpIntGE t).f (Int.toNat (i - t)) = i :=
      embeddingUpIntGE_toNat_sub_eq t i hti
    simpa [lower_stupid_truncation_map, lower_stupid_truncation_inclusion,
      lower_stupid_truncation_inclusion_f_of_ge, lower_stupid_truncation_x_iso, hi] using
      (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
        (K := K) (L := L) (φ := f) (e := ComplexShape.embeddingUpIntGE t) hi)
  · -- Below the cutoff, both inclusion components vanish, so the square is trivial.
    simp [lower_stupid_truncation_map, lower_stupid_truncation_inclusion,
      lower_stupid_truncation_inclusion_f, hti]

/-- Helper for Lemma 12.26.1: the lower-truncation inclusions assemble into a natural
transformation from the truncation functor to the identity functor. -/
private noncomputable def lower_stupid_truncation_inclusion_nat_trans (t : ℤ) :
    (ComplexShape.embeddingUpIntGE t).stupidTruncFunctor AddCommGrpCat ⟶
      𝟭 AbCochainComplex where
  app K := lower_stupid_truncation_inclusion K t
  naturality := by
    intro K L f
    simpa [ComplexShape.Embedding.stupidTruncFunctor] using
      lower_stupid_truncation_map_comp_inclusion (K := K) (L := L) f t

/-- Helper for Lemma 12.26.1: rowwise lower brutal truncation of the exact complex of
complexes. -/
private noncomputable abbrev lower_stupid_truncation_sequence
    (A : AbCochainComplexSequence) (t : ℤ) :
    AbCochainComplexSequence :=
  (((ComplexShape.embeddingUpIntGE t).stupidTruncFunctor AddCommGrpCat).mapHomologicalComplex
    (up ℕ)).obj A

/-- Helper for Lemma 12.26.1: the rowwise lower truncation maps naturally into the original
coaugmented complex of complexes. -/
private noncomputable def lower_stupid_truncation_sequence_inclusion
    (A : AbCochainComplexSequence) (t : ℤ) :
    lower_stupid_truncation_sequence A t ⟶ A :=
  (NatTrans.mapHomologicalComplex
    (lower_stupid_truncation_inclusion_nat_trans t) (up ℕ)).app A

/-- Helper for Lemma 12.26.1: the coaugmentation truncates functorially with the rows. -/
private noncomputable abbrev lower_stupid_truncation_coaugmentation
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0) (t : ℤ) :
    M.stupidTrunc (ComplexShape.embeddingUpIntGE t) ⟶
      (lower_stupid_truncation_sequence A t).X 0 :=
  lower_stupid_truncation_map ι t

/-- Helper for Lemma 12.26.1: the truncated coaugmentation still lands in the cycles of the
first truncated row. -/
private theorem lower_stupid_truncation_coaugmentation_comp_d
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (t : ℤ) :
    lower_stupid_truncation_coaugmentation A ι t ≫
      (lower_stupid_truncation_sequence A t).d 0 1 = 0 := by
  -- The rowwise truncation is a functor, so the first differential is the truncation of
  -- `A.d 0 1`, and the cycle relation is preserved by functoriality.
  change lower_stupid_truncation_map ι t ≫ lower_stupid_truncation_map (A.d 0 1) t = 0
  simpa [lower_stupid_truncation_map, Functor.map_comp] using
    congrArg
      (fun k : M ⟶ A.X 1 ↦
        HomologicalComplex.stupidTruncMap k (ComplexShape.embeddingUpIntGE t))
      hι

/-- Helper for Lemma 12.26.1: truncating the coaugmentation is compatible with the canonical
inclusions back into the original row complexes. -/
private theorem lower_stupid_truncation_coaugmentation_comp_inclusion
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0) (t : ℤ) :
    lower_stupid_truncation_coaugmentation A ι t ≫
      (lower_stupid_truncation_sequence_inclusion A t).f 0 =
        lower_stupid_truncation_inclusion M t ≫ ι := by
  -- The degree-zero row of the outer naturality square is exactly the desired comparison.
  simpa [lower_stupid_truncation_coaugmentation, lower_stupid_truncation_sequence_inclusion] using
    lower_stupid_truncation_map_comp_inclusion (K := M) (L := A.X 0) ι t

/-- Helper for Lemma 12.26.1: the canonical map from a truncated stage into the total of the
truncated bicomplex. -/
private noncomputable def lower_stupid_truncation_to_total
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (t : ℤ) :
    M.stupidTrunc (ComplexShape.embeddingUpIntGE t) ⟶
      Tot (coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)) :=
  coaugmentedToTotal
    (lower_stupid_truncation_sequence A t)
    (lower_stupid_truncation_coaugmentation A ι t)
    (lower_stupid_truncation_coaugmentation_comp_d A ι hι t)

/-- Helper for Lemma 12.26.1: the flip symmetry of total complexes is natural in bicomplex
maps. This is the owner-level transport needed to compare stage totalization with the ambient
totalization. -/
private theorem totalFlipIso_hom_map_eq
    {B₁ B₂ : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ)}
    [B₁.HasTotal (up ℤ)] [B₂.HasTotal (up ℤ)]
    (φ : B₁ ⟶ B₂) :
    total.map ((flipFunctor AddCommGrpCat (up ℤ) (up ℤ)).map φ) (up ℤ) ≫
        (B₂.totalFlipIso (up ℤ)).hom =
      (B₁.totalFlipIso (up ℤ)).hom ≫ total.map φ (up ℤ) := by
  -- Compare the two composites on each antidiagonal summand of the flipped total complex.
  ext n
  apply total.hom_ext
  intro q p h
  calc
    B₁.flip.ιTotal (up ℤ) q p n h ≫
        (total.map ((flipFunctor AddCommGrpCat (up ℤ) (up ℤ)).map φ) (up ℤ)).f n ≫
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

/-- Helper for Lemma 12.26.1: postcomposing the zero-column comparison with a bicomplex map
agrees with postcomposing the induced total map by `total.map`. -/
private theorem doubleComplexZeroRow_comp_map_cycles
    {K : AbCochainComplex}
    {B₁ B₂ : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ)}
    (α : K ⟶ ((HomologicalComplex.eval AddCommGrpCat (up ℤ) (0 : ℤ)).mapHomologicalComplex
      (up ℤ)).obj B₁)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (B₁.X p).d 0 1 = 0)
    (β : B₁ ⟶ B₂) :
    ∀ p : ℤ,
      (α ≫ ((HomologicalComplex.eval AddCommGrpCat (up ℤ) (0 : ℤ)).mapHomologicalComplex
          (up ℤ)).map β).f p ≫ (B₂.X p).d 0 1 = 0 := by
  intro p
  -- Move the vertical differential across the column map `β.f p`.
  calc
    (α ≫ ((HomologicalComplex.eval AddCommGrpCat (up ℤ) (0 : ℤ)).mapHomologicalComplex
          (up ℤ)).map β).f p ≫
        (B₂.X p).d 0 1 =
      α.f p ≫ (β.f p).f 0 ≫ (B₂.X p).d 0 1 := by
        rfl
    _ = α.f p ≫ (B₁.X p).d 0 1 ≫ (β.f p).f 1 := by
      rw [Category.assoc, (β.f p).comm 0 1 (by simp)]
    _ = 0 := by
      rw [hαcycles p, zero_comp]

/-- Helper for Lemma 12.26.1: postcomposing the zero-column comparison with a bicomplex map
agrees with postcomposing the induced total map by `total.map`. -/
private theorem zero_column_to_total_comp_total_map
    {K : AbCochainComplex}
    {B₁ B₂ : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ)}
    [B₁.HasTotal (up ℤ)] [B₂.HasTotal (up ℤ)]
    (α : K ⟶ B₁.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (B₁.d 0 1).f q = 0)
    (φ : B₁ ⟶ B₂)
    (hcompcycles : ∀ q : ℤ, (α ≫ φ.f 0).f q ≫ (B₂.d 0 1).f q = 0) :
    doubleComplexZeroColumnToTotal (α ≫ φ.f 0) hcompcycles =
      doubleComplexZeroColumnToTotal α hαcycles ≫ total.map φ (up ℤ) := by
  let φflip := (flipFunctor AddCommGrpCat (up ℤ) (up ℤ)).map φ
  have hflip_map :
      doubleComplexZeroColumnToZeroRowFlip (α ≫ φ.f 0) =
        doubleComplexZeroColumnToZeroRowFlip α ≫
          ((HomologicalComplex.eval AddCommGrpCat (up ℤ) (0 : ℤ)).mapHomologicalComplex
            (up ℤ)).map φflip := by
    -- On the flipped zero row, the comparison is just postcomposition by the row map.
    ext q
    simp [doubleComplexZeroColumnToZeroRowFlip, φflip, Category.assoc]
  have hrow :
      doubleComplexZeroRowToTotal
          (doubleComplexZeroColumnToZeroRowFlip (α ≫ φ.f 0))
          (doubleComplexZeroColumnToZeroRowFlip_comp_d (α ≫ φ.f 0) hcompcycles) =
        doubleComplexZeroRowToTotal
          (doubleComplexZeroColumnToZeroRowFlip α ≫
            ((HomologicalComplex.eval AddCommGrpCat (up ℤ) (0 : ℤ)).mapHomologicalComplex
              (up ℤ)).map φflip)
          (doubleComplexZeroRow_comp_map_cycles
            (doubleComplexZeroColumnToZeroRowFlip α)
            (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles)
            φflip) := by
    rw [hflip_map]
    ext n
    rfl
  -- Rewrite through the flipped zero-row comparison, use row functoriality there, and then
  -- transport back with the naturality of `totalFlipIso`.
  calc
    doubleComplexZeroColumnToTotal (α ≫ φ.f 0) hcompcycles =
        doubleComplexZeroRowToTotal
            (doubleComplexZeroColumnToZeroRowFlip α ≫
              ((HomologicalComplex.eval AddCommGrpCat (up ℤ) (0 : ℤ)).mapHomologicalComplex
                (up ℤ)).map φflip)
            (doubleComplexZeroRow_comp_map_cycles
              (doubleComplexZeroColumnToZeroRowFlip α)
              (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles)
              φflip) ≫
          (B₂.totalFlipIso (up ℤ)).hom := by
      simp [doubleComplexZeroColumnToTotal, hrow]
    _ =
        doubleComplexZeroRowToTotal
            (doubleComplexZeroColumnToZeroRowFlip α)
            (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) ≫
          total.map φflip (up ℤ) ≫ (B₂.totalFlipIso (up ℤ)).hom := by
      rw [doubleComplexZeroRowToTotal_comp_map]
    _ =
        doubleComplexZeroRowToTotal
            (doubleComplexZeroColumnToZeroRowFlip α)
            (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) ≫
          (B₁.totalFlipIso (up ℤ)).hom ≫ total.map φ (up ℤ) := by
      rw [Category.assoc, totalFlipIso_hom_map_eq, ← Category.assoc]
    _ = doubleComplexZeroColumnToTotal α hαcycles ≫ total.map φ (up ℤ) := by
      rfl

/-- Helper for Lemma 12.26.1: the stage total map compares to the ambient total map through the
canonical inclusion of the truncated bicomplex into the original bicomplex. -/
private theorem lower_stupid_truncation_to_total_compare
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (t : ℤ) :
    lower_stupid_truncation_to_total A ι hι t ≫
        total.map
          (HomologicalComplex.extendMap
            (lower_stupid_truncation_sequence_inclusion A t) embeddingUpNat)
          (up ℤ) =
      lower_stupid_truncation_inclusion M t ≫ coaugmentedToTotal A ι hι := by
  let φ :
      coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t) ⟶
        coaugmentedColumnBicomplex A :=
    HomologicalComplex.extendMap
      (lower_stupid_truncation_sequence_inclusion A t) embeddingUpNat
  have hφ0 :
      φ.f 0 =
        (coaugmentedColumnBicomplexZeroIso (lower_stupid_truncation_sequence A t)).hom ≫
          (lower_stupid_truncation_sequence_inclusion A t).f 0 ≫
            (coaugmentedColumnBicomplexZeroIso A).inv := by
    -- Degree `0` in the extended outer complex is the original degree `0` row.
    simpa [φ, coaugmentedColumnBicomplex, coaugmentedColumnBicomplexZeroIso] using
      (HomologicalComplex.extendMap_f
        (lower_stupid_truncation_sequence_inclusion A t) embeddingUpNat
        (i := 0) (i' := (0 : ℤ)) rfl)
  have hcol :
      coaugmentedToZeroColumn
          (lower_stupid_truncation_sequence A t)
          (lower_stupid_truncation_coaugmentation A ι t) ≫
        φ.f 0 =
      lower_stupid_truncation_inclusion M t ≫ coaugmentedToZeroColumn A ι := by
    -- Rewrite the degree-zero column map through the explicit `extendMap` component and the
    -- degree-zero inclusion square for the truncated coaugmentation.
    rw [hφ0, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, lower_stupid_truncation_coaugmentation_comp_inclusion]
    simp [coaugmentedToZeroColumn, Category.assoc]
  have hcompcycles :
      ∀ q : ℤ,
        ((coaugmentedToZeroColumn
            (lower_stupid_truncation_sequence A t)
            (lower_stupid_truncation_coaugmentation A ι t)) ≫
          φ.f 0).f q ≫ ((coaugmentedColumnBicomplex A).d 0 1).f q = 0 := by
    intro q
    -- After the zero-column comparison is identified with the ambient coaugmentation map,
    -- the horizontal cycle condition is exactly the original one precomposed with the cutoff
    -- inclusion.
    rw [hcol]
    simp [Category.assoc, coaugmentedToZeroColumn_comp_d A ι hι q]
  -- Apply the owner-level functoriality of zero-column totalization to the bicomplex inclusion.
  simpa [lower_stupid_truncation_to_total, coaugmentedToTotal, φ] using
    zero_column_to_total_comp_total_map
      (coaugmentedToZeroColumn
        (lower_stupid_truncation_sequence A t)
        (lower_stupid_truncation_coaugmentation A ι t))
      (coaugmentedToZeroColumn_comp_d
        (lower_stupid_truncation_sequence A t)
        (lower_stupid_truncation_coaugmentation A ι t)
        (lower_stupid_truncation_coaugmentation_comp_d A ι hι t))
      φ hcompcycles

/-- Helper for Lemma 12.26.1: in `AddCommGrpCat`, an exact short complex with monic left map
identifies its left term with the cycles of the right map. -/
private theorem shortComplex_toCycles_isIso_of_exact_of_mono
    (S : ShortComplex AddCommGrpCat) (hS : S.Exact) [Mono S.f] :
    IsIso S.toCycles := by
  -- This is the exact-to-kernel bridge used in the retained branch of the cutoff argument.
  simpa using hS.isIso_toCycles

/-- Helper for Lemma 12.26.1: evaluating the coaugmented exact row at a fixed degree preserves
the exact short-complex structure. -/
private theorem coaugmented_row_exact_eval
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0)
    (hExact₀ : (ShortComplex.mk ι (A.d 0 1) hι).Exact) (q : ℤ) :
    (ShortComplex.mk
      (ι.f q)
      ((A.d 0 1).f q)
      (by
        -- The evaluated short complex keeps the same vanishing composition degreewise.
        simpa using congrArg (fun f ↦ f.f q) hι)).Exact := by
  let F := HomologicalComplex.eval AddCommGrpCat (up ℤ) q
  -- Evaluation is an additive functor, so it preserves exact short complexes.
  simpa [F] using hExact₀.map F

/-- Helper for Lemma 12.26.1: evaluating an exact outer row of complexes at a fixed vertical
degree gives an exact short complex of abelian groups. -/
private theorem outer_row_exact_eval
    (A : AbCochainComplexSequence)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (n : ℕ) (q : ℤ) :
    (ShortComplex.mk
      ((A.d n (n + 1)).f q)
      ((A.d (n + 1) (n + 2)).f q)
      (by
        -- Degreewise evaluation turns `d ≫ d = 0` into the needed short-complex relation.
        simpa using congrArg (fun f ↦ f.f q) (A.d_comp_d n (n + 1) (n + 2))).Exact := by
  let F := HomologicalComplex.eval AddCommGrpCat (up ℤ) q
  -- Reuse exactness of the outer short complex and evaluate it degreewise.
  simpa [HomologicalComplex.ExactAt, HomologicalComplex.exactAt_iff, F] using
    (hExact n).map F

/-- Helper for Lemma 12.26.1: evaluating two consecutive outer differentials at degree `q`
still gives a short-complex relation. -/
private theorem outer_row_component_comp_d
    (A : AbCochainComplexSequence) (n : ℕ) (q : ℤ) :
    ((A.d n (n + 1)).f q) ≫ ((A.d (n + 1) (n + 2)).f q) = 0 := by
  -- Degreewise evaluation of `d ≫ d = 0` gives the short-complex relation.
  simpa using congrArg (fun f ↦ f.f q) (A.d_comp_d n (n + 1) (n + 2))

/-- Helper for Lemma 12.26.1: the degree-`q` outer row
`A_n^q ⟶ A_{n+1}^q ⟶ A_{n+2}^q` as a short complex. -/
private noncomputable abbrev outer_row_shortComplex
    (A : AbCochainComplexSequence) (n : ℕ) (q : ℤ) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk
    ((A.d n (n + 1)).f q)
    ((A.d (n + 1) (n + 2)).f q)
    (outer_row_component_comp_d A n q)

/-- Helper for Lemma 12.26.1: below the cutoff, every term of the rowwise lower brutal
truncation is zero. -/
private theorem lower_stupid_truncation_sequence_isZero_X_of_lt
    (A : AbCochainComplexSequence) (t : ℤ) (p : ℕ) {q : ℤ} (hqt : q < t) :
    IsZero (((lower_stupid_truncation_sequence A t).X p).X q) := by
  -- The `p`-th row is just the lower brutal truncation of `A.X p`, so discarded degrees vanish.
  exact (A.X p).isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) q
    (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hqt)

/-- Helper for Lemma 12.26.1: in a retained degree, evaluating the rowwise lower brutal
truncation recovers the original row term. -/
private noncomputable def lower_stupid_truncation_sequence_x_iso
    (A : AbCochainComplexSequence) (t : ℤ) (p : ℕ) (q : ℤ) (htq : t ≤ q) :
    ((lower_stupid_truncation_sequence A t).X p).X q ≅ (A.X p).X q :=
  lower_stupid_truncation_x_iso (A.X p) t q htq

/-- Helper for Lemma 12.26.1: in a retained degree, the rowwise truncation inclusion component is
the canonical identification with the original row term. -/
private theorem lower_stupid_truncation_sequence_inclusion_f_of_ge
    (A : AbCochainComplexSequence) (t : ℤ) (p : ℕ) {q : ℤ} (htq : t ≤ q) :
    ((lower_stupid_truncation_sequence_inclusion A t).f p).f q =
      (lower_stupid_truncation_sequence_x_iso A t p q htq).hom := by
  -- The outer natural transformation is rowwise the lower-truncation inclusion.
  simpa [lower_stupid_truncation_sequence_inclusion, lower_stupid_truncation_sequence_x_iso,
    lower_stupid_truncation_sequence] using
    (lower_stupid_truncation_inclusion_f_of_ge (K := A.X p) t htq)

/-- Helper for Lemma 12.26.1: on a retained antidiagonal summand, the stage-to-ambient total map
acts by the canonical rowwise lower-truncation inclusion. -/
private theorem totalStageInclusion_iota_assoc
    (A : AbCochainComplexSequence) (t : ℤ) (p : ℕ) {q n : ℤ}
    (h : (p : ℤ) + q = n) (htq : t ≤ q) :
    (coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).ιTotal (up ℤ) p q n h ≫
        (total.map
          (HomologicalComplex.extendMap
            (lower_stupid_truncation_sequence_inclusion A t) embeddingUpNat)
          (up ℤ)).f n =
      (lower_stupid_truncation_sequence_x_iso A t p q htq).hom ≫
        (coaugmentedColumnBicomplex A).ιTotal (up ℤ) p q n h := by
  -- Evaluate the owner `total.map` formula on one retained summand, then rewrite the row map by
  -- the retained-degree truncation identification.
  rw [ιTotal_map_assoc]
  have hfp :
      (HomologicalComplex.extendMap
          (lower_stupid_truncation_sequence_inclusion A t) embeddingUpNat).f p =
        (coaugmentedColumnBicomplexXIso (lower_stupid_truncation_sequence A t) p).hom ≫
          (lower_stupid_truncation_sequence_inclusion A t).f p ≫
            (coaugmentedColumnBicomplexXIso A p).inv := by
    simpa [coaugmentedColumnBicomplex, coaugmentedColumnBicomplexXIso] using
      (HomologicalComplex.extendMap_f
        (lower_stupid_truncation_sequence_inclusion A t) embeddingUpNat
        (i := p) (i' := (p : ℤ)) (embeddingUpNat_f_eq p))
  rw [hfp]
  rw [lower_stupid_truncation_sequence_inclusion_f_of_ge A t p htq]
  simp [coaugmentedColumnBicomplexXIso, lower_stupid_truncation_sequence_x_iso, Category.assoc]

/-- Helper for Lemma 12.26.1: the vertical differential in a retained degree of the truncated
`p`-th row is the original vertical differential. -/
private theorem lower_stupid_truncation_sequence_row_d_via_x_iso
    (A : AbCochainComplexSequence) (t : ℤ) (p : ℕ) {i j : ℤ}
    (hti : t ≤ i) (htj : t ≤ j) :
    (lower_stupid_truncation_sequence_x_iso A t p i hti).inv ≫
      ((lower_stupid_truncation_sequence A t).X p).d i j ≫
      (lower_stupid_truncation_sequence_x_iso A t p j htj).hom =
        (A.X p).d i j := by
  -- This is exactly the retained-degree transport theorem for the brutally truncated `p`-th row.
  simpa [lower_stupid_truncation_sequence_x_iso, lower_stupid_truncation_sequence] using
    lower_stupid_truncation_d_via_x_iso (K := A.X p) t hti htj

/-- Helper for Lemma 12.26.1: in a retained vertical degree, the horizontal map of the rowwise
lower brutal truncation is the original outer differential evaluated at that degree. -/
private theorem lower_stupid_truncation_sequence_map_f_via_x_iso
    (A : AbCochainComplexSequence) (t : ℤ) {p p' : ℕ} (q : ℤ) (htq : t ≤ q) :
    (lower_stupid_truncation_sequence_x_iso A t p q htq).inv ≫
      ((lower_stupid_truncation_sequence A t).d p p').f q ≫
      (lower_stupid_truncation_sequence_x_iso A t p' q htq).hom =
        (A.d p p').f q := by
  let hq : (ComplexShape.embeddingUpIntGE t).f (Int.toNat (q - t)) = q :=
    embeddingUpIntGE_toNat_sub_eq t q htq
  have hmap :
      ((lower_stupid_truncation_sequence A t).d p p').f q ≫
        (lower_stupid_truncation_sequence_x_iso A t p' q htq).hom =
      (lower_stupid_truncation_sequence_x_iso A t p q htq).hom ≫
        (A.d p p').f q := by
    -- The rowwise truncation is functorial, so evaluation at a retained degree commutes with the
    -- outer differential after identifying both truncated terms with the original ones.
    simpa [lower_stupid_truncation_sequence, lower_stupid_truncation_map,
      lower_stupid_truncation_sequence_x_iso, hq] using
      (HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
        (K := A.X p) (L := A.X p') (φ := A.d p p')
        (e := ComplexShape.embeddingUpIntGE t) hq)
  calc
    (lower_stupid_truncation_sequence_x_iso A t p q htq).inv ≫
        ((lower_stupid_truncation_sequence A t).d p p').f q ≫
        (lower_stupid_truncation_sequence_x_iso A t p' q htq).hom =
      (lower_stupid_truncation_sequence_x_iso A t p q htq).inv ≫
        ((lower_stupid_truncation_sequence_x_iso A t p q htq).hom ≫
          (A.d p p').f q) := by
            rw [hmap]
    _ = (A.d p p').f q := by
      simp [Category.assoc]

/-- Helper for Lemma 12.26.1: the degree-`q` component of the original coaugmentation still lands
in the cycles of the first row. -/
private theorem coaugmented_row_component_comp_d
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (q : ℤ) :
    ι.f q ≫ (A.d 0 1).f q = 0 := by
  -- The chain-map vanishing relation is checked degreewise.
  simpa using congrArg (fun f ↦ f.f q) hι

/-- Helper for Lemma 12.26.1: the degree-`q` component of the truncated coaugmentation still
lands in the cycles of the first truncated row. -/
private theorem lower_stupid_truncation_coaugmentation_component_comp_d
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (t q : ℤ) :
    (lower_stupid_truncation_coaugmentation A ι t).f q ≫
      ((lower_stupid_truncation_sequence A t).d 0 1).f q = 0 := by
  -- Degreewise evaluation turns the chain-map vanishing relation into the needed row equation.
  simpa using congrArg
    (fun f :
      M.stupidTrunc (ComplexShape.embeddingUpIntGE t) ⟶
        (lower_stupid_truncation_sequence A t).X 1 ↦ f.f q)
    (lower_stupid_truncation_coaugmentation_comp_d A ι hι t)

/-- Helper for Lemma 12.26.1: the retained stage row at outer degree `0` is the original
coaugmentation row in vertical degree `q`. -/
private noncomputable abbrev truncated_original_row_shortComplex
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (q : ℤ) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk
    (ι.f q)
    ((A.d 0 1).f q)
    (coaugmented_row_component_comp_d A ι hι q)

/-- Helper for Lemma 12.26.1: the retained stage zero-column row short complex whose `toCycles`
map is the stage `doubleComplexZeroColumnCyclesMap`. -/
private noncomputable abbrev truncated_stage_zero_column_shortComplex
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (t q : ℤ) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk
    ((doubleComplexZeroColumnToZeroRowFlip
        (coaugmentedToZeroColumn
          (lower_stupid_truncation_sequence A t)
          (lower_stupid_truncation_coaugmentation A ι t))).f q)
    (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).d 0 1)
    (doubleComplexZeroColumnToZeroRowFlip_comp_d
      (coaugmentedToZeroColumn
        (lower_stupid_truncation_sequence A t)
        (lower_stupid_truncation_coaugmentation A ι t))
      (coaugmentedToZeroColumn_comp_d
        (lower_stupid_truncation_sequence A t)
        (lower_stupid_truncation_coaugmentation A ι t)
        (lower_stupid_truncation_coaugmentation_comp_d A ι hι t))
      q)

/-- Helper for Lemma 12.26.1: the retained stage row before undoing the lower-truncation
identifications. -/
private noncomputable abbrev truncated_rowwise_shortComplex
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (t q : ℤ) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk
    ((lower_stupid_truncation_coaugmentation A ι t).f q)
    (((lower_stupid_truncation_sequence A t).d 0 1).f q)
    (lower_stupid_truncation_coaugmentation_component_comp_d A ι hι t q)

/-- Helper for Lemma 12.26.1: the outer-degree embedding `ℕ ↪ ℤ` is definitionally the usual
coercion. -/
private theorem embeddingUpNat_f_eq (p : ℕ) :
    (ComplexShape.embeddingUpNat.f p : ℤ) = p := rfl

/-- Helper for Lemma 12.26.1: evaluating the extended bicomplex in an outer degree recovers the
corresponding original row complex. -/
private noncomputable def coaugmentedColumnBicomplexXIso
    (A : AbCochainComplexSequence) (p : ℕ) :
    (coaugmentedColumnBicomplex A).X p ≅ A.X p :=
  A.extendXIso embeddingUpNat (embeddingUpNat_f_eq p)

/-- Helper for Lemma 12.26.1: the outer differential of the extended bicomplex is the original
outer differential after transporting through the canonical row identifications. -/
private theorem coaugmentedColumnBicomplex_d_eq
    (A : AbCochainComplexSequence) (p p' : ℕ) :
    (coaugmentedColumnBicomplex A).d p p' =
      (coaugmentedColumnBicomplexXIso A p).hom ≫
        A.d p p' ≫
        (coaugmentedColumnBicomplexXIso A p').inv := by
  -- Rewrite the outer differential of the extended bicomplex back to the original sequence.
  simpa [coaugmentedColumnBicomplex, coaugmentedColumnBicomplexXIso] using
    (HomologicalComplex.extend_d_eq
      (K := A) (e := embeddingUpNat)
      (i := p) (j := p') (i' := (p : ℤ)) (j' := (p' : ℤ))
      (embeddingUpNat_f_eq p) (embeddingUpNat_f_eq p'))

/-- Helper for Lemma 12.26.1: cancelling only the owner-level flip/extend transport identifies the
stage zero-column row with the explicit truncated row in degree `q`. -/
private noncomputable def stage_zero_column_shortComplex_iso_rowwise_truncation
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (t q : ℤ) :
    truncated_stage_zero_column_shortComplex A ι hι t q ≅
      truncated_rowwise_shortComplex A ι hι t q := by
  let e₂ :
      (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).X 0) ≅
        (((lower_stupid_truncation_sequence A t).X 0).X q) :=
    (HomologicalComplex.eval AddCommGrpCat (up ℤ) q).mapIso
      (coaugmentedColumnBicomplexXIso (lower_stupid_truncation_sequence A t) 0)
  let e₃ :
      (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).X 1) ≅
        (((lower_stupid_truncation_sequence A t).X 1).X q) :=
    (HomologicalComplex.eval AddCommGrpCat (up ℤ) q).mapIso
      (coaugmentedColumnBicomplexXIso (lower_stupid_truncation_sequence A t) 1)
  -- The source term is unchanged; only the middle and right terms need the owner-level
  -- `extendXIso` identification in outer degrees `0` and `1`.
  refine ShortComplex.isoMk (Iso.refl _) e₂ e₃ ?_ ?_
  · -- The first square is exactly the cancellation between the zero-column identification and the
    -- rowwise `extendXIso` in outer degree `0`.
    simp only [truncated_stage_zero_column_shortComplex, truncated_rowwise_shortComplex,
      doubleComplexZeroColumnToZeroRowFlip, coaugmentedToZeroColumn,
      coaugmentedColumnBicomplexXIso, Category.assoc]
  · -- The second square is the degree-`q` component of the outer differential comparison.
    have hd :
        (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).d 0 1) =
          e₂.hom ≫
            (((lower_stupid_truncation_sequence A t).d 0 1).f q) ≫
            e₃.inv := by
      simpa [e₂, e₃] using
        congrArg (fun f ↦ f.f q)
          (coaugmentedColumnBicomplex_d_eq (lower_stupid_truncation_sequence A t) 0 1)
    -- Postcompose the transported differential comparison with `e₃.hom`.
    calc
      e₂.hom ≫ (((lower_stupid_truncation_sequence A t).d 0 1).f q)
          = e₂.hom ≫ (((lower_stupid_truncation_sequence A t).d 0 1).f q) ≫ e₃.inv ≫ e₃.hom := by
              simp [Category.assoc]
      _ = (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).d 0 1) ≫
            e₃.hom := by
              rw [hd]
              simp [Category.assoc]

/-- Helper for Lemma 12.26.1: in a retained degree, cancelling the lower-truncation transport
identifies the truncated row with the original coaugmentation row. -/
private noncomputable def rowwise_truncation_coaugmentation_shortComplex_iso_of_ge
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (t q : ℤ) (htq : t ≤ q) :
    truncated_rowwise_shortComplex A ι hι t q ≅
      truncated_original_row_shortComplex A ι hι q := by
  let e₁ : (M.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X q ≅ M.X q :=
    lower_stupid_truncation_x_iso M t q htq
  let e₂ :
      (((lower_stupid_truncation_sequence A t).X 0).X q) ≅ ((A.X 0).X q) :=
    lower_stupid_truncation_sequence_x_iso A t 0 q htq
  let e₃ :
      (((lower_stupid_truncation_sequence A t).X 1).X q) ≅ ((A.X 1).X q) :=
    lower_stupid_truncation_sequence_x_iso A t 1 q htq
  -- In retained degree `q`, the truncated row is the original row after cancelling the
  -- lower-truncation inclusions on `M`, `A₀`, and `A₁`.
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · have hcomp :
        (lower_stupid_truncation_coaugmentation A ι t).f q ≫ e₂.hom =
          e₁.hom ≫ ι.f q := by
      simpa [e₁, e₂, Category.assoc] using
        congrArg (fun f ↦ f.f q)
          (lower_stupid_truncation_coaugmentation_comp_inclusion A ι t)
    -- This is the retained-degree component of the naturality square for the truncation
    -- inclusion and the coaugmentation.
    simpa [truncated_rowwise_shortComplex, truncated_original_row_shortComplex] using hcomp.symm
  · -- The second square is exactly the retained-degree transport formula for the outer
    -- differential of the truncated row.
    calc
      e₂.hom ≫ (A.d 0 1).f q =
          e₂.hom ≫
            (e₂.inv ≫ ((lower_stupid_truncation_sequence A t).d 0 1).f q ≫ e₃.hom) := by
              rw [lower_stupid_truncation_sequence_map_f_via_x_iso A t q htq]
      _ = ((lower_stupid_truncation_sequence A t).d 0 1).f q ≫ e₃.hom := by
            simp [Category.assoc]

/-- Helper for Lemma 12.26.1: in a retained vertical degree, the stage zero-column row short
complex is canonically identified with the original coaugmentation row. -/
private noncomputable def truncated_coaugmentation_shortComplex_iso_of_ge
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) (t q : ℤ) (htq : t ≤ q) :
    truncated_stage_zero_column_shortComplex A ι hι t q ≅
      truncated_original_row_shortComplex A ι hι q := by
  -- Compose the owner-level transport with the retained-degree truncation transport.
  exact
    stage_zero_column_shortComplex_iso_rowwise_truncation A ι hι t q ≪≫
      rowwise_truncation_coaugmentation_shortComplex_iso_of_ge A ι hι t q htq

/-- Helper for Lemma 12.26.1: in a retained vertical degree, the stage zero-column map is monic
because it is conjugate to the original coaugmentation component. -/
private theorem truncated_stage_zero_column_mono_of_ge
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) [Mono ι]
    (t q : ℤ) (htq : t ≤ q) :
    Mono (truncated_stage_zero_column_shortComplex A ι hι t q).f := by
  let e := truncated_coaugmentation_shortComplex_iso_of_ge A ι hι t q htq
  have hιq : Mono ((truncated_original_row_shortComplex A ι hι q).f) := by
    change Mono ((HomologicalComplex.eval AddCommGrpCat (up ℤ) q).map ι)
    infer_instance
  have hf :
      (truncated_stage_zero_column_shortComplex A ι hι t q).f =
        e.hom.τ₁ ≫ (truncated_original_row_shortComplex A ι hι q).f ≫ e.inv.τ₂ := by
    -- Solve for the stage left map from the first commutative square of the short-complex
    -- isomorphism.
    calc
      (truncated_stage_zero_column_shortComplex A ι hι t q).f
          = (truncated_stage_zero_column_shortComplex A ι hι t q).f ≫ e.hom.τ₂ ≫ e.inv.τ₂ := by
              simp [Category.assoc]
      _ = e.hom.τ₁ ≫ (truncated_original_row_shortComplex A ι hι q).f ≫ e.inv.τ₂ := by
            rw [← Category.assoc, ← e.hom.comm₁₂]
            simp [Category.assoc]
  -- The stage left map is a composite of two isomorphisms with the monic component `ι.f q`.
  simpa [hf]

/-- Helper for Lemma 12.26.1: in a retained vertical degree, the stage zero-column row short
complex is exact because it is isomorphic to the original exact row. -/
private theorem truncated_stage_zero_column_exact_of_ge
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0)
    (hExact₀ : (ShortComplex.mk ι (A.d 0 1) hι).Exact)
    (t q : ℤ) (htq : t ≤ q) :
    (truncated_stage_zero_column_shortComplex A ι hι t q).Exact := by
  -- Transport exactness of the original coaugmentation row back along the stage comparison.
  exact
    (ShortComplex.exact_iff_of_iso
      (truncated_coaugmentation_shortComplex_iso_of_ge A ι hι t q htq)).2
      (coaugmented_row_exact_eval A ι hι hExact₀ q)

/-- Helper for Lemma 12.26.1: the stage zero-column cycles map is an isomorphism in every
retained vertical degree. -/
private theorem truncated_zero_column_cycles_isIso_of_ge
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) [Mono ι]
    (hExact₀ : (ShortComplex.mk ι (A.d 0 1) hι).Exact)
    (t q : ℤ) (htq : t ≤ q) :
    IsIso
      (doubleComplexZeroColumnCyclesMap
        (coaugmentedToZeroColumn
          (lower_stupid_truncation_sequence A t)
          (lower_stupid_truncation_coaugmentation A ι t))
        (coaugmentedToZeroColumn_comp_d
          (lower_stupid_truncation_sequence A t)
          (lower_stupid_truncation_coaugmentation A ι t)
          (lower_stupid_truncation_coaugmentation_comp_d A ι hι t))
        q) := by
  -- The stage cycles map is exactly the `toCycles` map of the transported stage short complex.
  simpa [doubleComplexZeroColumnCyclesMap, doubleComplexZeroRowCyclesMap,
    truncated_stage_zero_column_shortComplex] using
    (shortComplex_toCycles_isIso_of_exact_of_mono
      (truncated_stage_zero_column_shortComplex A ι hι t q)
      (truncated_stage_zero_column_exact_of_ge A ι hι hExact₀ t q htq))

/-- Helper for Lemma 12.26.1: in a retained vertical degree, the truncated flipped row slice is
canonically the evaluated original outer row. -/
private noncomputable def truncated_row_shortComplex_iso_of_ge
    (A : AbCochainComplexSequence) (t q : ℤ) (n : ℕ) (htq : t ≤ q) :
    (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).sc'
      n (n + 1) (n + 2)) ≅
      outer_row_shortComplex A n q := by
  let e₀ (p : ℕ) :
      (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).X p) ≅
        (((lower_stupid_truncation_sequence A t).X p).X q) :=
    (HomologicalComplex.eval AddCommGrpCat (up ℤ) q).mapIso
      (coaugmentedColumnBicomplexXIso (lower_stupid_truncation_sequence A t) p)
  let e₁ (p : ℕ) :
      (((lower_stupid_truncation_sequence A t).X p).X q) ≅ ((A.X p).X q) :=
    lower_stupid_truncation_sequence_x_iso A t p q htq
  let e (p : ℕ) :
      (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).X p) ≅
        ((A.X p).X q) :=
    e₀ p ≪≫ e₁ p
  have hcomm :
      ∀ p p' : ℕ,
        (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).d p p') ≫
            (e p').hom =
          (e p).hom ≫ (A.d p p').f q := by
    intro p p'
    have hd₀ :
        (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).d p p') =
          (e₀ p).hom ≫
            (((lower_stupid_truncation_sequence A t).d p p').f q) ≫
            (e₀ p').inv := by
      -- Evaluating the extended outer differential identifies it with the rowwise truncation map.
      simpa [e₀] using
        congrArg (fun f ↦ f.f q)
          (coaugmentedColumnBicomplex_d_eq (lower_stupid_truncation_sequence A t) p p')
    have hd₁ :
        (((lower_stupid_truncation_sequence A t).d p p').f q) =
          (e₁ p).hom ≫ (A.d p p').f q ≫ (e₁ p').inv := by
      -- In retained degree `q`, the rowwise truncation map is the original outer differential.
      calc
        (((lower_stupid_truncation_sequence A t).d p p').f q)
            = (e₁ p).hom ≫
                ((e₁ p).inv ≫
                  (((lower_stupid_truncation_sequence A t).d p p').f q) ≫
                  (e₁ p').hom) ≫
                (e₁ p').inv := by
                  simp [Category.assoc]
        _ = (e₁ p).hom ≫ (A.d p p').f q ≫ (e₁ p').inv := by
              rw [lower_stupid_truncation_sequence_map_f_via_x_iso
                (A := A) (t := t) (p := p) (p' := p') q htq]
    -- Compose the owner-level `extendXIso` comparison with the retained-degree truncation
    -- comparison to identify the truncated row differential with the original one.
    rw [hd₀, hd₁]
    simp [e, Category.assoc]
  refine ShortComplex.isoMk (e n) (e (n + 1)) (e (n + 2)) ?_ ?_
  · -- The first square compares the `n → n + 1` differential in the truncated flipped row with
    -- the evaluated original outer differential.
    simpa [outer_row_shortComplex] using hcomm n (n + 1)
  · -- The second square is the same comparison one step further along the row.
    simpa [outer_row_shortComplex] using hcomm (n + 1) (n + 2)

/-- Helper for Lemma 12.26.1: in a retained vertical degree, the positive rows of the truncated
bicomplex are exact. -/
private theorem truncated_row_exactAt_of_ge
    (A : AbCochainComplexSequence)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (t q : ℤ) (n : ℕ) (htq : t ≤ q) :
    ((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).ExactAt
      (n + 1) := by
  let S :
      ShortComplex AddCommGrpCat :=
    (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).sc'
      n (n + 1) (n + 2))
  have hSExact : S.Exact := by
    -- Transport exactness of the evaluated original outer row back to the retained truncated row.
    exact
      (ShortComplex.exact_iff_of_iso
        (truncated_row_shortComplex_iso_of_ge A t q n htq)).2
        (by
          simpa [outer_row_shortComplex] using outer_row_exact_eval A hExact n q)
  simpa [S, HomologicalComplex.exactAt_iff] using hSExact

/-- Helper for Lemma 12.26.1: in a discarded vertical degree, every object of the flipped
truncated row vanishes. -/
private theorem truncated_row_object_isZero_of_lt
    (A : AbCochainComplexSequence) (t q : ℤ) (hqt : q < t) (p : ℕ) :
    IsZero ((((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).X p)) := by
  let e :
      (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).X p) ≅
        (((lower_stupid_truncation_sequence A t).X p).X q) :=
    (HomologicalComplex.eval AddCommGrpCat (up ℤ) q).mapIso
      (coaugmentedColumnBicomplexXIso (lower_stupid_truncation_sequence A t) p)
  -- Evaluating the owner-level outer-degree identification reduces the claim to the discarded
  -- rowwise truncation term.
  exact e.isZero_iff.mpr (lower_stupid_truncation_sequence_isZero_X_of_lt A t p hqt)

/-- Helper for Lemma 12.26.1: every positive row of the truncated bicomplex is exact, including
the discarded vertical degrees where the whole row vanishes. -/
private theorem truncated_row_exactAt
    (A : AbCochainComplexSequence)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (t q p : ℤ) (hp : 0 < p) :
    ((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).ExactAt p := by
  let n : ℕ := Int.toNat (p - 1)
  have hp_eq : (n : ℤ) + 1 = p := by
    dsimp [n]
    omega
  by_cases htq : t ≤ q
  · -- In retained degrees, exactness is already proved by transport to the original row.
    simpa [hp_eq] using truncated_row_exactAt_of_ge A hExact t q n htq
  · have hqt : q < t := lt_of_not_ge htq
    let S :
        ShortComplex AddCommGrpCat :=
      (((coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)).flip.X q).sc'
        n (n + 1) (n + 2))
    have h₁ : IsZero S.X₁ := by
      -- The discarded row is zero termwise, so the left object of the short complex vanishes.
      simpa [S] using truncated_row_object_isZero_of_lt A t q hqt n
    have h₂ : IsZero S.X₂ := by
      -- The same discarded-degree argument kills the middle object.
      simpa [S] using truncated_row_object_isZero_of_lt A t q hqt (n + 1)
    have h₃ : IsZero S.X₃ := by
      -- The right object also vanishes in the discarded row.
      simpa [S] using truncated_row_object_isZero_of_lt A t q hqt (n + 2)
    let e₁₂ : S.X₁ ≅ S.X₂ := h₁.iso h₂
    have hf : S.f = e₁₂.hom := by
      -- Any morphism out of a zero object agrees with the canonical isomorphism.
      exact h₁.eq_of_src _ _
    haveI : IsIso S.f := by
      rw [hf]
      infer_instance
    have hshort : S.ShortExact :=
      (ShortComplex.Splitting.ofIsIsoOfIsZero S inferInstance h₃).shortExact
    -- A split short exact sequence gives exactness at the middle object.
    simpa [S, hp_eq, HomologicalComplex.exactAt_iff] using hshort.exact

/-- Helper for Lemma 12.26.1: the stage zero-column row short complex is monic in every vertical
degree, including discarded degrees where all objects vanish. -/
private theorem truncated_stage_zero_column_mono
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) [Mono ι]
    (t q : ℤ) :
    Mono (truncated_stage_zero_column_shortComplex A ι hι t q).f := by
  by_cases htq : t ≤ q
  · -- The retained branch is already identified with the original monomorphism `ι.f q`.
    exact truncated_stage_zero_column_mono_of_ge A ι hι t q htq
  · have hqt : q < t := lt_of_not_ge htq
    let S : ShortComplex AddCommGrpCat := truncated_stage_zero_column_shortComplex A ι hι t q
    have h₁ : IsZero S.X₁ := by
      -- The source term of the truncated coaugmentation vanishes below the cutoff.
      exact M.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) q
        (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hqt)
    have h₂ : IsZero S.X₂ := by
      -- The degree-zero row object of the discarded stage vanishes with the whole row.
      simpa [S, truncated_stage_zero_column_shortComplex] using
        truncated_row_object_isZero_of_lt A t q hqt 0
    let e₁₂ : S.X₁ ≅ S.X₂ := h₁.iso h₂
    have hf : S.f = e₁₂.hom := by
      -- Any map out of the zero source is forced to be the canonical isomorphism.
      exact h₁.eq_of_src _ _
    rw [hf]
    infer_instance

/-- Helper for Lemma 12.26.1: the stage zero-column row short complex is exact in every vertical
degree, including discarded degrees where it is split by zero objects. -/
private theorem truncated_stage_zero_column_exact
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0)
    (hExact₀ : (ShortComplex.mk ι (A.d 0 1) hι).Exact)
    (t q : ℤ) :
    (truncated_stage_zero_column_shortComplex A ι hι t q).Exact := by
  by_cases htq : t ≤ q
  · -- In retained degrees, exactness is transported from the original coaugmentation row.
    exact truncated_stage_zero_column_exact_of_ge A ι hι hExact₀ t q htq
  · have hqt : q < t := lt_of_not_ge htq
    let S : ShortComplex AddCommGrpCat := truncated_stage_zero_column_shortComplex A ι hι t q
    have h₁ : IsZero S.X₁ := by
      -- The source term of the truncated coaugmentation vanishes below the cutoff.
      exact M.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) q
        (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hqt)
    have h₂ : IsZero S.X₂ := by
      -- The degree-zero row object of the discarded stage vanishes with the whole row.
      simpa [S, truncated_stage_zero_column_shortComplex] using
        truncated_row_object_isZero_of_lt A t q hqt 0
    have h₃ : IsZero S.X₃ := by
      -- The degree-one row object of the discarded stage also vanishes.
      simpa [S, truncated_stage_zero_column_shortComplex] using
        truncated_row_object_isZero_of_lt A t q hqt 1
    let e₁₂ : S.X₁ ≅ S.X₂ := h₁.iso h₂
    have hf : S.f = e₁₂.hom := by
      -- Any map out of the zero source is forced to be the canonical isomorphism.
      exact h₁.eq_of_src _ _
    haveI : IsIso S.f := by
      rw [hf]
      infer_instance
    have hshort : S.ShortExact :=
      (ShortComplex.Splitting.ofIsIsoOfIsZero S inferInstance h₃).shortExact
    -- A split short exact sequence is exact at the middle term.
    exact hshort.exact

/-- Helper for Lemma 12.26.1: the stage zero-column cycles map is an isomorphism in every
vertical degree. -/
private theorem truncated_zero_column_cycles_isIso
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) [Mono ι]
    (hExact₀ : (ShortComplex.mk ι (A.d 0 1) hι).Exact)
    (t q : ℤ) :
    IsIso
      (doubleComplexZeroColumnCyclesMap
        (coaugmentedToZeroColumn
          (lower_stupid_truncation_sequence A t)
          (lower_stupid_truncation_coaugmentation A ι t))
        (coaugmentedToZeroColumn_comp_d
          (lower_stupid_truncation_sequence A t)
          (lower_stupid_truncation_coaugmentation A ι t)
          (lower_stupid_truncation_coaugmentation_comp_d A ι hι t))
        q) := by
  by_cases htq : t ≤ q
  · -- The retained branch is the already-transported cycles comparison.
    exact truncated_zero_column_cycles_isIso_of_ge A ι hι hExact₀ t q htq
  · -- In discarded degrees, the stage short complex is split by zero objects.
    simpa [doubleComplexZeroColumnCyclesMap, doubleComplexZeroRowCyclesMap,
      truncated_stage_zero_column_shortComplex] using
      (shortComplex_toCycles_isIso_of_exact_of_mono
        (truncated_stage_zero_column_shortComplex A ι hι t q)
        (truncated_stage_zero_column_exact A ι hι hExact₀ t q))

/-- Helper for Lemma 12.26.1: every rowwise lower-truncated stage has finite antidiagonal
support. -/
private theorem lower_stupid_truncation_bicomplex_hasFiniteAntidiagonalSupport
    (A : AbCochainComplexSequence) (t : ℤ) :
    doubleComplexHasFiniteAntidiagonalSupport
      (coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)) := by
  intro n
  let B := coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)
  have hsubset :
      {p : ℤ | ¬ IsZero ((B.X p).X (n - p))} ⊆ Set.Icc 0 (n - t) := by
    intro p hp
    constructor
    · by_contra hpneg
      have hrow : IsZero (B.X p) := by
        -- Negative outer degrees are absent from the extension along `embeddingUpNat`.
        exact (lower_stupid_truncation_sequence A t).isZero_extend_X embeddingUpNat p
          (fun j hj ↦ by
            have hnonneg : (0 : ℤ) ≤ (ComplexShape.embeddingUpNat.f j : ℤ) := by
              simp [ComplexShape.embeddingUpNat]
            rw [hj] at hnonneg
            omega)
      have hterm : IsZero ((B.X p).X (n - p)) := by
        -- Evaluating a zero row at degree `n - p` still gives a zero object.
        exact (HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - p)).map_isZero hrow
      exact hp hterm
    · by_contra hple
      have hp0 : 0 ≤ p := by omega
      let e : B.X p ≅ (lower_stupid_truncation_sequence A t).X (Int.toNat p) := by
        -- In nonnegative outer degree `p`, the extension row is the original row `p.toNat`.
        simpa [B, coaugmentedColumnBicomplex, Int.toNat_of_nonneg hp0] using
          (coaugmentedColumnBicomplexXIso (lower_stupid_truncation_sequence A t) (Int.toNat p))
      have hqt : n - p < t := by
        omega
      have hrowterm :
          IsZero (((lower_stupid_truncation_sequence A t).X (Int.toNat p)).X (n - p)) := by
        -- Once the vertical degree drops below `t`, the rowwise lower truncation kills it.
        exact lower_stupid_truncation_sequence_isZero_X_of_lt A t (Int.toNat p) hqt
      have hterm : IsZero ((B.X p).X (n - p)) := by
        -- Transport the discarded-row vanishing back across the owner-level row identification.
        exact ((HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - p)).mapIso e).isZero_iff.mpr
          hrowterm
      exact hp hterm
  -- The only possible nonzero summands occur for `0 ≤ p ≤ n - t`.
  exact (Set.finite_Icc 0 (n - t)).subset hsubset

/-- Helper for Lemma 12.26.1: every cutoff stage map is a quasi-isomorphism by direct
application of Lemma `12.25.4` to the truncated bicomplex. -/
private theorem lower_stupid_truncation_to_total_quasiIso
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) [Mono ι]
    (hExact₀ : (ShortComplex.mk ι (A.d 0 1) hι).Exact)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
    (t : ℤ) :
    QuasiIso (lower_stupid_truncation_to_total A ι hι t) := by
  let B := coaugmentedColumnBicomplex (lower_stupid_truncation_sequence A t)
  let α :=
    coaugmentedToZeroColumn
      (lower_stupid_truncation_sequence A t)
      (lower_stupid_truncation_coaugmentation A ι t)
  let hαcycles :=
    coaugmentedToZeroColumn_comp_d
      (lower_stupid_truncation_sequence A t)
      (lower_stupid_truncation_coaugmentation A ι t)
      (lower_stupid_truncation_coaugmentation_comp_d A ι hι t)
  -- Apply Lemma `12.25.4` directly to the truncated bicomplex after packaging its three
  -- hypotheses: finite antidiagonal support, vanishing in negative columns, and row exactness.
  let hvanish : ∀ p q : ℤ, p < 0 → IsZero ((B.X p).X q) := by
    intro p q hp
    have hrow : IsZero (B.X p) := by
      exact (lower_stupid_truncation_sequence A t).isZero_extend_X embeddingUpNat p
        (fun j hj ↦ by
          have hnonneg : (0 : ℤ) ≤ (ComplexShape.embeddingUpNat.f j : ℤ) := by
            simp [ComplexShape.embeddingUpNat]
          rw [hj] at hnonneg
          omega)
    exact (HomologicalComplex.eval AddCommGrpCat (up ℤ) q).map_isZero hrow
  let hexact : ∀ p q : ℤ, 0 < p → (B.flip.X q).ExactAt p := by
    intro p q hp
    exact truncated_row_exactAt A hExact t q p hp
  let hαiso :
      ∀ q : ℤ, IsIso (doubleComplexZeroColumnCyclesMap α hαcycles q) := by
    intro q
    exact truncated_zero_column_cycles_isIso A ι hι hExact₀ t q
  -- The stage total map is exactly the zero-column comparison for the truncated bicomplex.
  simpa [lower_stupid_truncation_to_total, B, α, hαcycles] using
    (zeroColumnToTotal_quasiIso_of_exact_rows_and_cycles
      (A := B)
      (K := M.stupidTrunc (ComplexShape.embeddingUpIntGE t))
      (hfin := lower_stupid_truncation_bicomplex_hasFiniteAntidiagonalSupport A t)
      hvanish
      hexact
      α
      hαcycles
      hαiso)

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
@[stacks 0E1Q]
theorem coaugmentedToTotal_quasiIso_of_exact_complex_of_complexes
    {M : AbCochainComplex}
    (A : AbCochainComplexSequence) (ι : M ⟶ A.X 0)
    (hι : ι ≫ A.d 0 1 = 0) [Mono ι]
    (hExact₀ : (ShortComplex.mk ι (A.d 0 1) hι).Exact)
    (hExact : ∀ n : ℕ, A.ExactAt (n + 1)) :
    QuasiIso (coaugmentedToTotal A ι hι) :=
  -- Route correction: keep the textbook cutoff argument. The new truncation inclusion above
  -- isolates the stage objects `σ_{\ge t}A_p^\bullet`, the stage coaugmentation
  -- `σ_{\ge t}M^\bullet ⟶ σ_{\ge t}A_0^\bullet`, and the canonical stage total map
  -- `lower_stupid_truncation_to_total`. The remaining work is the genuinely structural part:
  -- prove the stage quasi-isomorphism via Lemma `12.25.4`, then descend surjectivity and
  -- injectivity on homology from finite-support cocycle and boundary lifts in the coproduct
  -- total.
  -- TODO: prove that each stage map `lower_stupid_truncation_to_total A ι hι t` is a
  -- quasi-isomorphism by checking the row exactness and zero-column cycle hypotheses for
  -- `lower_stupid_truncation_sequence A t`, and then compare those stage maps with
  -- `coaugmentedToTotal A ι hι` using finite-support representatives in `Tot`.
  sorry
