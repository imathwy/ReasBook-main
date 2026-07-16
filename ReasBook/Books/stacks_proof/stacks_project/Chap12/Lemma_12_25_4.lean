import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_18_3
import stacks_proof.stacks_project.Chap12.Lemma_12_24_4
import stacks_proof.stacks_project.Chap12.Lemma_12_25_1
import stacks_proof.stacks_project.Chap12.Lemma_12_25_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂
open scoped HomologicalComplex₂

noncomputable section

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]

local notation "ev₀" => HomologicalComplex.eval 𝒜 (up ℤ) (0 : ℤ)

/- Domain-style sampling for Lemma 12.25.4:
- primary domain: cohomological double complexes, their total complexes, and quasi-isomorphism
  criteria detected on one filtration line;
- sampled owner declarations:
  `HomologicalComplex₂.total`,
  `HomologicalComplex₂.totalFlipIso`,
  `HomologicalComplex₂.flip`,
  `HomologicalComplex.ExactAt`,
  `doubleComplexHasFiniteAntidiagonalSupport`,
  `QuasiIso`;
- best owner abstraction: the canonical comparison morphisms from the zero row or zero column into
  the owner total complex `Tot(A)`;
- primitive data: a morphism into the zero row `A^{•,0}` or zero column `A^{0,•}`, together with
  the corresponding cycle condition on its components;
- derived API: the induced maps to the column or row cycles and the resulting `QuasiIso`
  criterion under finite antidiagonal support and exactness off the chosen axis;
- source/core/bridge triage:
  `source-facing`: the comparison maps from the zero row or zero column into
    `Tot(A^{•,•})` and the two quasi-isomorphism theorems;
  `core/canonical`: `Tot(_)`, `HomologicalComplex.ExactAt`, `QuasiIso`, and
    `doubleComplexHasFiniteAntidiagonalSupport`, together with the flip symmetry of totalization;
  `bridge/view`: `HomologicalComplex₂.zeroColumnIsoZeroRowFlip`,
    `doubleComplexZeroRowCyclesMap`, and `doubleComplexZeroColumnCyclesMap`, which record the
    identifications of `K^p` or `K^q` with the corresponding cycles on the chosen axis.

The public theorems below should therefore be stated directly in terms of these owners. In each
orientation, exactness on the negative side is derived from the vanishing hypothesis, so the
nontrivial primitive exactness input is only the positive-degree part away from the chosen axis.
-/

namespace HomologicalComplex₂

/-- The zeroth column `A^{0,\bullet}` is canonically the zeroth row of the flipped bicomplex
`(A.flip)^{\bullet,0}`. -/
noncomputable def zeroColumnIsoZeroRowFlip
    (A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) :
    A.X 0 ≅ ((ev₀).mapHomologicalComplex (up ℤ)).obj A.flip :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ Iso.refl _)
    (fun p q hpq ↦ by
      have h : p + 1 = q := by
        simpa [ComplexShape.up, ComplexShape.up'] using hpq
      subst h
      simp)

end HomologicalComplex₂

/-- The degree-`n` component of the canonical map `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})`
attached to a morphism `α : K^\bullet ⟶ A^{\bullet,0}`. -/
noncomputable def doubleComplexZeroRowToTotalComponent
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A) (n : ℤ) :
    K.X n ⟶ (Tot(A)).X n :=
  α.f n ≫ A.ιTotal (up ℤ) n 0 n (Int.add_zero n)

-- Proof sketch: expand the total differential as the sum of its horizontal and vertical parts.
-- The horizontal part is the row differential and is handled by the cochain-map condition on `α`;
-- the vertical part vanishes because each `α^p` lands in the cycles of the `p`-th column.
/-- The row-zero comparison components define a morphism of cochain complexes into the total
complex. -/
theorem doubleComplexZeroRowToTotal_comm
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (n n' : ℤ) (_ : (up ℤ).Rel n n') :
    doubleComplexZeroRowToTotalComponent α n ≫ (Tot(A)).d n n' =
      K.d n n' ≫ doubleComplexZeroRowToTotalComponent α n' := by
  have hrel : (up ℤ).Rel n n' := by assumption
  have hrel01 : (up ℤ).Rel (0 : ℤ) 1 := by
    simp [ComplexShape.up, ComplexShape.up']
  have hn' : n + 1 = n' := by
    simpa [ComplexShape.up, ComplexShape.up'] using hrel
  -- Expand the total differential into its horizontal and vertical parts.
  calc
    doubleComplexZeroRowToTotalComponent α n ≫ (Tot(A)).d n n' =
        α.f n ≫ (A.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫
          (A.D₁ (up ℤ) n n' + A.D₂ (up ℤ) n n')) := by
      rfl
    _ =
        α.f n ≫ A.d₁ (up ℤ) n 0 n' + α.f n ≫ A.d₂ (up ℤ) n 0 n' := by
      rw [Preadditive.comp_add, Category.assoc, Category.assoc,
        HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
    _ =
        α.f n ≫ ((A.d n n').f 0 ≫ A.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
          α.f n ≫ (n.negOnePow •
            ((A.X n).d 0 1 ≫ A.ιTotal (up ℤ) n 1 n' hn')) := by
      rw [A.d₁_eq hrel 0 n' (Int.add_zero n'), A.d₂_eq n hrel01 n' hn']
      simp [ComplexShape.ε_up_ℤ]
    _ =
        α.f n ≫ ((A.d n n').f 0 ≫ A.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) := by
      rw [Linear.comp_units_smul, hαcycles n, zero_comp, smul_zero, add_zero]
    _ =
        K.d n n' ≫ α.f n' ≫ A.ιTotal (up ℤ) n' 0 n' (Int.add_zero n') := by
      rw [← Category.assoc, α.comm n n' hrel]
    _ = K.d n n' ≫ doubleComplexZeroRowToTotalComponent α n' := by
      rfl

/-- The canonical morphism `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})` induced by a morphism
`α : K^\bullet ⟶ A^{\bullet,0}` whose components land in the cycles of the columns. -/
noncomputable def doubleComplexZeroRowToTotal
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0) :
    K ⟶ Tot(A) where
  f := doubleComplexZeroRowToTotalComponent α
  comm' := doubleComplexZeroRowToTotal_comm α hαcycles

/-- The canonical morphism from the zeroth column into the zeroth row of the flipped bicomplex. -/
noncomputable def doubleComplexZeroColumnToZeroRowFlip
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ A.X 0) :
    K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A.flip :=
  α ≫ (A.zeroColumnIsoZeroRowFlip).hom

/-- The zero-column cycle condition is exactly the row-zero cycle condition on the flipped
bicomplex. -/
theorem doubleComplexZeroColumnToZeroRowFlip_comp_d
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0) :
    ∀ q : ℤ, (doubleComplexZeroColumnToZeroRowFlip α).f q ≫ (A.flip.X q).d 0 1 = 0 := by
  intro q
  -- The zero-column/zero-row identification is componentwise the identity, so the cycle
  -- condition transports directly to the flipped bicomplex.
  simpa [doubleComplexZeroColumnToZeroRowFlip, HomologicalComplex₂.zeroColumnIsoZeroRowFlip] using
    hαcycles q

/-- The canonical morphism `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})` induced by a morphism
`α : K^\bullet ⟶ A^{0,\bullet}` whose components land in the cycles of the rows. -/
noncomputable def doubleComplexZeroColumnToTotal
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0) :
    K ⟶ Tot(A) :=
  doubleComplexZeroRowToTotal
      (doubleComplexZeroColumnToZeroRowFlip α)
      (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) ≫
    (A.totalFlipIso (up ℤ)).hom

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [Abelian 𝒜] [CategoryWithHomology 𝒜]

local notation "ev₀" => HomologicalComplex.eval 𝒜 (up ℤ) (0 : ℤ)
local notation "singleRow₀" => CochainComplex.singleFunctor 𝒜 (0 : ℤ)

/-- The morphism from `K^p` to the cycles `\ker(d_2^{p,0})` induced by the component
`α^p : K^p ⟶ A^{p,0}`. -/
noncomputable def doubleComplexZeroRowCyclesMap
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0) (p : ℤ) :
    K.X p ⟶ (A.X p).cycles 0 :=
  (A.X p).liftCycles' (α.f p) 1 rfl (hαcycles p)

/-- The morphism from `K^q` to the cycles `\ker(d_1^{0,q})` induced by the component
`α^q : K^q ⟶ A^{0,q}`. -/
noncomputable def doubleComplexZeroColumnCyclesMap
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0) (q : ℤ) :
    K.X q ⟶ (A.flip.X q).cycles 0 :=
  doubleComplexZeroRowCyclesMap
      (doubleComplexZeroColumnToZeroRowFlip α)
      (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) q

/-- Helper for Lemma 12.25.4: exactness of the `p`-th column in positive degree forces the
corresponding first-page term to vanish. -/
private theorem column_homology_isZero_of_exact
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (hexact : ∀ p q : ℤ, 0 < q → (A.X p).ExactAt q)
    (p q : ℤ) (hq : 0 < q) :
    IsZero ((A.X p).homology q) := by
  -- Convert the exactness hypothesis into the homology-vanishing form used on the `E₁` page.
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact hexact p q hq

/-- Helper for Lemma 12.25.4: if the `q`-th object of the `p`-th column already vanishes, then
its homology at degree `q` vanishes as well. -/
private theorem column_homology_isZero_of_vanish
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (hvanish : ∀ p q : ℤ, q < 0 → IsZero ((A.X p).X q))
    (p q : ℤ) (hq : q < 0) :
    IsZero ((A.X p).homology q) := by
  -- The middle object of the defining short complex is already zero, so its homology vanishes.
  have hX : IsZero ((A.X p).X q) := hvanish p q hq
  simpa [HomologicalComplex.homology] using
    (ShortComplex.isZero_homology_of_isZero_X₂ ((A.X p).sc' (q - 1) q (q + 1)) hX)

/-- Helper for Lemma 12.25.4: under the column hypotheses, the first-page term of `A` is
concentrated on the row `q = 0`. -/
private theorem firstDoubleComplexPageOne_isZero_of_ne_zero
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (hvanish : ∀ p q : ℤ, q < 0 → IsZero ((A.X p).X q))
    (hexact : ∀ p q : ℤ, 0 < q → (A.X p).ExactAt q)
    (p q : ℤ) (hq : q ≠ 0) :
    IsZero (firstDoubleComplexPageOne A p q) := by
  -- Route correction: compute the textbook `E₁` term as column homology first, then split by the
  -- sign of `q` instead of unfolding the associated spectral sequence directly.
  rw [firstDoubleComplexPageOne_def]
  by_cases hq_pos : 0 < q
  · exact column_homology_isZero_of_exact hexact p q hq_pos
  · have hq_neg : q < 0 := lt_of_le_of_ne (le_of_not_gt hq_pos) hq
    exact column_homology_isZero_of_vanish hvanish p q hq_neg

/-- Helper for Lemma 12.25.4: the double complex obtained by placing `K` on the row `q = 0`
and zero objects on every other row. -/
noncomputable def zeroRowBicomplex (K : CochainComplex 𝒜 ℤ) :
    HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ) :=
  (singleRow₀.mapHomologicalComplex (up ℤ)).obj K

/-- Helper for Lemma 12.25.4: evaluating the zero-row bicomplex on the row `q = 0` recovers the
original complex `K`. -/
noncomputable def zeroRowBicomplexRowIso (K : CochainComplex 𝒜 ℤ) :
    ((ev₀).mapHomologicalComplex (up ℤ)).obj (zeroRowBicomplex K) ≅ K :=
  singleObjXSelf (up ℤ) (0 : ℤ) K

/-- Helper for Lemma 12.25.4: every nonzero row of the degenerate source bicomplex is zero. -/
theorem isZero_zeroRowBicomplex_X
    (K : CochainComplex 𝒜 ℤ) (p q : ℤ) (hq : q ≠ 0) :
    IsZero (((zeroRowBicomplex K).X p).X q) := by
  -- Each vertical complex is a single complex concentrated in degree `0`.
  simpa [zeroRowBicomplex] using
    (HomologicalComplex.isZero_single_obj_X (up ℤ) (0 : ℤ) (K.X p) q hq)

/-- Helper for Lemma 12.25.4: the row-zero source bicomplex has finite antidiagonal support,
because on total degree `n` only the summand with `p = n` can lie on the row `q = 0`. -/
private theorem zeroRowBicomplex_hasFiniteAntidiagonalSupport
    (K : CochainComplex 𝒜 ℤ) :
    doubleComplexHasFiniteAntidiagonalSupport (zeroRowBicomplex K) := by
  intro n
  refine (Set.finite_singleton n).subset ?_
  intro p hp
  rw [Set.mem_singleton_iff]
  by_contra hpn
  exact hp (isZero_zeroRowBicomplex_X K p (n - p) (by omega))

/-- Helper for Lemma 12.25.4: the `p`-th column of the row-zero bicomplex maps into the `p`-th
column of `A` via the component `α^p`. -/
private noncomputable def zeroRowBicomplexMapComponent
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (p : ℤ) :
    (zeroRowBicomplex K).X p ⟶ A.X p :=
  HomologicalComplex.mkHomFromSingle
    (α.f p)
    (fun q hq ↦ by
      -- Any outgoing differential from degree `0` in the cohomological shape lands in degree `1`.
      have hq' : q = 1 := by
        simpa [ComplexShape.up, ComplexShape.up'] using hq
      subst hq'
      simpa using hαcycles p)

/-- Helper for Lemma 12.25.4: the column maps defined by `α` commute with the horizontal
differentials, so they assemble to a bicomplex morphism. -/
private theorem zeroRowBicomplexMapComponent_comm
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (p p' : ℤ) (hpp' : (up ℤ).Rel p p') :
    zeroRowBicomplexMapComponent α hαcycles p ≫ A.d p p' =
      (zeroRowBicomplex K).d p p' ≫ zeroRowBicomplexMapComponent α hαcycles p' := by
  -- Maps out of a single complex are determined by their degree-`0` component.
  apply HomologicalComplex.from_single_hom_ext
  simpa [zeroRowBicomplex, zeroRowBicomplexMapComponent, Category.assoc] using α.comm p p' hpp'

/-- Helper for Lemma 12.25.4: the cycle-compatible row-zero data `α` defines a bicomplex map from
the degenerate source bicomplex into `A`. -/
noncomputable def zeroRowBicomplexMap
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0) :
    zeroRowBicomplex K ⟶ A where
  f := zeroRowBicomplexMapComponent α hαcycles
  comm' := zeroRowBicomplexMapComponent_comm α hαcycles

/-- Helper for Lemma 12.25.4: evaluating `zeroRowBicomplexMap α` on the row `q = 0` recovers the
original map `α` after identifying that row with `K`. -/
theorem zeroRowBicomplexMap_row_zero
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0) :
    ((ev₀).mapHomologicalComplex (up ℤ)).map (zeroRowBicomplexMap α hαcycles) =
      (zeroRowBicomplexRowIso K).hom ≫ α := by
  -- The degree-`0` component of `mkHomFromSingle` is the prescribed `α^p`.
  ext p
  simp [zeroRowBicomplexMap, zeroRowBicomplexMapComponent, zeroRowBicomplexRowIso,
    Category.assoc]

/-- Helper for Lemma 12.25.4: on the source row-zero bicomplex, the `E₁` term on the row
`q = 0` is canonically `K^p`. -/
noncomputable def zeroRowBicomplex_pageOne_zero_iso
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    firstDoubleComplexPageOne (zeroRowBicomplex K) p 0 ≅ K.X p := by
  -- This is the standard homology computation for a complex concentrated in degree `0`.
  simpa [zeroRowBicomplex, firstDoubleComplexPageOne] using
    (HomologicalComplex.singleObjHomologySelfIso (up ℤ) (0 : ℤ) (K.X p))

/-- Helper for Lemma 12.25.4: the source `E₁` page of the row-zero bicomplex vanishes away from
the row `q = 0`. -/
private theorem zeroRowBicomplex_pageOne_isZero_of_ne_zero
    (K : CochainComplex 𝒜 ℤ) (p q : ℤ) (hq : q ≠ 0) :
    IsZero (firstDoubleComplexPageOne (zeroRowBicomplex K) p q) := by
  -- The middle object of the source column is zero in every nonzero degree.
  rw [firstDoubleComplexPageOne_def]
  have hX : IsZero (((zeroRowBicomplex K).X p).X q) := isZero_zeroRowBicomplex_X K p q hq
  simpa [HomologicalComplex.homology] using
    (ShortComplex.isZero_homology_of_isZero_X₂ (((zeroRowBicomplex K).X p).sc' (q - 1) q (q + 1))
      hX)

/-- Helper for Lemma 12.25.4: postcomposing the row-zero data with a bicomplex morphism again
lands in column cycles. -/
private theorem doubleComplexZeroRow_comp_map_cycles
    {K : CochainComplex 𝒜 ℤ}
    {A B : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (β : A ⟶ B) :
    ∀ p : ℤ,
      (α ≫ ((ev₀).mapHomologicalComplex (up ℤ)).map β).f p ≫ (B.X p).d 0 1 = 0 := by
  intro p
  -- Move the vertical differential across the column map `β.f p`.
  calc
    (α ≫ ((ev₀).mapHomologicalComplex (up ℤ)).map β).f p ≫ (B.X p).d 0 1 =
        α.f p ≫ (β.f p).f 0 ≫ (B.X p).d 0 1 := by
      rfl
    _ = α.f p ≫ (A.X p).d 0 1 ≫ (β.f p).f 1 := by
      rw [Category.assoc, (β.f p).comm 0 1 (by simp)]
    _ = 0 := by
      rw [hαcycles p, zero_comp]

/-- Helper for Lemma 12.25.4: the row-zero comparison map is functorial in the target bicomplex,
with comparison morphism `total.map β`. -/
theorem doubleComplexZeroRowToTotal_comp_map
    {K : CochainComplex 𝒜 ℤ}
    {A B : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (β : A ⟶ B) :
    doubleComplexZeroRowToTotal
        (α ≫ ((ev₀).mapHomologicalComplex (up ℤ)).map β)
        (doubleComplexZeroRow_comp_map_cycles α hαcycles β) =
      doubleComplexZeroRowToTotal α hαcycles ≫ total.map β (up ℤ) := by
  ext n
  -- Both maps are the same inclusion of the `(n,0)` summand followed by `β`.
  simp [doubleComplexZeroRowToTotal, doubleComplexZeroRowToTotalComponent, Category.assoc]

-- Proof sketch: apply the second spectral sequence of the double complex. The hypotheses imply
-- that the `E₁`-page is concentrated on the row `q = 0`, where it identifies with `K^\bullet`
-- via the maps to cycles. The vanishing hypothesis makes the negative rows automatically exact,
-- so only positive vertical degrees need to be assumed exact. Finite antidiagonal support gives
-- convergence to
-- `H^\ast(\mathrm{Tot}(A^{\bullet,\bullet}))`, so the induced map from `K^\bullet` to the total
-- complex is a quasi-isomorphism.
/-- Lemma 12.25.4: if `A^{p,q}` vanishes for `q < 0`, every column `A^{p,\bullet}` is exact in
every positive degree `q > 0`, and a morphism `α : K^\bullet ⟶ A^{\bullet,0}` identifies each
`K^p` with the cycles `\ker(d_2^{p,0})`, then under finite antidiagonal support the induced
comparison map `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})` is a quasi-isomorphism. -/
@[stacks 0133]
theorem zeroRowToTotal_quasiIso_of_exact_columns_and_cycles
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport A)
    (hvanish : ∀ p q : ℤ, q < 0 → IsZero ((A.X p).X q))
    (hexact : ∀ p q : ℤ, 0 < q → (A.X p).ExactAt q)
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (hαiso : ∀ p : ℤ, IsIso (doubleComplexZeroRowCyclesMap α hαcycles p)) :
    -- Route correction: the source bicomplex and total-map functoriality are now explicit via
    -- `zeroRowBicomplex`, `zeroRowBicomplexRowIso`, and
    -- `doubleComplexZeroRowToTotal_comp_map`. The remaining work is the genuine spectral-sequence
    -- bridge: build the filtered-complex morphism induced by the bicomplex map
    -- `zeroRowBicomplex K ⟶ A`, identify its `E₁` map with `doubleComplexZeroRowCyclesMap`, and
    -- conclude by convergence.
    QuasiIso (doubleComplexZeroRowToTotal α hαcycles) := by
  let β : zeroRowBicomplex K ⟶ A := zeroRowBicomplexMap α hαcycles
  have hβrow :
      ((ev₀).mapHomologicalComplex (up ℤ)).map β =
        (zeroRowBicomplexRowIso K).hom ≫ α :=
    zeroRowBicomplexMap_row_zero α hαcycles
  have hsrc_zero : ∀ p : ℤ, firstDoubleComplexPageOne (zeroRowBicomplex K) p 0 ≅ K.X p := by
    intro p
    exact zeroRowBicomplex_pageOne_zero_iso K p
  have hsrc_off : ∀ p q : ℤ, q ≠ 0 →
      IsZero (firstDoubleComplexPageOne (zeroRowBicomplex K) p q) := by
    intro p q hq
    exact zeroRowBicomplex_pageOne_isZero_of_ne_zero K p q hq
  have htgt_off : ∀ p q : ℤ, q ≠ 0 → IsZero (firstDoubleComplexPageOne A p q) := by
    intro p q hq
    exact firstDoubleComplexPageOne_isZero_of_ne_zero hvanish hexact p q hq
  have hsrc_fin : doubleComplexHasFiniteAntidiagonalSupport (zeroRowBicomplex K) :=
    zeroRowBicomplex_hasFiniteAntidiagonalSupport K
  -- TODO: choose associated spectral sequences for the first filtrations on
  -- `Tot(zeroRowBicomplex K)` and `Tot(A)`, using the owner-level filtered map induced by `β`.
  -- Then compute the induced `E₁` map via `associatedSpectralSequenceMap_commSq`, identify its
  -- row `q = 0` part with `doubleComplexZeroRowCyclesMap α hαcycles`, and apply convergence for
  -- `hsrc_fin` and `hfin` to conclude that `total.map β` and hence
  -- `doubleComplexZeroRowToTotal α hαcycles` is a quasi-isomorphism.
  sorry

private theorem doubleComplexHasFiniteAntidiagonalSupport_flip
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (hfin : doubleComplexHasFiniteAntidiagonalSupport A) :
    doubleComplexHasFiniteAntidiagonalSupport A.flip := by
  intro n
  -- Swapping the two indices preserves the antidiagonal `p + q = n`; use the involution
  -- `p ↦ n - p` to transport the finite support set.
  simpa [CategoryTheory.doubleComplexHasFiniteAntidiagonalSupport] using
    (hfin n).preimage (fun p : ℤ ↦ n - p) (by
      intro p q hpq
      linarith)

-- Proof sketch: apply the previous theorem to the flipped bicomplex. The hypotheses become the
-- zero-row hypotheses for `A.flip`, and `A.totalFlipIso (up ℤ)` transports the resulting
-- quasi-isomorphism back to `Tot(A)`.
/-- Lemma 12.25.4 (moreover): if `A^{p,q}` vanishes for `p < 0`, every row `A^{\bullet,q}` is
exact in every positive degree `p > 0`, and a morphism `α : K^\bullet ⟶ A^{0,\bullet}`
identifies each `K^q` with the cycles `\ker(d_1^{0,q})`, then under finite antidiagonal support
the induced comparison map `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})` is a
quasi-isomorphism. -/
@[stacks 0133]
theorem zeroColumnToTotal_quasiIso_of_exact_rows_and_cycles
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport A)
    (hvanish : ∀ p q : ℤ, p < 0 → IsZero ((A.X p).X q))
    (hexact : ∀ p q : ℤ, 0 < p → (A.flip.X q).ExactAt p)
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0)
    (hαiso : ∀ q : ℤ, IsIso (doubleComplexZeroColumnCyclesMap α hαcycles q)) :
    QuasiIso (doubleComplexZeroColumnToTotal α hαcycles) := by
  let α' := doubleComplexZeroColumnToZeroRowFlip α
  let hα'cycles := doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles
  have hvanishFlip : ∀ p q : ℤ, q < 0 → IsZero ((A.flip.X p).X q) := by
    intro p q hq
    simpa using hvanish q p hq
  have hexactFlip : ∀ p q : ℤ, 0 < q → (A.flip.X p).ExactAt q := by
    intro p q hq
    simpa using hexact q p hq
  have hα'iso : ∀ p : ℤ, IsIso (doubleComplexZeroRowCyclesMap α' hα'cycles p) := by
    intro p
    simpa [doubleComplexZeroColumnCyclesMap, α', hα'cycles] using hαiso p
  letI : QuasiIso (doubleComplexZeroRowToTotal α' hα'cycles) :=
    zeroRowToTotal_quasiIso_of_exact_columns_and_cycles
      (doubleComplexHasFiniteAntidiagonalSupport_flip hfin)
      hvanishFlip hexactFlip α' hα'cycles hα'iso
  simpa [doubleComplexZeroColumnToTotal, α', hα'cycles] using
    (inferInstance : QuasiIso (doubleComplexZeroRowToTotal α' hα'cycles ≫
      (A.totalFlipIso (up ℤ)).hom))

end

end
