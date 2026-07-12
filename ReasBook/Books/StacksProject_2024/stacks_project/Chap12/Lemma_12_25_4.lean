import Mathlib
import StacksProject_2024.Chap12.Definition_12_18_3
import StacksProject_2024.Chap12.Lemma_12_24_4
import StacksProject_2024.Chap12.Lemma_12_25_1
import StacksProject_2024.Chap12.Lemma_12_25_3

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

/-- Totalization is available on the flipped bicomplex whenever it is available on the original
bicomplex. -/
private instance flipHasTotal
    (A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [A.HasTotal (up ℤ)] :
    A.flip.HasTotal (up ℤ) := by
  infer_instance

/-- The degree-`n` component of the canonical map `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})`
attached to a morphism `α : K^\bullet ⟶ A^{\bullet,0}`. -/
noncomputable def doubleComplexZeroRowToTotalComponent
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A) (n : ℤ) :
    K.X n ⟶ (Tot(A)).X n :=
  α.f n ≫ A.ιTotal (up ℤ) n 0 n (Int.add_zero n)

/-- Composing the row-zero component with the total differential expands into the horizontal and
vertical contributions on the `(n, 0)` summand. -/
private theorem doubleComplexZeroRowToTotal_total_d_on_zero_summand
    {K : CochainComplex 𝒜 ℤ} {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (n n' : ℤ) (hrel : (up ℤ).Rel n n') (hn' : n + 1 = n') :
    doubleComplexZeroRowToTotalComponent α n ≫ (Tot(A)).d n n' =
      α.f n ≫ ((A.d n n').f 0 ≫ A.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
        α.f n ≫ (n.negOnePow • ((A.X n).d 0 1 ≫ A.ιTotal (up ℤ) n 1 n' hn')) := by
  sorry

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
  sorry

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
  sorry

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
theorem zeroRowToTotal_quasiIso_of_exact_columns_and_cycles
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport A)
    (hvanish : ∀ p q : ℤ, q < 0 → IsZero ((A.X p).X q))
    (hexact : ∀ p q : ℤ, 0 < q → (A.X p).ExactAt q)
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (hαiso : ∀ p : ℤ, IsIso (doubleComplexZeroRowCyclesMap α hαcycles p)) :
    QuasiIso (doubleComplexZeroRowToTotal α hαcycles) := by
  sorry

-- Proof sketch: apply the previous theorem to the flipped bicomplex. The hypotheses become the
-- zero-row hypotheses for `A.flip`, and `A.totalFlipIso (up ℤ)` transports the resulting
-- quasi-isomorphism back to `Tot(A)`.
/-- Lemma 12.25.4 (moreover): if `A^{p,q}` vanishes for `p < 0`, every row `A^{\bullet,q}` is
exact in every positive degree `p > 0`, and a morphism `α : K^\bullet ⟶ A^{0,\bullet}`
identifies each `K^q` with the cycles `\ker(d_1^{0,q})`, then under finite antidiagonal support
the induced comparison map `K^\bullet ⟶ \mathrm{Tot}(A^{\bullet,\bullet})` is a
quasi-isomorphism. -/
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
  sorry

end

end
