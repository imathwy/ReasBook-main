import Mathlib
import StacksProject_2024.Chap12.Definition_12_18_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomologicalComplex HomologicalComplex₂
open scoped HomologicalComplex₂

universe v u

noncomputable section

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [CategoryTheory.Limits.HasZeroObject 𝒜]

local notation "ev₀" => HomologicalComplex.eval 𝒜 (up ℤ) (0 : ℤ)
local notation "single₀" => CochainComplex.singleFunctor (CochainComplex 𝒜 ℤ) (0 : ℤ)

namespace HomologicalComplex₂

/-- Helper for Lemma 12.25.5: the zeroth column of a bicomplex is canonically the zeroth row of
its flip. -/
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

/-- Helper for Lemma 12.25.5: totalization is available on the flipped bicomplex whenever it is
available on the original bicomplex. -/
private instance flipHasTotal
    (A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [A.HasTotal (up ℤ)] :
    ((flipFunctor 𝒜 (up ℤ) (up ℤ)).obj A).HasTotal (up ℤ) := by
  change A.flip.HasTotal (up ℤ)
  infer_instance

/-- Helper for Lemma 12.25.5: the degree-`n` component of the canonical map from the zeroth row
into the total complex. -/
private noncomputable def doubleComplexZeroRowToTotalComponent
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A) (n : ℤ) :
    K.X n ⟶ (Tot(A)).X n :=
  α.f n ≫ A.ιTotal (up ℤ) n 0 n (Int.add_zero n)

/-- Helper for Lemma 12.25.5: composing the row-zero component with the total differential expands
into the horizontal and vertical contributions on the `(n,0)` summand. -/
private theorem doubleComplexZeroRowToTotal_total_d_on_zero_summand
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (n n' : ℤ) (hrel : (up ℤ).Rel n n') (hn' : n + 1 = n') :
    doubleComplexZeroRowToTotalComponent α n ≫ (Tot(A)).d n n' =
      α.f n ≫ ((A.d n n').f 0 ≫ A.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
        α.f n ≫ (n.negOnePow • ((A.X n).d 0 1 ≫ A.ιTotal (up ℤ) n 1 n' hn')) := by
  have hrel01 : (up ℤ).Rel (0 : ℤ) 1 := by
    simp [ComplexShape.up, ComplexShape.up']
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
      rw [A.d₁_eq hrel 0 n' (Int.add_zero n')]
      rw [A.d₂_eq n hrel01 n' hn']
      simp [ComplexShape.ε_up_ℤ]

/-- Helper for Lemma 12.25.5: the row-zero comparison components define a chain map into the total
complex. -/
private theorem doubleComplexZeroRowToTotal_comm
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (n n' : ℤ) (_ : (up ℤ).Rel n n') :
    doubleComplexZeroRowToTotalComponent α n ≫ (Tot(A)).d n n' =
      K.d n n' ≫ doubleComplexZeroRowToTotalComponent α n' := by
  have hrel : (up ℤ).Rel n n' := by assumption
  have hn' : n + 1 = n' := by
    simpa [ComplexShape.up, ComplexShape.up'] using hrel
  calc
    doubleComplexZeroRowToTotalComponent α n ≫ (Tot(A)).d n n' =
        α.f n ≫ ((A.d n n').f 0 ≫ A.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) +
          α.f n ≫ (n.negOnePow •
            ((A.X n).d 0 1 ≫ A.ιTotal (up ℤ) n 1 n' hn')) := by
      exact doubleComplexZeroRowToTotal_total_d_on_zero_summand α n n' hrel hn'
    _ =
        α.f n ≫ ((A.d n n').f 0 ≫ A.ιTotal (up ℤ) n' 0 n' (Int.add_zero n')) := by
      have hcycles_assoc :
          α.f n ≫ ((A.X n).d 0 1 ≫ A.ιTotal (up ℤ) n 1 n' hn') = 0 := by
        rw [Category.assoc, hαcycles n, zero_comp]
      have hvertical :
          α.f n ≫
              (n.negOnePow • (((A.X n).d 0 1) ≫ A.ιTotal (up ℤ) n 1 n' hn')) = 0 := by
        rw [Linear.comp_units_smul, hcycles_assoc, smul_zero]
      rw [hvertical, add_zero]
    _ =
        K.d n n' ≫ α.f n' ≫ A.ιTotal (up ℤ) n' 0 n' (Int.add_zero n') := by
      rw [← Category.assoc, α.comm n n' hrel]
    _ = K.d n n' ≫ doubleComplexZeroRowToTotalComponent α n' := by
      rfl

/-- Helper for Lemma 12.25.5: the canonical map from the zeroth row into the total complex. -/
private noncomputable def doubleComplexZeroRowToTotal
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0) :
    K ⟶ Tot(A) where
  f := doubleComplexZeroRowToTotalComponent α
  comm' := doubleComplexZeroRowToTotal_comm α hαcycles

/-- Helper for Lemma 12.25.5: the zeroth column map becomes a zeroth-row map after flipping. -/
private noncomputable def doubleComplexZeroColumnToZeroRowFlip
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ A.X 0) :
    K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A.flip :=
  α ≫ (A.zeroColumnIsoZeroRowFlip).hom

/-- Helper for Lemma 12.25.5: the zero-column cycle condition transports to the flipped zeroth
row. -/
omit [CategoryTheory.Limits.HasZeroObject 𝒜] in
private theorem doubleComplexZeroColumnToZeroRowFlip_comp_d
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0) :
    ∀ q : ℤ, (doubleComplexZeroColumnToZeroRowFlip α).f q ≫ (A.flip.X q).d 0 1 = 0 := by
  intro q
  simpa [doubleComplexZeroColumnToZeroRowFlip, HomologicalComplex₂.zeroColumnIsoZeroRowFlip] using
    hαcycles q

/-- Helper for Lemma 12.25.5: the canonical map from the zeroth column into the total complex. -/
private noncomputable def doubleComplexZeroColumnToTotal
    {K : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0) :
    K ⟶ Tot(A) :=
  doubleComplexZeroRowToTotal
      (doubleComplexZeroColumnToZeroRowFlip α)
      (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) ≫
    (A.totalFlipIso (up ℤ)).hom

/-- Helper for Lemma 12.25.5: postcomposing row-zero data with a bicomplex map still lands in
column cycles. -/
private theorem doubleComplexZeroRow_comp_map_cycles
    {K : CochainComplex 𝒜 ℤ}
    {A B : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (α : K ⟶ ((ev₀).mapHomologicalComplex (up ℤ)).obj A)
    (hαcycles : ∀ p : ℤ, α.f p ≫ (A.X p).d 0 1 = 0)
    (β : A ⟶ B) :
    ∀ p : ℤ,
      (α ≫ ((ev₀).mapHomologicalComplex (up ℤ)).map β).f p ≫ (B.X p).d 0 1 = 0 := by
  intro p
  calc
    (α ≫ ((ev₀).mapHomologicalComplex (up ℤ)).map β).f p ≫ (B.X p).d 0 1 =
        α.f p ≫ (β.f p).f 0 ≫ (B.X p).d 0 1 := by
      simp [Category.assoc]
    _ = α.f p ≫ ((β.f p).f 0 ≫ (B.X p).d 0 1) := by
      rw [Category.assoc, (β.f p).comm 0 1 (by simp)]
    _ = α.f p ≫ (A.X p).d 0 1 ≫ (β.f p).f 1 := by
      rw [Category.assoc]
    _ = 0 := by
      rw [hαcycles p, zero_comp]

/-- Helper for Lemma 12.25.5: the row-zero comparison map is functorial in the target bicomplex. -/
private theorem doubleComplexZeroRowToTotal_comp_map
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
  simp [doubleComplexZeroRowToTotal, doubleComplexZeroRowToTotalComponent, Category.assoc]

/- Domain-style sampling for Lemma 12.25.5:
- primary domain: cohomological bicomplexes, total complexes, and homotopy equivalences;
- sampled owner declarations:
  `doubleComplexZeroColumnToTotal`,
  `HomologicalComplex₂.total`,
  `HomologicalComplex₂.totalFunctor`,
  `Functor.mapHomotopyEquiv`,
  `HomotopyEquiv`;
- source/core/bridge triage:
  `source-facing`: the comparison map induced by `a : M^•[0] ⟶ A^{•,•}`;
  `core/canonical`: `Tot(A)` / `totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)` together with
    `doubleComplexZeroColumnToTotal` and `Functor.mapHomotopyEquiv`;
  `bridge/view`: the degree-zero column map extracted from `a`.

Primitive data:
- a bicomplex morphism `a : (single₀).obj M ⟶ A`;
- its degree-zero column map `M^• ⟶ A.X 0`.

Derived API:
- the source-facing comparison map `M^• ⟶ Tot(A)`,
- its compatibility with the owner morphism `total.map`.
-/

/-- The degree-zero column map extracted from `a : M^•[0] ⟶ A^{•,•}`. -/
noncomputable def singleZeroToZeroColumn
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (a : (single₀).obj M ⟶ A) :
    M ⟶ A.X 0 :=
  (singleObjXSelf (up ℤ) 0 M).inv ≫ a.f 0

/-- The cycle condition on the degree-zero column induced by `a`. -/
private theorem singleZeroToZeroColumn_comp_d
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (a : (single₀).obj M ⟶ A) :
    ∀ p : ℤ, (singleZeroToZeroColumn a).f p ≫ (A.d 0 1).f p = 0 := by
  intro p
  -- The outer chain-map identity at `0 ⟶ 1` says that the degree-zero column map lands in
  -- horizontal cycles, because the outer differential of the single complex is zero.
  have hcomm_p :
      (a.f 0).f p ≫ (A.d 0 1).f p =
        (((single₀).obj M).d 0 1).f p ≫ (a.f 1).f p := by
    simpa using congrArg
      (fun f : ((single₀).obj M).X 0 ⟶ A.X 1 ↦ f.f p)
      (a.comm 0 1 (by simp))
  calc
    (singleZeroToZeroColumn a).f p ≫ (A.d 0 1).f p =
        (singleObjXSelf (up ℤ) 0 M).inv.f p ≫ (a.f 0).f p ≫ (A.d 0 1).f p := by
      simp [singleZeroToZeroColumn, Category.assoc]
    _ =
        (singleObjXSelf (up ℤ) 0 M).inv.f p ≫ (((single₀).obj M).d 0 1).f p ≫ (a.f 1).f p := by
      rw [hcomm_p]
      simp [Category.assoc]
    _ = 0 := by
      simp [HomologicalComplex.single_obj_d, Category.assoc]

/-- The comparison map `α : M^• ⟶ \mathrm{Tot}(A^{•,•})` attached to a bicomplex morphism
`a : M^•[0] ⟶ A^{•,•}`. -/
noncomputable def singleZeroToTotal
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (a : (single₀).obj M ⟶ A) :
    M ⟶ Tot(A) :=
  doubleComplexZeroColumnToTotal (singleZeroToZeroColumn a) (singleZeroToZeroColumn_comp_d a)

/-- Helper for Lemma 12.25.5: the flip symmetry of total complexes is natural in bicomplex maps. -/
private theorem totalFlipIso_hom_map_eq
    {A B : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (φ : A ⟶ B) :
    total.map ((flipFunctor 𝒜 (up ℤ) (up ℤ)).map φ) (up ℤ) ≫ (B.totalFlipIso (up ℤ)).hom =
      (A.totalFlipIso (up ℤ)).hom ≫ total.map φ (up ℤ) := by
  -- Compare the two maps on each antidiagonal summand of `Tot(A.flip)`.
  ext n
  apply total.hom_ext
  intro q p h
  calc
    A.flip.ιTotal (up ℤ) q p n h ≫
        (total.map ((flipFunctor 𝒜 (up ℤ) (up ℤ)).map φ) (up ℤ)).f n ≫
          (B.totalFlipIso (up ℤ)).hom.f n =
      (φ.f p).f q ≫
        (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
          B.ιTotal (up ℤ) p q n
            (by rw [← ComplexShape.π_symm (up ℤ) (up ℤ) (up ℤ) p q, h])) := by
      rw [ιTotal_map_assoc, ιTotal_totalFlipIso_f_hom]
      rfl
    _ =
        ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
          ((φ.f p).f q ≫
            B.ιTotal (up ℤ) p q n
              (by rw [← ComplexShape.π_symm (up ℤ) (up ℤ) (up ℤ) p q, h])) := by
      rw [Linear.comp_units_smul]
    _ =
        A.flip.ιTotal (up ℤ) q p n h ≫
          (A.totalFlipIso (up ℤ)).hom.f n ≫ (total.map φ (up ℤ)).f n := by
      rw [ιTotal_totalFlipIso_f_hom_assoc, ιTotal_map]

/-- Helper for Lemma 12.25.5: postcomposing the zero-column comparison with a bicomplex morphism
agrees with postcomposing the induced total map by `total.map`. -/
private theorem zero_column_to_total_comp_total_map
    {K : CochainComplex 𝒜 ℤ}
    {A B : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (α : K ⟶ A.X 0)
    (hαcycles : ∀ q : ℤ, α.f q ≫ (A.d 0 1).f q = 0)
    (φ : A ⟶ B)
    (hcompcycles : ∀ q : ℤ, (α ≫ φ.f 0).f q ≫ (B.d 0 1).f q = 0) :
    doubleComplexZeroColumnToTotal (α ≫ φ.f 0) hcompcycles =
      doubleComplexZeroColumnToTotal α hαcycles ≫ total.map φ (up ℤ) := by
  let φflip := (flipFunctor 𝒜 (up ℤ) (up ℤ)).map φ
  have hflip_map :
      doubleComplexZeroColumnToZeroRowFlip (α ≫ φ.f 0) =
        doubleComplexZeroColumnToZeroRowFlip α ≫
          ((HomologicalComplex.eval 𝒜 (up ℤ) (0 : ℤ)).mapHomologicalComplex (up ℤ)).map φflip := by
    ext q
    simp [doubleComplexZeroColumnToZeroRowFlip, φflip, Category.assoc]
  have hrow :
      doubleComplexZeroRowToTotal
          (doubleComplexZeroColumnToZeroRowFlip (α ≫ φ.f 0))
          (doubleComplexZeroColumnToZeroRowFlip_comp_d (α ≫ φ.f 0) hcompcycles) =
        doubleComplexZeroRowToTotal
          (doubleComplexZeroColumnToZeroRowFlip α ≫
            ((HomologicalComplex.eval 𝒜 (up ℤ) (0 : ℤ)).mapHomologicalComplex (up ℤ)).map φflip)
          (doubleComplexZeroRow_comp_map_cycles
            (doubleComplexZeroColumnToZeroRowFlip α)
            (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles)
            φflip) := by
    rw [hflip_map]
    ext n
    rfl
  -- Rewrite the zero-column comparison through the flipped zero-row comparison, use the row
  -- functoriality theorem there, and then transport back with the naturality of `totalFlipIso`.
  calc
    doubleComplexZeroColumnToTotal (α ≫ φ.f 0) hcompcycles =
        doubleComplexZeroRowToTotal
            (doubleComplexZeroColumnToZeroRowFlip α ≫
              ((HomologicalComplex.eval 𝒜 (up ℤ) (0 : ℤ)).mapHomologicalComplex (up ℤ)).map
                φflip)
            (doubleComplexZeroRow_comp_map_cycles
              (doubleComplexZeroColumnToZeroRowFlip α)
              (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles)
              φflip) ≫
          (B.totalFlipIso (up ℤ)).hom := by
      simp [doubleComplexZeroColumnToTotal, hrow]
    _ =
        doubleComplexZeroRowToTotal
            (doubleComplexZeroColumnToZeroRowFlip α)
            (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) ≫
          total.map φflip (up ℤ) ≫ (B.totalFlipIso (up ℤ)).hom := by
      rw [doubleComplexZeroRowToTotal_comp_map]
    _ =
        doubleComplexZeroRowToTotal
            (doubleComplexZeroColumnToZeroRowFlip α)
            (doubleComplexZeroColumnToZeroRowFlip_comp_d α hαcycles) ≫
          (A.totalFlipIso (up ℤ)).hom ≫ total.map φ (up ℤ) := by
      rw [Category.assoc, totalFlipIso_hom_map_eq, ← Category.assoc]
    _ = doubleComplexZeroColumnToTotal α hαcycles ≫ total.map φ (up ℤ) := by
      simp [doubleComplexZeroColumnToTotal, Category.assoc]

/-- The source-facing comparison map is functorial in the target bicomplex map, and the
comparison with the owner totalization functor is the canonical map `total.map`. -/
theorem singleZeroToTotal_comp_map
    {M : CochainComplex 𝒜 ℤ}
    {A B : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (a : (single₀).obj M ⟶ A) (b : A ⟶ B) :
    singleZeroToTotal (a ≫ b) =
      singleZeroToTotal a ≫ total.map b (up ℤ) := by
  -- Compare the degree-zero column maps first, then apply the owner-level functoriality of
  -- zero-column totalization through `total.map`.
  have hcol :
      singleZeroToZeroColumn (a ≫ b) = singleZeroToZeroColumn a ≫ b.f 0 := by
    ext q
    simp [singleZeroToZeroColumn, Category.assoc]
  have hcompcycles :
      ∀ q : ℤ, (singleZeroToZeroColumn a ≫ b.f 0).f q ≫ (B.d 0 1).f q = 0 := by
    simpa [hcol] using singleZeroToZeroColumn_comp_d (a := a ≫ b)
  simpa [singleZeroToTotal, hcol] using
    zero_column_to_total_comp_total_map
      (singleZeroToZeroColumn a)
      (singleZeroToZeroColumn_comp_d a)
      b
      hcompcycles

/-- Helper for Lemma 12.25.5: a homotopy between endomorphisms of the outer degree-zero single
complex is already an equality of chain maps. -/
private theorem single_zero_self_map_eq_of_homotopy
    {M : CochainComplex 𝒜 ℤ}
    {f g : (single₀).obj M ⟶ (single₀).obj M}
    (h : Homotopy f g) :
    f = g := by
  -- Maps into the outer single complex are determined by their degree-zero component.
  apply HomologicalComplex.to_single_hom_ext
  -- The homotopy identity in degree `0` has no correction terms because the outer single
  -- complex vanishes away from degree `0`.
  have hhom_one : h.hom 1 0 = 0 := by
    exact (isZero_single_obj_X (up ℤ) (0 : ℤ) M 1 (by omega)).eq_of_src _ _
  have hhom_negOne : h.hom 0 (-1) = 0 := by
    exact (isZero_single_obj_X (up ℤ) (0 : ℤ) M (-1) (by omega)).eq_of_tgt _ _
  have hcomm_zero := h.comm 0
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hcomm_zero
  simpa [hhom_one, hhom_negOne, add_assoc, add_left_comm, add_comm] using hcomm_zero

/-- Helper for Lemma 12.25.5: the degree-zero column of a reverse map
`b : A^{\bullet,\bullet} \to M^\bullet[0]` is the chain map `A^{0,\bullet} \to M^\bullet`
obtained by collapsing the outer single complex in degree `0`. -/
private noncomputable def totalToSingleZeroZeroColumn
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (b : A ⟶ (single₀).obj M) :
    A.X 0 ⟶ M :=
  b.f 0 ≫ (singleObjXSelf (up ℤ) 0 M).hom

/-- Helper for Lemma 12.25.5: the horizontal differential from degree `-1` into the zeroth
column is annihilated by the reverse zero-column map, because the target single complex vanishes
outside outer degree `0`. -/
private theorem totalToSingleZero_prev_column_comp_zero
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)}
    (b : A ⟶ (single₀).obj M) :
    A.d (-1) 0 ≫ totalToSingleZeroZeroColumn b = 0 := by
  -- Route correction: isolate the `p = -1` source term now, since it is the only horizontal
  -- contribution that can survive after descending from `Tot(A)` to the zeroth column.
  calc
    A.d (-1) 0 ≫ totalToSingleZeroZeroColumn b
        = A.d (-1) 0 ≫ b.f 0 ≫ (singleObjXSelf (up ℤ) 0 M).hom := by
            simp [totalToSingleZeroZeroColumn, Category.assoc]
    _ = b.f (-1) ≫ ((single₀).obj M).d (-1) 0 ≫ (singleObjXSelf (up ℤ) 0 M).hom := by
          simpa [Category.assoc] using congrArg
            (fun f : A.X (-1) ⟶ ((single₀).obj M).X 0 ↦
              f ≫ (singleObjXSelf (up ℤ) 0 M).hom)
            (b.comm (-1) 0 (by simp))
    _ = 0 := by
          simp [Category.assoc, HomologicalComplex.single_obj_d]

/-- Helper for Lemma 12.25.5: `(0,n)` lies on the antidiagonal of total degree `n`. -/
private theorem zero_column_total_degree (n : ℤ) :
    (up ℤ).π (up ℤ) (up ℤ) (0, n) = n := by
  simp

/-- Helper for Lemma 12.25.5: the degree-`n` component of the textbook reverse map
`\mathrm{Tot}(A^{\bullet,\bullet}) \to M^\bullet`, supported only on the zeroth column. -/
private noncomputable def totalToSingleZeroComponent
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (b : A ⟶ (single₀).obj M) (n : ℤ) :
    (Tot(A)).X n ⟶ M.X n :=
  A.totalDesc fun p q h ↦
    if hp : p = 0 then
      (HomologicalComplex₂.XXIsoOfEq 𝒜 (up ℤ) (up ℤ) A hp (rfl : q = q)).hom ≫
        (totalToSingleZeroZeroColumn b).f q ≫
          (M.XIsoOfEq (by simpa [hp] using h)).hom
    else
      0

/-- Helper for Lemma 12.25.5: on each antidiagonal summand, the reverse component family is the
expected zeroth-column formula and is zero away from outer degree `0`. -/
private theorem ιTotal_comp_totalToSingleZeroComponent
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (b : A ⟶ (single₀).obj M)
    (p q n : ℤ) (h : p + q = n) :
    A.ιTotal (up ℤ) p q n h ≫ totalToSingleZeroComponent b n =
      if hp : p = 0 then
        (HomologicalComplex₂.XXIsoOfEq 𝒜 (up ℤ) (up ℤ) A hp (rfl : q = q)).hom ≫
          (totalToSingleZeroZeroColumn b).f q ≫
            (M.XIsoOfEq (by simpa [hp] using h)).hom
      else
        0 := by
  -- The descended map is defined summandwise, so precomposing with a chosen inclusion exposes
  -- exactly the `p = 0` branch of the textbook formula.
  simp [totalToSingleZeroComponent]

/-- Helper for Lemma 12.25.5: the reverse component family is compatible with the total
differential, by a summandwise check on the antidiagonal decomposition of `Tot(A)`. -/
private theorem totalToSingleZeroComponent_comm
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (b : A ⟶ (single₀).obj M)
    (n n' : ℤ) (hnn' : (up ℤ).Rel n n') :
    totalToSingleZeroComponent b n ≫ M.d n n' =
      (Tot(A)).d n n' ≫ totalToSingleZeroComponent b n' := by
  have hrel01 : (up ℤ).Rel (0 : ℤ) 1 := by
    simp [ComplexShape.up, ComplexShape.up']
  -- Route correction: follow the source proof on each antidiagonal summand instead of trying to
  -- transport the total differential abstractly.
  apply total.hom_ext
  intro p q hpq
  by_cases hp0 : p = 0
  · subst hp0
    have hq : q = n := by
      simpa using hpq
    subst hq
    -- On the zeroth column, the vertical part is the zero-column chain map and the horizontal
    -- part dies because the reverse family is supported only in outer degree `0`.
    calc
      A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) ≫
          totalToSingleZeroComponent b n ≫ M.d n n' =
        (totalToSingleZeroZeroColumn b).f n ≫ M.d n n' := by
          simp [ιTotal_comp_totalToSingleZeroComponent, Category.assoc]
      _ = (A.X 0).d n n' ≫ (totalToSingleZeroZeroColumn b).f n' := by
          simpa [Category.assoc] using (totalToSingleZeroZeroColumn b).comm n n' hnn'
      _ =
          A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) ≫
            (A.D₁ (up ℤ) n n' + A.D₂ (up ℤ) n n') ≫ totalToSingleZeroComponent b n' := by
          rw [A.d₁_eq hnn' 1 n' (by omega), A.d₂_eq 0 hrel01 n' (by omega)]
          have hne : ((1 : ℤ) ≠ 0) := by omega
          simp [ιTotal_comp_totalToSingleZeroComponent, hne, Category.assoc,
            ComplexShape.ε_up_ℤ]
      _ =
          A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) ≫
            (Tot(A)).d n n' ≫ totalToSingleZeroComponent b n' := by
          rw [A.total_d]
  · by_cases hpneg : p = -1
    · subst hpneg
      have hq : q = n' := by
        have : (-1 : ℤ) + q = n := by
          simpa using hpq
        have hn' : n + 1 = n' := by
          simpa [ComplexShape.up, ComplexShape.up'] using hnn'
        omega
      subst hq
      have hcomp :
          (A.d (-1) 0).f n' ≫ (totalToSingleZeroZeroColumn b).f n' = 0 := by
        simpa [Category.assoc] using
          congrArg (fun f : A.X (-1) ⟶ M ↦ f.f n') (totalToSingleZero_prev_column_comp_zero b)
      -- On the `(-1)`-st column, the only possible surviving horizontal term is the map into
      -- the zeroth column, and `b` kills it by construction.
      calc
        A.ιTotal (up ℤ) (-1) n' n hpq ≫
            totalToSingleZeroComponent b n ≫ M.d n n' = 0 := by
          simp [ιTotal_comp_totalToSingleZeroComponent, hp0, Category.assoc]
        _ =
            A.ιTotal (up ℤ) (-1) n' n hpq ≫
              (A.D₁ (up ℤ) n n' + A.D₂ (up ℤ) n n') ≫ totalToSingleZeroComponent b n' := by
            rw [Preadditive.comp_add, Category.assoc, Category.assoc,
              HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
            rw [A.d₁_eq hnn' 0 n' (Int.add_zero n'),
              A.d₂_eq (-1) hrel01 n' (by omega)]
            have hzero : (((-1 : ℤ) + 1) = 0) := by simp
            simp [ιTotal_comp_totalToSingleZeroComponent, hp0, hpneg, hzero, hcomp,
              Category.assoc, ComplexShape.ε_up_ℤ]
        _ =
            A.ιTotal (up ℤ) (-1) n' n hpq ≫
              (Tot(A)).d n n' ≫ totalToSingleZeroComponent b n' := by
            rw [A.total_d]
    · have hp10 : p + 1 ≠ 0 := by
        intro hp10
        apply hpneg
        omega
      -- Away from the zeroth and `(-1)`-st columns, both pieces of the total differential still
      -- land in columns where the reverse family vanishes.
      calc
        A.ιTotal (up ℤ) p q n hpq ≫ totalToSingleZeroComponent b n ≫ M.d n n' = 0 := by
          simp [ιTotal_comp_totalToSingleZeroComponent, hp0, Category.assoc]
        _ =
            A.ιTotal (up ℤ) p q n hpq ≫
              (A.D₁ (up ℤ) n n' + A.D₂ (up ℤ) n n') ≫ totalToSingleZeroComponent b n' := by
            rw [Preadditive.comp_add, Category.assoc, Category.assoc,
              HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
            rw [A.d₁_eq hnn' (p + 1) n' (by omega), A.d₂_eq p hrel01 n' (by omega)]
            simp [ιTotal_comp_totalToSingleZeroComponent, hp0, hp10, Category.assoc,
              ComplexShape.ε_up_ℤ]
        _ =
            A.ιTotal (up ℤ) p q n hpq ≫
              (Tot(A)).d n n' ≫ totalToSingleZeroComponent b n' := by
            rw [A.total_d]

/-- Helper for Lemma 12.25.5: the textbook reverse family assembles to a chain map
`\mathrm{Tot}(A^{\bullet,\bullet}) \to M^\bullet`. -/
private noncomputable def totalToSingleZero
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (b : A ⟶ (single₀).obj M) :
    Tot(A) ⟶ M where
  f := totalToSingleZeroComponent b
  -- The source proof defines `β` degreewise, so the only packaging step is the commutativity
  -- just verified on each total-degree summand.
  comm' := totalToSingleZeroComponent_comm b

/-- Helper for Lemma 12.25.5: the canonical comparison `singleZeroToTotal a` is the zeroth-column
summand inclusion on each degree. -/
private theorem singleZeroToTotal_component
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    (a : (single₀).obj M ⟶ A) (n : ℤ) :
    (singleZeroToTotal a).f n =
      (singleZeroToZeroColumn a).f n ≫ A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) := by
  -- Route correction: unfold the owner zero-column totalization once, then collapse the flip
  -- transport back to the literal `(0,n)` summand of `Tot(A)`.
  calc
    (singleZeroToTotal a).f n =
        (singleZeroToZeroColumn a).f n ≫
          A.flip.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫
            (A.totalFlipIso (up ℤ)).hom.f n := by
      simp [singleZeroToTotal, doubleComplexZeroColumnToTotal, doubleComplexZeroRowToTotal,
        doubleComplexZeroRowToTotalComponent, doubleComplexZeroColumnToZeroRowFlip,
        HomologicalComplex₂.zeroColumnIsoZeroRowFlip, Category.assoc]
    _ =
        (singleZeroToZeroColumn a).f n ≫
          (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) 0 n •
            A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n)) := by
      have hflip :
          A.flip.ιTotal (up ℤ) n 0 n (Int.add_zero n) ≫ (A.totalFlipIso (up ℤ)).hom.f n =
            ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) 0 n •
              A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) := by
        simpa [zero_column_total_degree] using
          (HomologicalComplex₂.ιTotal_totalFlipIso_f_hom
            (K := A) (c := up ℤ) (i₁ := 0) (i₂ := n) (j := n) (h := Int.add_zero n))
      exact congrArg (fun f ↦ (singleZeroToZeroColumn a).f n ≫ f) hflip
    _ =
        (singleZeroToZeroColumn a).f n ≫ A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) := by
      simp

/-- Helper for Lemma 12.25.5: if the outer homotopy inverse relation on `M^\bullet[0]` is given,
then the induced composite `M^\bullet \to \mathrm{Tot}(A^{\bullet,\bullet}) \to M^\bullet` is
strictly the identity. -/
private theorem singleZeroToTotal_comp_totalToSingleZero_eq_id_of_homotopy
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    {a : (single₀).obj M ⟶ A} {b : A ⟶ (single₀).obj M}
    (h : Homotopy (a ≫ b) (𝟙 ((single₀).obj M))) :
    singleZeroToTotal a ≫ totalToSingleZero b = 𝟙 M := by
  have hab : a ≫ b = 𝟙 ((single₀).obj M) :=
    single_zero_self_map_eq_of_homotopy h
  have hab₀ : (a ≫ b).f 0 = 𝟙 (((single₀).obj M).X 0) := by
    simpa using congrArg (fun f : (single₀).obj M ⟶ (single₀).obj M => f.f 0) hab
  have hcol : singleZeroToZeroColumn a ≫ totalToSingleZeroZeroColumn b = 𝟙 M := by
    -- Compare the two zero-column maps before descending to degreewise components.
    calc
      singleZeroToZeroColumn a ≫ totalToSingleZeroZeroColumn b =
          (singleObjXSelf (up ℤ) 0 M).inv ≫ (a ≫ b).f 0 ≫
            (singleObjXSelf (up ℤ) 0 M).hom := by
        simpa [singleZeroToZeroColumn, totalToSingleZeroZeroColumn, Category.assoc]
      _ = (singleObjXSelf (up ℤ) 0 M).inv ≫ 𝟙 _ ≫
            (singleObjXSelf (up ℤ) 0 M).hom := by
        rw [hab₀]
      _ = 𝟙 M := by
        simp
  ext n
  -- After exposing the source map on the `(0,n)` summand, the composite is exactly the zero-column
  -- composite already identified with the identity.
  calc
    (singleZeroToTotal a ≫ totalToSingleZero b).f n =
        (singleZeroToZeroColumn a ≫ totalToSingleZeroZeroColumn b).f n := by
      rw [singleZeroToTotal_component]
      simp [totalToSingleZero, ιTotal_comp_totalToSingleZeroComponent, Category.assoc]
    _ = (𝟙 M).f n := by
      rw [hcol]

/-- Helper for Lemma 12.25.5: the source-faithful reverse map followed by the source-facing
comparison agrees with totalization of the outer composite `b ≫ a`. -/
private theorem totalToSingleZero_comp_singleZeroToTotal_eq_total_map
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    {a : (single₀).obj M ⟶ A} {b : A ⟶ (single₀).obj M} :
    totalToSingleZero b ≫ singleZeroToTotal a = total.map (b ≫ a) (up ℤ) := by
  ext n
  apply total.hom_ext
  intro p q h
  by_cases hp : p = 0
  · subst hp
    have hq : q = n := by
      simpa using h
    subst hq
    have hcol : totalToSingleZeroZeroColumn b ≫ singleZeroToZeroColumn a = (b ≫ a).f 0 := by
      -- The zeroth-column comparison is the degree-zero outer component of `b ≫ a`.
      calc
        totalToSingleZeroZeroColumn b ≫ singleZeroToZeroColumn a =
            b.f 0 ≫ (singleObjXSelf (up ℤ) 0 M).hom ≫
              (singleObjXSelf (up ℤ) 0 M).inv ≫ a.f 0 := by
          simpa [singleZeroToZeroColumn, totalToSingleZeroZeroColumn, Category.assoc]
        _ = b.f 0 ≫ a.f 0 := by
          simp
        _ = (b ≫ a).f 0 := by
          rfl
    -- On the zeroth column, both sides are computed by the same degree-`n` component of `b ≫ a`.
    calc
      A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) ≫
          (totalToSingleZero b ≫ singleZeroToTotal a).f n =
        (totalToSingleZeroZeroColumn b ≫ singleZeroToZeroColumn a).f n ≫
          A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) := by
        rw [singleZeroToTotal_component]
        simp [totalToSingleZero, ιTotal_comp_totalToSingleZeroComponent, Category.assoc]
      _ = ((b ≫ a).f 0).f n ≫ A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) := by
        rw [hcol]
      _ = A.ιTotal (up ℤ) 0 n n (zero_column_total_degree n) ≫
            (total.map (b ≫ a) (up ℤ)).f n := by
        rw [← ιTotal_map]
  · have hb : b.f p = 0 := by
      exact (isZero_single_obj_X (up ℤ) (0 : ℤ) M p hp).eq_of_tgt _ _
    have hba : (b ≫ a).f p = 0 := by
      simp [hb]
    -- Away from the zeroth column, the reverse map vanishes and the total map also vanishes
    -- because `b` lands in the outer single complex.
    calc
      A.ιTotal (up ℤ) p q n h ≫ (totalToSingleZero b ≫ singleZeroToTotal a).f n = 0 := by
        rw [singleZeroToTotal_component]
        simp [totalToSingleZero, ιTotal_comp_totalToSingleZeroComponent, hp, Category.assoc]
      _ = A.ιTotal (up ℤ) p q n h ≫ (total.map (b ≫ a) (up ℤ)).f n := by
        symm
        rw [ιTotal_map]
        simp [hba]

-- Proof sketch: transport `a` through the owner totalization functor, use
-- `Functor.mapHomotopyEquiv` on a homotopy inverse of `a`, and compare the resulting map
-- `Tot(M^•[0]) ⟶ Tot(A)` with the canonical zero-column comparison `singleZeroToTotal a`.
/-- Lemma 12.25.5: if `a : M^•[0] ⟶ A^{•,•}` is a homotopy equivalence of cohomological
complexes of cochain complexes, then the induced comparison map
`α : M^• ⟶ \mathrm{Tot}(A^{•,•})` coming from the degree-zero column `M^• ⟶ A^{0,•}` is a
homotopy equivalence. -/
@[stacks 0FKH]
theorem singleZeroToTotal_homotopyEquivalence_of_homotopyEquivalence
    {M : CochainComplex 𝒜 ℤ}
    {A : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)]
    {a : (single₀).obj M ⟶ A}
    (ha : homotopyEquivalences (CochainComplex 𝒜 ℤ) (up ℤ) a) :
    homotopyEquivalences 𝒜 (up ℤ) (singleZeroToTotal a) := by
  rcases ha with ⟨e, rfl⟩
  let b : A ⟶ (single₀).obj M := e.inv
  let β : Tot(A) ⟶ M := totalToSingleZero b
  have hleft :
      singleZeroToTotal e.hom ≫ β = 𝟙 M := by
    -- The left inverse is strict because the outer homotopy on the single complex is already an
    -- equality in degree `0`.
    simpa [β, b] using
      singleZeroToTotal_comp_totalToSingleZero_eq_id_of_homotopy
        (a := e.hom) (b := b) e.homotopyHomInvId
  have hright :
      β ≫ singleZeroToTotal e.hom = total.map (b ≫ e.hom) (up ℤ) := by
    -- The right composite is the totalized outer endomorphism from the textbook proof.
    simpa [β, b] using
      totalToSingleZero_comp_singleZeroToTotal_eq_total_map (a := e.hom) (b := b)
  let htot :
      Homotopy (total.map (b ≫ e.hom) (up ℤ)) (𝟙 (Tot(A))) :=
    (totalFunctor 𝒜 (up ℤ) (up ℤ) (up ℤ)).mapHomotopy e.homotopyInvHomId
  refine ⟨
    { hom := singleZeroToTotal e.hom
      inv := β
      -- The first composite is strictly the identity after collapsing the outer single complex.
      homotopyHomInvId := Homotopy.ofEq hleft
      -- The second composite is homotopic to the identity via the totalized outer homotopy.
      homotopyInvHomId := by
        rw [hright]
        simpa [Functor.map_id] using htot }, rfl⟩

end
