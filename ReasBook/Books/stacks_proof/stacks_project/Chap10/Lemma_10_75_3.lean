import StacksProject_2024.Chap10.Lemma_10_75_3_Support

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ ComplexShape

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

/-- Helper for Chap10 Lemma 10 75 3: the row comparison component has the expected value on
each total-complex summand. -/
@[reassoc]
private theorem ιTotal_totalToRowCokernelComponent
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (i j n : ℕ) (h : ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (i, j) = n) :
    A.ιTotal (down ℕ) i j n h ≫ totalToRowCokernelComponent A n =
      if hi : i = 0 then
        (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A hi
          (by simpa [hi] using h)).hom ≫ cokernel.π ((A.d 1 0).f n)
      else
        0 := by
  -- Re-open the owner computation rule locally so the thin target file can use it after the
  -- support split.
  simp [totalToRowCokernelComponent]

/-- Helper for Chap10 Lemma 10 75 3: the induced row-cokernel chain map is characterized after
precomposing with the source cokernel projection. -/
private theorem cokernelπ_rowCokernelMapComponent_target
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)} (f : A ⟶ B) (j : ℕ) :
    cokernel.π ((A.d 1 0).f j) ≫ (rowCokernelMap f).f j =
      (f.f 0).f j ≫ cokernel.π ((B.d 1 0).f j) := by
  -- Unfold the induced chain map at degree `j`; the cokernel computation is built into its
  -- defining component.
  simpa [rowCokernelMap] using
    (_root_.cokernelπ_rowCokernelMapComponent f j)

/-- Helper for Chap10 Lemma 10 75 3: the row comparison map is natural in the bicomplex. -/
private theorem totalToRowCokernel_naturality
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)} (f : A ⟶ B) :
    HomologicalComplex₂.total.map f (down ℕ) ≫ totalToRowCokernel B =
      totalToRowCokernel A ≫ rowCokernelMap f := by
  -- Compare each component after precomposing with every total summand; both sides reduce to the
  -- same cokernel formula on the surviving horizontal-zero summand.
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  simp only [HomologicalComplex.comp_f]
  dsimp [totalToRowCokernel]
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  conv_lhs =>
    arg 2
    erw [ιTotal_totalToRowCokernelComponent]
  erw [ιTotal_totalToRowCokernelComponent_assoc]
  by_cases hi : i = 0
  · subst i
    have hj : j = n := by
      simpa [ComplexShape.π] using h
    subst j
    simp only [↓reduceDIte, XXIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    erw [cokernelπ_rowCokernelMapComponent_target]
    rfl
  · rw [dif_neg hi, dif_neg hi]
    aesop_cat

/-- The degree-`n` component of the canonical map from the total complex of `A` to the
columnwise cokernel complex `U(A)_•`. -/
noncomputable def totalToColumnCokernelComponent
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (n : ℕ) :
    (A.total (down ℕ)).X n ⟶ columnCokernelObject A n :=
  A.totalDesc (fun i j h ↦
    if hj : j = 0 then
      (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
        (by simpa [hj] using h) hj).hom ≫ cokernel.π ((A.X n).d 1 0)
    else
      0)

/-- Helper for Chap10 Lemma 10 75 3: the column comparison component has the expected value on
each total-complex summand. -/
@[reassoc]
private theorem ιTotal_totalToColumnCokernelComponent
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (i j n : ℕ) (h : ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (i, j) = n) :
    A.ιTotal (down ℕ) i j n h ≫ totalToColumnCokernelComponent A n =
      if hj : j = 0 then
        (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
          (by simpa [hj] using h) hj).hom ≫ cokernel.π ((A.X n).d 1 0)
      else
        0 := by
  -- This is the column analogue of the row computation, again by `totalDesc`.
  rw [totalToColumnCokernelComponent, HomologicalComplex₂.ι_totalDesc]
  split_ifs with hj
  · rfl
  · rfl

/-- Helper for Chap10 Lemma 10 75 3: the column comparison component is the row comparison
component for the flipped bicomplex, precomposed with the total-complex symmetry. -/
private theorem totalToColumnCokernelComponent_eq_flip
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (n : ℕ) :
    totalToColumnCokernelComponent A n =
      (A.totalFlipIso (down ℕ)).inv.f n ≫ totalToRowCokernelComponent A.flip n := by
  -- Compare both maps out of the total object on each summand. The flip isomorphism swaps the
  -- summand indices and contributes a sign; on the only surviving summands that sign is `1`.
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  rw [ιTotal_totalToColumnCokernelComponent]
  rw [← Category.assoc]
  rw [HomologicalComplex₂.ιTotal_totalFlipIso_f_inv]
  erw [Linear.units_smul_comp]
  erw [ιTotal_totalToRowCokernelComponent]
  by_cases hj : j = 0
  · subst j
    have hn : n = i := by
      simpa [ComplexShape.π] using h.symm
    subst n
    change cokernel.π ((A.X i).d 1 0) =
      ((-1 : ℤˣ) ^ (i * 0)) • cokernel.π ((A.X i).d 1 0)
    simp
  · rw [dif_neg hj]
    rw [dif_neg hj]
    change 0 =
      ((-1 : ℤˣ) ^ (i * j)) • (0 : (A.X i).X j ⟶ rowCokernelObject A.flip n)
    simp

-- Proof sketch: this is the same computation as for `totalToRowCokernel_comm`, now selecting the
-- `(n, 0)` summand instead of `(0, n)`.
/-- The canonical degreewise maps from the total complex to `U(A)_•` commute with the
differentials. -/
private theorem totalToColumnCokernel_comm
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (n n' : ℕ) (_hnn' : (down ℕ).Rel n n') :
    totalToColumnCokernelComponent A n ≫ (columnCokernelComplex A).d n n' =
      (A.total (down ℕ)).d n n' ≫ totalToColumnCokernelComponent A n' := by
  -- Route correction: use the established row chain map for `A.flip` and the component bridge
  -- above, instead of repeating the long summand calculation in the column direction.
  rw [totalToColumnCokernelComponent_eq_flip A n,
    totalToColumnCokernelComponent_eq_flip A n']
  simpa [totalToRowCokernel, columnCokernelComplex, Category.assoc] using
    (((A.totalFlipIso (down ℕ)).inv ≫ totalToRowCokernel A.flip).comm n n')

/-- The canonical morphism from the total complex of `A` to the columnwise cokernel complex
`U(A)_•`. -/
noncomputable def totalToColumnCokernel
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) :
    A.total (down ℕ) ⟶ columnCokernelComplex A where
  f := totalToColumnCokernelComponent A
  comm' := totalToColumnCokernel_comm A

/-- Helper for Chap10 Lemma 10 75 3: the column comparison chain map is the row comparison for
the flipped bicomplex, precomposed with the total-complex symmetry. -/
private theorem totalToColumnCokernel_eq_flip
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) :
    totalToColumnCokernel A =
      (A.totalFlipIso (down ℕ)).inv ≫ totalToRowCokernel A.flip := by
  -- Compare chain maps degreewise; the component bridge already identifies the two maps.
  apply HomologicalComplex.Hom.ext
  funext n
  exact totalToColumnCokernelComponent_eq_flip A n

/-- Helper for Chap10 Lemma 10 75 3: the column comparison map is natural in the bicomplex. -/
private theorem totalToColumnCokernel_naturality
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)} (f : A ⟶ B) :
    HomologicalComplex₂.total.map f (down ℕ) ≫ totalToColumnCokernel B =
      totalToColumnCokernel A ≫ columnCokernelMap f := by
  -- As in the row case, compare on each total summand and reduce to the flipped cokernel map.
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  simp only [HomologicalComplex.comp_f]
  dsimp [totalToColumnCokernel, columnCokernelMap, rowCokernelMap]
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  conv_lhs =>
    arg 2
    erw [ιTotal_totalToColumnCokernelComponent]
  erw [ιTotal_totalToColumnCokernelComponent_assoc]
  by_cases hj : j = 0
  · subst j
    have hi : i = n := by
      simpa [ComplexShape.π] using h
    subst i
    simp only [↓reduceDIte, XXIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    erw [cokernelπ_rowCokernelMapComponent]
    rfl
  · rw [dif_neg hj, dif_neg hj]
    erw [zero_comp, comp_zero]

-- Proof sketch: apply the previous rowwise argument to the flipped bicomplex `A.flip`; its
-- rowwise cokernel complex is definitionally `U(A)_•`.
/-- If the columns of `A` resolve `U(A)_•`, then the canonical map from `Tot(A)` to `U(A)_•` is a
quasi-isomorphism. -/
theorem totalToColumnCokernel_quasiIso
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hcols : ColumnsResolve A) :
    QuasiIso (totalToColumnCokernel A) := by
  -- The column comparison is componentwise the composite of the total flip isomorphism with the
  -- row comparison for `A.flip`; quasi-isomorphisms are stable under this composition.
  letI : QuasiIso (totalToRowCokernel A.flip) := totalToRowCokernel_quasiIso A.flip hcols
  rw [totalToColumnCokernel_eq_flip A]
  infer_instance

/-- Chap10 Lemma 10 75 3

If the rows of `A` resolve `R(A)_•` and the columns resolve `U(A)_•`, then their homology
groups are canonically isomorphic. -/
@[stacks 00M1]
noncomputable def resolved_double_complex_homology_comparison
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) (hcols : ColumnsResolve A) (i : ℕ) :
    (rowCokernelComplex A).homology i ≅ (columnCokernelComplex A).homology i :=
  letI : QuasiIso (totalToRowCokernel A) := totalToRowCokernel_quasiIso A hrows
  letI : QuasiIso (totalToColumnCokernel A) := totalToColumnCokernel_quasiIso A hcols
  (isoOfQuasiIsoAt (totalToRowCokernel A) i).symm ≪≫
    isoOfQuasiIsoAt (totalToColumnCokernel A) i

/-- Helper for Chap10 Lemma 10 75 3: inverse quasi-isomorphism homology maps are natural across
a commuting square of chain complexes. -/
private theorem homologyMap_isoOfQuasiIsoAt_inv_naturality
    {K L K' L' : ChainComplex (ModuleCat R) ℕ}
    (α : K ⟶ L) (α' : K' ⟶ L') (gK : K ⟶ K') (gL : L ⟶ L')
    [QuasiIso α] [QuasiIso α'] (i : ℕ)
    (h : gK ≫ α' = α ≫ gL) :
    homologyMap gL i ≫ (isoOfQuasiIsoAt α' i).inv =
      (isoOfQuasiIsoAt α i).inv ≫ homologyMap gK i := by
  -- Apply homology to the square, then cancel the two isomorphism factors.
  have hhom :
      homologyMap gK i ≫ homologyMap α' i =
        homologyMap α i ≫ homologyMap gL i := by
    simpa [HomologicalComplex.homologyMap_comp] using congrArg (fun q ↦ homologyMap q i) h
  calc
    homologyMap gL i ≫ (isoOfQuasiIsoAt α' i).inv =
        (isoOfQuasiIsoAt α i).inv ≫ homologyMap α i ≫
          homologyMap gL i ≫ (isoOfQuasiIsoAt α' i).inv := by
      simp
    _ = (isoOfQuasiIsoAt α i).inv ≫ homologyMap gK i ≫
          homologyMap α' i ≫ (isoOfQuasiIsoAt α' i).inv := by
      simpa [Category.assoc] using
        congrArg
          (fun q ↦ (isoOfQuasiIsoAt α i).inv ≫ q ≫ (isoOfQuasiIsoAt α' i).inv)
          hhom.symm
    _ = (isoOfQuasiIsoAt α i).inv ≫ homologyMap gK i := by
      simp

/-- Helper for Chap10 Lemma 10 75 3: quasi-isomorphism homology maps are natural across a
commuting square of chain complexes. -/
private theorem homologyMap_isoOfQuasiIsoAt_hom_naturality
    {K L K' L' : ChainComplex (ModuleCat R) ℕ}
    (α : K ⟶ L) (α' : K' ⟶ L') (gK : K ⟶ K') (gL : L ⟶ L')
    [QuasiIso α] [QuasiIso α'] (i : ℕ)
    (h : gK ≫ α' = α ≫ gL) :
    homologyMap gK i ≫ (isoOfQuasiIsoAt α' i).hom =
      (isoOfQuasiIsoAt α i).hom ≫ homologyMap gL i := by
  -- The forward direction is just functoriality of `homologyMap` applied to the square.
  have hhom := congrArg (fun q ↦ homologyMap q i) h
  simpa [HomologicalComplex.homologyMap_comp, isoOfQuasiIsoAt] using hhom

/-- The homology comparison of Lemma 10.75.3 is natural in morphisms of resolved double
complexes. -/
theorem resolved_double_complex_homology_comparison_naturality
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)}
    (hrowsA : RowsResolve A) (hcolsA : ColumnsResolve A)
    (hrowsB : RowsResolve B) (hcolsB : ColumnsResolve B)
    (f : A ⟶ B) (i : ℕ) :
    homologyMap (rowCokernelMap f) i ≫
        (resolved_double_complex_homology_comparison B hrowsB hcolsB i).hom =
      (resolved_double_complex_homology_comparison A hrowsA hcolsA i).hom ≫
        homologyMap (columnCokernelMap f) i := by
  -- Expand the comparison isomorphisms and use the two chain-level naturality squares proved
  -- above to move the row and column homology maps across the quasi-isomorphism factors.
  letI : QuasiIso (totalToRowCokernel A) := totalToRowCokernel_quasiIso A hrowsA
  letI : QuasiIso (totalToColumnCokernel A) := totalToColumnCokernel_quasiIso A hcolsA
  letI : QuasiIso (totalToRowCokernel B) := totalToRowCokernel_quasiIso B hrowsB
  letI : QuasiIso (totalToColumnCokernel B) := totalToColumnCokernel_quasiIso B hcolsB
  let totalMap := HomologicalComplex₂.total.map f (down ℕ)
  have hrow :=
    homologyMap_isoOfQuasiIsoAt_inv_naturality
      (totalToRowCokernel A) (totalToRowCokernel B) totalMap (rowCokernelMap f) i
      (totalToRowCokernel_naturality f)
  have hcol :=
    homologyMap_isoOfQuasiIsoAt_hom_naturality
      (totalToColumnCokernel A) (totalToColumnCokernel B) totalMap
      (columnCokernelMap f) i
      (totalToColumnCokernel_naturality f)
  dsimp [resolved_double_complex_homology_comparison]
  calc
    homologyMap (rowCokernelMap f) i ≫
        (isoOfQuasiIsoAt (totalToRowCokernel B) i).inv ≫
        (isoOfQuasiIsoAt (totalToColumnCokernel B) i).hom =
      (isoOfQuasiIsoAt (totalToRowCokernel A) i).inv ≫
        homologyMap totalMap i ≫
        (isoOfQuasiIsoAt (totalToColumnCokernel B) i).hom := by
        simpa [Category.assoc] using
          congrArg (fun q ↦ q ≫ (isoOfQuasiIsoAt (totalToColumnCokernel B) i).hom) hrow
    _ = (isoOfQuasiIsoAt (totalToRowCokernel A) i).inv ≫
        (isoOfQuasiIsoAt (totalToColumnCokernel A) i).hom ≫
        homologyMap (columnCokernelMap f) i := by
        simpa [Category.assoc] using
          congrArg (fun q ↦ (isoOfQuasiIsoAt (totalToRowCokernel A) i).inv ≫ q) hcol

end
