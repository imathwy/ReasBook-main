import StacksProject_2024.Chap10.Definition_10_71_2

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ ComplexShape

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

local notation "moduleSingle[" M "]" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) M

/-- Helper for Chap10 Lemma 10 75 3: the chain-total shape on `down ℕ` is symmetric, with
the Koszul sign `(-1)^(i*j)` for swapping horizontal and vertical degrees. -/
private instance downNatTotalComplexShapeSymmetry :
    TotalComplexShapeSymmetry (down ℕ) (down ℕ) (down ℕ) where
  symm p q := by
    -- The total degree is addition, so swapping the two indices preserves it by commutativity.
    simp [ComplexShape.π, add_comm]
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    intro p p' h q
    -- A horizontal down-step lowers `p` by one, contributing the vertical sign `(-1)^q`.
    dsimp [ComplexShape.ε₁, ComplexShape.ε₂]
    have hp : p = p' + 1 := by
      simpa [ComplexShape.down, ComplexShape.down'] using h.symm
    rw [hp, add_mul, one_mul, mul_one]
    calc
      (-1 : ℤˣ) ^ (p' * q + q) =
          (-1 : ℤˣ) ^ (p' * q) * (-1 : ℤˣ) ^ q := by
        exact pow_add (-1 : ℤˣ) (p' * q) q
      _ = (-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ (p' * q) := by
        rw [mul_comm]
  σ_ε₂ := by
    intro p q q' h
    -- A vertical down-step lowers `q` by one, and the two copies of `(-1)^p` cancel.
    dsimp [ComplexShape.ε₁, ComplexShape.ε₂]
    have hq : q = q' + 1 := by
      simpa [ComplexShape.down, ComplexShape.down'] using h.symm
    rw [hq, mul_add, mul_one, one_mul]
    calc
      (-1 : ℤˣ) ^ (p * q' + p) * (-1 : ℤˣ) ^ p =
          (((-1 : ℤˣ) ^ (p * q') * (-1 : ℤˣ) ^ p) * (-1 : ℤˣ) ^ p) := by
        exact congrArg (fun x : ℤˣ ↦ x * (-1 : ℤˣ) ^ p)
          (pow_add (-1 : ℤˣ) (p * q') p)
      _ = (-1 : ℤˣ) ^ (p * q') := by
        rw [mul_assoc, Int.units_mul_self, mul_one]

/-- The `j`-th row of a first-quadrant double complex, viewed as a chain complex in the horizontal
direction. -/
private abbrev rowComplexFunctor (j : ℕ) :
    HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ) ⥤ ChainComplex (ModuleCat R) ℕ :=
  (HomologicalComplex.eval (ModuleCat R) (down ℕ) j).mapHomologicalComplex (down ℕ)

/-- The `j`-th row of a first-quadrant double complex, viewed as a chain complex in the horizontal
direction. -/
abbrev rowComplex
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (j : ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  (rowComplexFunctor j).obj A

/-- The degree-`j` term of the row-cokernel complex `R(A)_•`. -/
abbrev rowCokernelObject
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (j : ℕ) : ModuleCat R :=
  cokernel ((A.d 1 0).f j)

/-- The canonical augmentation from the `j`-th row of `A` to the corresponding term of
`R(A)_•`. -/
noncomputable def rowAugmentation
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (j : ℕ) :
    rowComplex A j ⟶ moduleSingle[rowCokernelObject A j] where
  f i := match i with
    | 0 => cokernel.π ((A.d 1 0).f j)
    | _ + 1 => 0
  comm' i i' h := by
    rcases i with _ | i
    · cases h
    rcases i with _ | i
    · rcases i' with _ | i'
      · aesop_cat
      · cases h
    · rcases i' with _ | i'
      · cases h
      · aesop_cat

/-- The differential on the row-cokernel complex `R(A)_•`. -/
noncomputable def rowCokernelDifferential
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (j : ℕ) :
    rowCokernelObject A (j + 1) ⟶ rowCokernelObject A j :=
  cokernel.map
    ((A.d 1 0).f (j + 1))
    ((A.d 1 0).f j)
    ((A.X 1).d (j + 1) j)
    ((A.X 0).d (j + 1) j)
    (A.d_comm 1 0 (j + 1) j)

/-- Helper for Chap10 Lemma 10 75 3: the row-cokernel differential is characterized after
the cokernel projection. -/
theorem cokernelπ_rowCokernelDifferential
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (j : ℕ) :
    cokernel.π ((A.d 1 0).f (j + 1)) ≫ rowCokernelDifferential A j =
      (A.X 0).d (j + 1) j ≫ cokernel.π ((A.d 1 0).f j) := by
  -- The induced differential was defined by the universal cokernel map.
  simp [rowCokernelDifferential]

-- Proof sketch: compose two induced cokernel maps and use that the vertical differentials in the
-- columns square to zero.
/-- Consecutive differentials in the row-cokernel complex compose to zero. -/
private theorem rowCokernelDifferential_sq
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (j : ℕ) :
    rowCokernelDifferential A (j + 1) ≫ rowCokernelDifferential A j = 0 := by
  -- It suffices to compare after precomposing with the cokernel projection, which is epi.
  apply (cancel_epi (cokernel.π ((A.d 1 0).f (j + 2)))).1
  -- After this reduction, the statement is just `d ≫ d = 0` in the `0`-th row.
  simp [rowCokernelDifferential, Category.assoc]

/-- The chain complex `R(A)_•` obtained by taking rowwise cokernels of the first horizontal
morphism in a double complex. -/
noncomputable def rowCokernelComplex
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) :
    ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of
    (rowCokernelObject A)
    (rowCokernelDifferential A)
    (rowCokernelDifferential_sq A)

/-- Each row of `A` is a resolution of the corresponding term of `R(A)_•` in the canonical
Chapter `10.71` sense: the row augmentation is a quasi-isomorphism. -/
def RowsResolve (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) : Prop :=
  ∀ j, QuasiIso (rowAugmentation A j)

/-- Each column of `A` is a resolution of the corresponding term of `U(A)_•`. -/
abbrev ColumnsResolve (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) : Prop :=
  RowsResolve A.flip

/-- `ColumnsResolve` is definitionally the row-resolution condition on the flipped bicomplex. -/
@[simp] theorem columnsResolve_iff
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) :
    ColumnsResolve A ↔ RowsResolve A.flip :=
  Iff.rfl

/-- The degree-`i` term of the column-cokernel complex `U(A)_•`. -/
abbrev columnCokernelObject
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (i : ℕ) : ModuleCat R :=
  rowCokernelObject A.flip i

/-- The differential on the column-cokernel complex `U(A)_•`. -/
noncomputable abbrev columnCokernelDifferential
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (i : ℕ) :
    columnCokernelObject A (i + 1) ⟶ columnCokernelObject A i :=
  rowCokernelDifferential A.flip i

/-- The chain complex `U(A)_•` obtained by taking columnwise cokernels of the first vertical
morphism in a double complex. -/
noncomputable abbrev columnCokernelComplex
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) :
    ChainComplex (ModuleCat R) ℕ :=
  rowCokernelComplex A.flip

/-- The induced map on the degree-`j` row-cokernel objects. -/
private noncomputable def rowCokernelMapComponent
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)} (f : A ⟶ B) (j : ℕ) :
    rowCokernelObject A j ⟶ rowCokernelObject B j :=
  cokernel.map
    ((A.d 1 0).f j)
    ((B.d 1 0).f j)
    ((f.f 1).f j)
    ((f.f 0).f j)
    ((comm_f f 1 0 j).symm)

/-- Helper for Chap10 Lemma 10 75 3: the row-cokernel map is characterized after the
cokernel projection. -/
theorem cokernelπ_rowCokernelMapComponent
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)} (f : A ⟶ B) (j : ℕ) :
    cokernel.π ((A.d 1 0).f j) ≫ rowCokernelMapComponent f j =
      (f.f 0).f j ≫ cokernel.π ((B.d 1 0).f j) := by
  -- This is the defining computation rule for the induced cokernel map.
  simp [rowCokernelMapComponent]

-- Proof sketch: check the square with the induced cokernel maps in consecutive degrees using
-- commutativity of `f` with the vertical differentials; `ChainComplex.ofHom` extends this to a
-- chain map.
private theorem rowCokernelMapComponent_comm
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)} (f : A ⟶ B) (j : ℕ) :
    rowCokernelMapComponent f (j + 1) ≫ rowCokernelDifferential B j =
      rowCokernelDifferential A j ≫ rowCokernelMapComponent f j := by
  -- As above, we compare after precomposing with the source cokernel projection.
  apply (cancel_epi (cokernel.π ((A.d 1 0).f (j + 1)))).1
  -- The induced square on cokernels is defined precisely so that this reduces to
  -- compatibility of `f` with the vertical differentials.
  simp [rowCokernelMapComponent, rowCokernelDifferential, Category.assoc]

/-- The morphism `R(A)_• ⟶ R(B)_•` induced by a morphism of double complexes. -/
noncomputable def rowCokernelMap
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)} (f : A ⟶ B) :
    rowCokernelComplex A ⟶ rowCokernelComplex B :=
  ChainComplex.ofHom
    (rowCokernelObject A)
    (rowCokernelDifferential A)
    (rowCokernelDifferential_sq A)
    (rowCokernelObject B)
    (rowCokernelDifferential B)
    (rowCokernelDifferential_sq B)
    (rowCokernelMapComponent f)
    (rowCokernelMapComponent_comm f)

/-- The morphism `U(A)_• ⟶ U(B)_•` induced by a morphism of double complexes. -/
noncomputable abbrev columnCokernelMap
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)} (f : A ⟶ B) :
    columnCokernelComplex A ⟶ columnCokernelComplex B :=
  rowCokernelMap ((flipFunctor (ModuleCat R) (down ℕ) (down ℕ)).map f)

/-- The degree-`n` component of the canonical map from the total complex of `A` to the rowwise
cokernel complex `R(A)_•`. -/
noncomputable def totalToRowCokernelComponent
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (n : ℕ) :
    (A.total (down ℕ)).X n ⟶ rowCokernelObject A n :=
  A.totalDesc (fun i j h ↦
    if hi : i = 0 then
      (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A hi
        (by simpa [hi] using h)).hom ≫ cokernel.π ((A.d 1 0).f n)
    else
      0)

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
  -- The component was defined by `totalDesc`, so the summand computation is its owner lemma.
  simp [totalToRowCokernelComponent]

/-- Helper for Chap10 Lemma 10 75 3: precomposing a total differential with a total summand
inclusion splits into the horizontal and vertical total differentials. -/
private theorem ιTotal_total_d_comp
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (i j n n' : ℕ)
    (h : ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (i, j) = n)
    {X : ModuleCat R} (g : (A.total (down ℕ)).X n' ⟶ X) :
    A.ιTotal (down ℕ) i j n h ≫ (A.total (down ℕ)).d n n' ≫ g =
      A.ιTotal (down ℕ) i j n h ≫ A.D₁ (down ℕ) n n' ≫ g +
        A.ιTotal (down ℕ) i j n h ≫ A.D₂ (down ℕ) n n' ≫ g := by
  -- The total differential is by definition the sum of `D₁` and `D₂`; reassociate once so
  -- later summand-case proofs can rewrite the two pieces separately.
  rw [A.total_d]
  rw [← Category.assoc]
  conv_lhs =>
    arg 1
    erw [Preadditive.comp_add]
  erw [Preadditive.add_comp]
  erw [← Category.assoc]
  erw [Category.assoc]
  rfl

/-- Helper for Chap10 Lemma 10 75 3: a `down ℕ` differential lowers the degree by one. -/
private theorem downRel_eq_succ {n n' : ℕ} (h : (down ℕ).Rel n n') :
    n = n' + 1 := by
  -- The `down` shape is encoded with the target plus one equal to the source.
  simpa [ComplexShape.down, ComplexShape.down'] using h.symm

/-- Helper for Chap10 Lemma 10 75 3: the vertical differential from horizontal degree `0`
survives as the row-cokernel differential after projecting to `R(A)_•`. -/
private theorem rowD₂_zeroHorizontal_totalToRowCokernelComponent
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (n : ℕ) :
    A.d₂ (down ℕ) 0 (n + 1) n ≫ totalToRowCokernelComponent A n =
      (A.X 0).d (n + 1) n ≫ cokernel.π ((A.d 1 0).f n) := by
  -- Rewrite the source-level vertical differential and then evaluate the row component on the
  -- resulting horizontal-degree-zero summand.
  rw [A.d₂_eq (down ℕ) 0
    (show (down ℕ).Rel (n + 1) n by simp [ComplexShape.down, ComplexShape.down'])
    n
    (show ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (0, n) = n by
      simp [ComplexShape.π])]
  simp only [ε₂_def, ε_zero, one_smul]
  erw [Category.assoc]
  erw [ιTotal_totalToRowCokernelComponent]
  simp only [↓reduceDIte, XXIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]

/-- Helper for Chap10 Lemma 10 75 3: vertical differentials from positive horizontal degree
vanish after the row-cokernel comparison component. -/
private theorem rowD₂_positiveHorizontal_totalToRowCokernelComponent_eq_zero
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {i j n : ℕ} (hi : i ≠ 0) :
    A.d₂ (down ℕ) i j n ≫ totalToRowCokernelComponent A n = 0 := by
  -- If the vertical step exists and lands in total degree `n`, the component formula kills it
  -- because the horizontal degree remains positive; otherwise the total summand map is zero.
  by_cases hrel : (down ℕ).Rel j ((down ℕ).next j)
  · by_cases hπ :
        ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (i, (down ℕ).next j) = n
    · rw [A.d₂_eq (down ℕ) i hrel n hπ]
      simp only [ε₂_def, ε_down_ℕ]
      erw [Linear.units_smul_comp]
      erw [Category.assoc]
      erw [ιTotal_totalToRowCokernelComponent]
      simp [hi]
    · rw [A.d₂_eq_zero' (down ℕ) i hrel n hπ]
      simp
  · rw [A.d₂_eq_zero (down ℕ) i j n hrel]
    simp

/-- Helper for Chap10 Lemma 10 75 3: the horizontal differential from degree `1` is killed by
the defining cokernel projection in `R(A)_•`. -/
private theorem rowD₁_oneHorizontal_totalToRowCokernelComponent_eq_zero
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (n : ℕ) :
    A.d₁ (down ℕ) 1 n n ≫ totalToRowCokernelComponent A n = 0 := by
  -- Rewrite the horizontal differential to the map defining the cokernel and then apply the
  -- cokernel condition after evaluating the degree-zero row component.
  rw [A.d₁_eq (down ℕ)
    (show (down ℕ).Rel 1 0 by simp [ComplexShape.down, ComplexShape.down'])
    n n
    (show ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (0, n) = n by
      simp [ComplexShape.π])]
  simp only [ε₁_def, one_smul]
  erw [Category.assoc]
  erw [ιTotal_totalToRowCokernelComponent]
  simp only [↓reduceDIte, XXIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  exact cokernel.condition ((A.d 1 0).f n)

/-- Helper for Chap10 Lemma 10 75 3: horizontal differentials not starting in degree `1`
vanish after the row-cokernel comparison component. -/
private theorem rowD₁_notOneHorizontal_totalToRowCokernelComponent_eq_zero
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {i j n : ℕ} (hi : i ≠ 1) :
    A.d₁ (down ℕ) i j n ≫ totalToRowCokernelComponent A n = 0 := by
  -- A missing horizontal step gives zero immediately; if the step exists, landing in horizontal
  -- degree `0` would force `i = 1`, so the row component kills all remaining cases.
  by_cases hrel : (down ℕ).Rel i ((down ℕ).next i)
  · by_cases hπ :
        ComplexShape.π (down ℕ) (down ℕ) (down ℕ) ((down ℕ).next i, j) = n
    · have hnext_ne : (down ℕ).next i ≠ 0 := by
        intro hzero
        apply hi
        have hsucc : (down ℕ).next i + 1 = i := by
          simpa [ComplexShape.down, ComplexShape.down'] using hrel
        omega
      rw [A.d₁_eq (down ℕ) hrel j n hπ]
      simp only [ε₁_def, one_smul]
      erw [Category.assoc]
      erw [ιTotal_totalToRowCokernelComponent]
      simp [hnext_ne]
    · rw [A.d₁_eq_zero' (down ℕ) hrel j n hπ]
      simp
  · rw [A.d₁_eq_zero (down ℕ) i j n hrel]
    simp

-- Proof sketch: check the identity after precomposing with each summand inclusion `A_{i,j} →
-- Tot(A)_n`. Only the `(i, j) = (0, n)` and `(1, n')` summands contribute, and the remaining
-- relation is exactly the defining compatibility of `cokernel.map`.
/-- The canonical degreewise maps from the total complex to `R(A)_•` commute with the
differentials. -/
private theorem totalToRowCokernel_comm
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (n n' : ℕ) (hnn' : (down ℕ).Rel n n') :
    totalToRowCokernelComponent A n ≫ (rowCokernelComplex A).d n n' =
      (A.total (down ℕ)).d n n' ≫ totalToRowCokernelComponent A n' := by
  -- Compare the two maps after precomposing with each total-complex summand.
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  -- The total degree and the `down` differential relation force the three horizontal cases:
  -- `i = 0`, `i = 1`, and `i ≥ 2`.
  have hn : n = i + j := by
    simpa [ComplexShape.π] using h.symm
  have hrel : n' + 1 = i + j := (downRel_eq_succ hnn').symm.trans hn
  subst n
  rcases i with _ | i
  · have hj : j = n' + 1 := by
      omega
    subst j
    -- In horizontal degree `0`, the `D₁` summand vanishes and the `D₂` summand is exactly the
    -- vertical differential defining the row-cokernel complex.
    rw [← Category.assoc, ιTotal_totalToRowCokernelComponent]
    simp only [↓reduceDIte, XXIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    simp only [rowCokernelComplex, ChainComplex.of_d]
    erw [cokernelπ_rowCokernelDifferential]
    erw [ιTotal_total_d_comp]
    rw [HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
    have hd₁ : A.d₁ (down ℕ) 0 (n' + 1) n' ≫ totalToRowCokernelComponent A n' = 0 :=
      @rowD₁_notOneHorizontal_totalToRowCokernelComponent_eq_zero
        R _ A 0 (n' + 1) n' (by omega)
    have hd₂ : A.d₂ (down ℕ) 0 (n' + 1) n' ≫ totalToRowCokernelComponent A n' =
        (A.X 0).d (n' + 1) n' ≫ cokernel.π ((A.d 1 0).f n') :=
      rowD₂_zeroHorizontal_totalToRowCokernelComponent A n'
    calc
      (A.X 0).d (n' + 1) n' ≫ cokernel.π ((A.d 1 0).f n') =
          0 + (A.X 0).d (n' + 1) n' ≫ cokernel.π ((A.d 1 0).f n') := by
        simp
      _ = A.d₁ (down ℕ) 0 (n' + 1) n' ≫ totalToRowCokernelComponent A n' +
          A.d₂ (down ℕ) 0 (n' + 1) n' ≫ totalToRowCokernelComponent A n' := by
        rw [hd₁, hd₂]
  rcases i with _ | i
  · have hj : j = n' := by
      omega
    subst j
    -- In horizontal degree `1`, the left side is zero, and the two total-differential summands
    -- are killed by the cokernel condition and positive-horizontal-degree vanishing.
    rw [← Category.assoc, ιTotal_totalToRowCokernelComponent]
    simp only [Nat.succ_ne_zero, ↓reduceDIte, zero_comp]
    erw [ιTotal_total_d_comp]
    rw [HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
    change 0 = A.d₁ (down ℕ) 1 n' n' ≫ totalToRowCokernelComponent A n' +
      A.d₂ (down ℕ) 1 n' n' ≫ totalToRowCokernelComponent A n'
    have hd₁ : A.d₁ (down ℕ) 1 n' n' ≫ totalToRowCokernelComponent A n' = 0 :=
      rowD₁_oneHorizontal_totalToRowCokernelComponent_eq_zero A n'
    have hd₂ : A.d₂ (down ℕ) 1 n' n' ≫ totalToRowCokernelComponent A n' = 0 :=
      @rowD₂_positiveHorizontal_totalToRowCokernelComponent_eq_zero
        R _ A 1 n' n' (by omega)
    simpa [hd₁, hd₂]
  · -- In horizontal degree at least `2`, both total-differential summands stay away from
    -- horizontal degree `0`, so the row component kills them.
    rw [← Category.assoc, ιTotal_totalToRowCokernelComponent]
    simp only [Nat.succ_ne_zero, ↓reduceDIte, zero_comp]
    erw [ιTotal_total_d_comp]
    rw [HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
    change 0 = A.d₁ (down ℕ) (i + 1 + 1) j n' ≫ totalToRowCokernelComponent A n' +
      A.d₂ (down ℕ) (i + 1 + 1) j n' ≫ totalToRowCokernelComponent A n'
    have hd₁ :
        A.d₁ (down ℕ) (i + 1 + 1) j n' ≫ totalToRowCokernelComponent A n' = 0 :=
      @rowD₁_notOneHorizontal_totalToRowCokernelComponent_eq_zero
        R _ A (i + 1 + 1) j n' (by omega)
    have hd₂ :
        A.d₂ (down ℕ) (i + 1 + 1) j n' ≫ totalToRowCokernelComponent A n' = 0 :=
      @rowD₂_positiveHorizontal_totalToRowCokernelComponent_eq_zero
        R _ A (i + 1 + 1) j n' (by omega)
    simpa [hd₁, hd₂]

/-- The canonical morphism from the total complex of `A` to the rowwise cokernel complex
`R(A)_•`. -/
noncomputable def totalToRowCokernel
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) :
    A.total (down ℕ) ⟶ rowCokernelComplex A where
  f := totalToRowCokernelComponent A
  comm' := totalToRowCokernel_comm A

/-- Helper for Chap10 Lemma 10 75 3: the row comparison map is natural in the bicomplex. -/
private theorem totalToRowCokernel_naturality
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)} (f : A ⟶ B) :
    HomologicalComplex₂.total.map f (down ℕ) ≫ totalToRowCokernel B =
      totalToRowCokernel A ≫ rowCokernelMap f := by
  -- It is enough to compare every component after precomposing with each total summand.
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  -- On a summand the totalized map is just the component of `f`; both row comparison maps
  -- then reduce to the same cokernel projection formula.
  simp only [HomologicalComplex.comp_f]
  dsimp [totalToRowCokernel, rowCokernelMap]
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
    erw [cokernelπ_rowCokernelMapComponent]
    rfl
  · rw [dif_neg hi, dif_neg hi]
    aesop_cat

/-- Helper for Chap10 Lemma 10 75 3: the degree-zero row augmentation kills the incoming
horizontal differential. -/
private theorem rowAugmentation_comp_zero
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (j : ℕ) :
    (rowComplex A j).d 1 0 ≫ (rowAugmentation A j).f 0 = 0 := by
  -- This is just the chain-map condition for `rowAugmentation` at degrees `1` and `0`.
  simpa using ((rowAugmentation A j).comm 1 0).symm

/-- Helper for Chap10 Lemma 10 75 3: row resolutions are exact in every positive horizontal
degree. -/
private theorem rowAugmentation_exactAt_succ
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) (j i : ℕ) :
    (rowComplex A j).ExactAt (i + 1) := by
  -- A row augmentation is a quasi-isomorphism, and the target single complex is exact away from
  -- degree zero, so the source row is exact in the matching positive degree.
  have hAt : QuasiIsoAt (rowAugmentation A j) (i + 1) :=
    (quasiIso_iff (rowAugmentation A j)).1 (hrows j) (i + 1)
  exact
    (quasiIsoAt_iff_exactAt' (rowAugmentation A j) (i + 1)
      (ChainComplex.exactAt_succ_single_obj (rowCokernelObject A j) i)).1 hAt

/-- Helper for Chap10 Lemma 10 75 3: row resolutions identify horizontal degree-zero homology
with the row cokernel and make the augmentation epimorphic. -/
private theorem rowAugmentation_exactAndEpi_zero
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) (j : ℕ) :
    (ShortComplex.mk ((rowComplex A j).d 1 0) ((rowAugmentation A j).f 0)
      (rowAugmentation_comp_zero A j)).Exact ∧ Epi ((rowAugmentation A j).f 0) := by
  -- At degree zero, the standard quasi-isomorphism criterion to a `single₀` complex gives exactly
  -- the short exactness and epimorphy needed for the bottom filtration quotient.
  have hAt : QuasiIsoAt (rowAugmentation A j) 0 :=
    (quasiIso_iff (rowAugmentation A j)).1 (hrows j) 0
  rw [ChainComplex.quasiIsoAt₀_iff] at hAt
  let S₁ := (shortComplexFunctor' (ModuleCat R) (down ℕ) 1 0 0).obj (rowComplex A j)
  let S₂ :=
    (shortComplexFunctor' (ModuleCat R) (down ℕ) 1 0 0).obj
      moduleSingle[rowCokernelObject A j]
  let φ := (shortComplexFunctor' (ModuleCat R) (down ℕ) 1 0 0).map (rowAugmentation A j)
  have hg₁ : S₁.g = 0 := by
    -- The right differential in the source short complex is the zero map `d 0 0`.
    simp [S₁]
    rfl
  have hf₂ : S₂.f = 0 := by
    -- The target single complex has no nonzero incoming differential in degree zero.
    simp [S₂]
    rfl
  have hg₂ : S₂.g = 0 := by
    -- The target single complex also has zero outgoing differential from degree zero.
    simp [S₂]
    rfl
  have hw : S₁.f ≫ φ.τ₂ = 0 := by
    -- The zero proof for the short complex is the left square of the short-complex morphism.
    rw [← φ.comm₁₂, hf₂, comp_zero]
  have hShort :
      (ShortComplex.mk S₁.f φ.τ₂ hw).Exact ∧ Epi φ.τ₂ := by
    simpa [φ] using (ShortComplex.quasiIso_iff_of_zeros' φ hg₁ hf₂ hg₂).1 hAt
  simpa [S₁, S₂, φ, rowAugmentation_comp_zero] using hShort

/-- Helper for Chap10 Lemma 10 75 3: the row-cokernel projection is surjective up to
refinements in horizontal degree `0`. -/
theorem rowCokernelProjection_refinement
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) (j : ℕ) {T : ModuleCat R}
    (y : T ⟶ rowCokernelObject A j) :
    ∃ (T' : ModuleCat R) (π : T' ⟶ T) (_ : Epi π)
      (z : T' ⟶ (A.X 0).X j), π ≫ y = z ≫ cokernel.π ((A.d 1 0).f j) := by
  -- Use the epimorphic degree-zero row augmentation and then unfold its degree-zero component.
  have hEpi : Epi ((rowAugmentation A j).f 0) :=
    (rowAugmentation_exactAndEpi_zero A hrows j).2
  obtain ⟨T', π, hπ, z, hz⟩ :=
    surjective_up_to_refinements_of_epi ((rowAugmentation A j).f 0) y
  exact ⟨T', π, hπ, z, by simpa [rowAugmentation] using hz⟩

/-- Helper for Chap10 Lemma 10 75 3: a degree-zero row cycle killed by the cokernel
projection is a horizontal boundary up to refinements. -/
theorem rowZeroBoundary_refinement
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) (j : ℕ) {T : ModuleCat R}
    (z : T ⟶ (A.X 0).X j) (hz : z ≫ cokernel.π ((A.d 1 0).f j) = 0) :
    ∃ (T' : ModuleCat R) (π : T' ⟶ T) (_ : Epi π)
      (w : T' ⟶ (A.X 1).X j), π ≫ z = w ≫ (A.d 1 0).f j := by
  -- Apply exactness of the short row complex at horizontal degree zero.
  have hExact :=
    (rowAugmentation_exactAndEpi_zero A hrows j).1
  obtain ⟨T', π, hπ, w, hw⟩ :=
    hExact.exact_up_to_refinements z (by simpa [rowAugmentation] using hz)
  exact ⟨T', π, hπ, w, by simpa [rowComplex, rowComplexFunctor] using hw⟩

/-- Helper for Chap10 Lemma 10 75 3: every positive horizontal row cycle is a boundary up to
refinements. -/
theorem rowPositiveBoundary_refinement
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) (j i : ℕ) {T : ModuleCat R}
    (z : T ⟶ (A.X (i + 1)).X j) (hz : z ≫ (A.d (i + 1) i).f j = 0) :
    ∃ (T' : ModuleCat R) (π : T' ⟶ T) (_ : Epi π)
      (w : T' ⟶ (A.X (i + 2)).X j), π ≫ z = w ≫ (A.d (i + 2) (i + 1)).f j := by
  -- Convert positive row exactness into the standard refinement form for chain complexes.
  have hExact : (rowComplex A j).ExactAt (i + 1) :=
    rowAugmentation_exactAt_succ A hrows j i
  have href :=
    (HomologicalComplex.exactAt_iff_exact_up_to_refinements
      (rowComplex A j) (i + 2) (i + 1) i
      (by simpa using (ChainComplex.prev ℕ (i + 1)))
      (by simpa using (ChainComplex.next_nat_succ i))).1 hExact
  obtain ⟨T', π, hπ, w, hw⟩ :=
    href z (by simpa [rowComplex, rowComplexFunctor] using hz)
  exact ⟨T', π, hπ, w, by simpa [rowComplex, rowComplexFunctor] using hw⟩

end
