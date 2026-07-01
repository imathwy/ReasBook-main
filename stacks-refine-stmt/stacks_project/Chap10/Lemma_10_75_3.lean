import Mathlib
import stacks_project.Chap10.Definition_10_71_2

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ ComplexShape

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

local notation "moduleSingle[" M "]" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) M

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

-- Proof sketch: compose two induced cokernel maps and use that the vertical differentials in the
-- columns square to zero.
/-- Consecutive differentials in the row-cokernel complex compose to zero. -/
private theorem rowCokernelDifferential_sq
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (j : ℕ) :
    rowCokernelDifferential A (j + 1) ≫ rowCokernelDifferential A j = 0 := sorry

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

-- Proof sketch: check the square with the induced cokernel maps in consecutive degrees using
-- commutativity of `f` with the vertical differentials; `ChainComplex.ofHom` extends this to a
-- chain map.
private theorem rowCokernelMapComponent_comm
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)} (f : A ⟶ B) (j : ℕ) :
    rowCokernelMapComponent f (j + 1) ≫ rowCokernelDifferential B j =
      rowCokernelDifferential A j ≫ rowCokernelMapComponent f j := sorry

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

-- Proof sketch: check the identity after precomposing with each summand inclusion `A_{i,j} →
-- Tot(A)_n`. Only the `(i, j) = (0, n)` and `(1, n')` summands contribute, and the remaining
-- relation is exactly the defining compatibility of `cokernel.map`.
/-- The canonical degreewise maps from the total complex to `R(A)_•` commute with the
differentials. -/
private theorem totalToRowCokernel_comm
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (n n' : ℕ) (_ : (down ℕ).Rel n n') :
    totalToRowCokernelComponent A n ≫ (rowCokernelComplex A).d n n' =
      (A.total (down ℕ)).d n n' ≫ totalToRowCokernelComponent A n' := by
  sorry

/-- The canonical morphism from the total complex of `A` to the rowwise cokernel complex
`R(A)_•`. -/
noncomputable def totalToRowCokernel
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) :
    A.total (down ℕ) ⟶ rowCokernelComplex A where
  f := totalToRowCokernelComponent A
  comm' := totalToRowCokernel_comm A

-- Proof sketch: filter the total complex by horizontal degree. The associated graded pieces are
-- the rows of `A`, and the induced augmentation on the `j`-th graded piece is exactly
-- `rowAugmentation A j`. Since each row augmentation is a quasi-isomorphism by hypothesis, the
-- total comparison map is a quasi-isomorphism.
/-- If the rows of `A` resolve `R(A)_•`, then the canonical map from `Tot(A)` to `R(A)_•` is a
quasi-isomorphism. -/
theorem totalToRowCokernel_quasiIso
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) :
    QuasiIso (totalToRowCokernel A) := by
  sorry

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

-- Proof sketch: this is the same computation as for `totalToRowCokernel_comm`, now selecting the
-- `(n, 0)` summand instead of `(0, n)`.
/-- The canonical degreewise maps from the total complex to `U(A)_•` commute with the
differentials. -/
private theorem totalToColumnCokernel_comm
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (n n' : ℕ) (_ : (down ℕ).Rel n n') :
    totalToColumnCokernelComponent A n ≫ (columnCokernelComplex A).d n n' =
      (A.total (down ℕ)).d n n' ≫ totalToColumnCokernelComponent A n' := by
  sorry

/-- The canonical morphism from the total complex of `A` to the columnwise cokernel complex
`U(A)_•`. -/
noncomputable def totalToColumnCokernel
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) :
    A.total (down ℕ) ⟶ columnCokernelComplex A where
  f := totalToColumnCokernelComponent A
  comm' := totalToColumnCokernel_comm A

-- Proof sketch: apply the previous rowwise argument to the flipped bicomplex `A.flip`; its
-- rowwise cokernel complex is definitionally `U(A)_•`.
/-- If the columns of `A` resolve `U(A)_•`, then the canonical map from `Tot(A)` to `U(A)_•` is a
quasi-isomorphism. -/
theorem totalToColumnCokernel_quasiIso
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hcols : RowsResolve A.flip) :
    QuasiIso (totalToColumnCokernel A) := by
  sorry

/-- Lemma 10.75.3: if the rows of `A` resolve `R(A)_•` and the columns resolve `U(A)_•`, then
their homology groups are canonically isomorphic. -/
noncomputable def resolved_double_complex_homology_comparison
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) (hcols : RowsResolve A.flip) (i : ℕ) :
    (rowCokernelComplex A).homology i ≅ (columnCokernelComplex A).homology i :=
  letI : QuasiIso (totalToRowCokernel A) := totalToRowCokernel_quasiIso A hrows
  letI : QuasiIso (totalToColumnCokernel A) := totalToColumnCokernel_quasiIso A hcols
  (isoOfQuasiIsoAt (totalToRowCokernel A) i).symm ≪≫
    isoOfQuasiIsoAt (totalToColumnCokernel A) i

/-- The homology comparison of Lemma 10.75.3 is natural in morphisms of resolved double
complexes. -/
theorem resolved_double_complex_homology_comparison_naturality
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)}
    (hrowsA : RowsResolve A) (hcolsA : RowsResolve A.flip)
    (hrowsB : RowsResolve B) (hcolsB : RowsResolve B.flip)
    (f : A ⟶ B) (i : ℕ) :
    homologyMap (rowCokernelMap f) i ≫
        (resolved_double_complex_homology_comparison B hrowsB hcolsB i).hom =
      (resolved_double_complex_homology_comparison A hrowsA hcolsA i).hom ≫
        homologyMap (columnCokernelMap f) i := by
  sorry

end
