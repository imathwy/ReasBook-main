import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_75_3 (from Chap10) -/
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
  -- TODO: precompose with each `ιTotal`, split into the `(0,n)`, `(1,n')`, and `i ≥ 2`
  -- summands, and rewrite `total_d` via `ι_D₁`/`ι_D₂`. The remaining blocker is stabilizing the
  -- arithmetic/shape rewrites from `π (i,j) = n` and `n' + 1 = n` into the exact hypotheses
  -- needed by `d₁_eq`, `d₁_eq_zero`, `d₂_eq`, and `d₂_eq_zero`.
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
  -- TODO: implement the source-proof filtration argument on total degree / horizontal degree.
  -- The current file now has the cokernel interface established, but the quasi-isomorphism step
  -- still needs the structural filtered-complex comparison.
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
  -- TODO: derive this from the row statement on `A.flip` through `A.totalFlipIso (down ℕ)`
  -- instead of duplicating the summand-by-summand calculation.
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
  -- TODO: transport `totalToRowCokernel_quasiIso` across the flip symmetry
  -- `A.totalFlipIso (down ℕ)` and the identification `rowCokernelComplex A.flip = U(A)_•`.
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
  -- TODO: once both comparison maps from the total complex are quasi-isomorphisms, expand the
  -- defining composite and cancel the quasi-isomorphism factors using `homologyMap_comp`.
  sorry

end

/-! ### Remark_10_75_4 (from Chap10) -/
/-!
`Remark 10.75.4` exists in the source data (`tag 00M2`) and sits between
`Lemma 10.75.3` and `Lemma 10.75.5`. The repository was missing the target
module path, so we keep the canonical target filename and provide the module
stub here instead of remapping the item onto a different remark.
-/

/- Domain-style sampling for Remark 10.75.4:
- primary domain: homological algebra of double complexes and sign conventions in comparison
  isomorphisms;
- sampled owner declarations:
  `resolved_double_complex_homology_comparison`,
  `resolved_double_complex_homology_comparison_naturality`;
- best owner abstraction: the source-facing mathematical object under discussion is the comparison
  isomorphism `resolved_double_complex_homology_comparison` from Lemma `10.75.3`;
- primitive data: a resolved first-quadrant double complex together with the row and column
  resolution hypotheses;
- derived API: naturality and later sign-sensitive variants.

Source/core/bridge triage:
- `source-facing`: the comparison isomorphism constructed in Lemma `10.75.3`;
- `core/canonical`: that same named comparison isomorphism in the chapter API;
- `bridge/view`: later sign bookkeeping for compatibilities of diagrams built from this
  comparison.

This remark is editorial rather than theorem-shaped: it says that the chosen comparison isomorphism
is only the correct one up to sign conventions, and that the chapter will use the specific
comparison already constructed. The faithful statement-stage rendering is therefore a direct recall
of that comparison, not a new wrapper theorem about signs. -/

/- Remark 10.75.4: the homology comparison isomorphism constructed in Lemma `10.75.3` is the
chosen comparison to use in the chapter, even though the sign conventions in homological algebra
mean that this is only the “correct” comparison up to signs. -/
recall resolved_double_complex_homology_comparison

/-! ### Lemma_10_75_5 (from Chap10) -/
noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open BraidedCategory

universe v u

section

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

private lemma tensoringLeft_map_comp_tensorLeftIso {M N : C} (f : M ⟶ N) :
    (tensoringLeft C).map f ≫ (tensorLeftIsoTensorRight N).hom =
      (tensorLeftIsoTensorRight M).hom ≫ (tensoringRight C).map f := by
  ext X
  simpa using braiding_naturality_left f X

private lemma tensoringRight_map_comp_tensorLeftIso_inv {M N : C} (f : M ⟶ N) :
    (tensoringRight C).map f ≫ (tensorLeftIsoTensorRight N).inv =
      (tensorLeftIsoTensorRight M).inv ≫ (tensoringLeft C).map f := by
  ext X
  simpa using braiding_inv_naturality_left f X

end

section

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C] [HasProjectiveResolutions C]

private noncomputable def torFlipComponentIso (i : ℕ) (M : C) :
    ((Tor C i).obj M) ≅ ((Functor.flip (Tor' C i)).obj M) where
  hom := by
    simpa [Tor'] using (NatTrans.leftDerived ((tensorLeftIsoTensorRight M).hom) i)
  inv := by
    simpa [Tor'] using (NatTrans.leftDerived ((tensorLeftIsoTensorRight M).inv) i)
  hom_inv_id := by
    ext X
    change ((NatTrans.leftDerived ((tensorLeftIsoTensorRight M).hom) i) ≫
        NatTrans.leftDerived ((tensorLeftIsoTensorRight M).inv) i).app X =
      𝟙 _
    rw [← NatTrans.leftDerived_comp]
    simp
  inv_hom_id := by
    ext X
    change ((NatTrans.leftDerived ((tensorLeftIsoTensorRight M).inv) i) ≫
        NatTrans.leftDerived ((tensorLeftIsoTensorRight M).hom) i).app X =
      𝟙 _
    rw [← NatTrans.leftDerived_comp]
    simp

/-- Lemma 10.75.5: for every `i ≥ 0`, the bifunctors
`(M, N) ↦ Tor_i(M, N)` and `(M, N) ↦ Tor_i(N, M)` on a braided monoidal abelian category are
canonically isomorphic. -/
noncomputable def tor_flip_iso (i : ℕ) :
    Tor C i ≅ Functor.flip (Tor' C i) where
  hom :=
    { app := fun M ↦ (torFlipComponentIso C i M).hom
      naturality := by
        intro M N f
        ext X
        change ((NatTrans.leftDerived ((tensoringLeft C).map f) i) ≫
              NatTrans.leftDerived ((tensorLeftIsoTensorRight N).hom) i).app X =
          ((NatTrans.leftDerived ((tensorLeftIsoTensorRight M).hom) i) ≫
                NatTrans.leftDerived ((tensoringRight C).map f) i).app X
        rw [← NatTrans.leftDerived_comp, ← NatTrans.leftDerived_comp,
          tensoringLeft_map_comp_tensorLeftIso] }
  inv :=
    { app := fun M ↦ (torFlipComponentIso C i M).inv
      naturality := by
        intro M N f
        ext X
        change ((NatTrans.leftDerived ((tensoringRight C).map f) i) ≫
              NatTrans.leftDerived ((tensorLeftIsoTensorRight N).inv) i).app X =
          ((NatTrans.leftDerived ((tensorLeftIsoTensorRight M).inv) i) ≫
                NatTrans.leftDerived ((tensoringLeft C).map f) i).app X
        rw [← NatTrans.leftDerived_comp, ← NatTrans.leftDerived_comp,
          tensoringRight_map_comp_tensorLeftIso_inv] }
  hom_inv_id := by
    ext M X
    exact (torFlipComponentIso C i M).hom_inv_id_app X
  inv_hom_id := by
    ext M X
    exact (torFlipComponentIso C i M).inv_hom_id_app X

/-- The component of `tor_flip_iso` at a pair `(M, N)` is an isomorphism. -/
theorem isIso_tor_flip_iso_app_app (i : ℕ) (M N : C) :
    IsIso (((tor_flip_iso C i).app M).hom.app N) := by
  infer_instance

end

/-! ### Remark_10_75_6 (from Chap10) -/
noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ModuleCat.MonoidalCategory

universe u

section

variable {R : Type u} [CommRing R]

/-- In degree `0`, the diagonal component of the symmetry from Lemma `10.75.5` identifies,
via the canonical degree-`0` comparisons with tensor product in the two variables, with the usual
tensor-product braiding on `M ⊗[R] M`. -/
theorem tor_zero_self_flip_via_tensor_braiding (M : ModuleCat R) :
    ((tensorLeft M).leftDerivedZeroIsoSelf.inv.app M) ≫
        ((tor_flip_iso (ModuleCat R) 0).app M).hom.app M ≫
        (tensorRight M).fromLeftDerivedZero.app M =
      (β_ M M).hom := sorry

end

section

variable {k : Type u} [Field k]

private theorem rankTwoTensor_swap_ne :
    (TensorProduct.tmul k ((1 : k), 0) ((0 : k), 1) : TensorProduct k (k × k) (k × k)) ≠
      TensorProduct.tmul k ((0 : k), 1) ((1 : k), 0) := by
  intro h
  let fst : (k × k) →ₗ[k] k := LinearMap.fst k k k
  let snd : (k × k) →ₗ[k] k := LinearMap.snd k k k
  have h' := congr_arg
    ((TensorProduct.map fst snd) :
      TensorProduct k (k × k) (k × k) →ₗ[k] TensorProduct k k k) h
  simp [fst, snd] at h'

/-- For the free rank-`2` module over a field, the diagonal symmetry on `Tor₀` is not the
identity. -/
theorem tor_zero_self_flip_not_identity_on_free_rankTwo :
    ((tensorLeft (ModuleCat.of k (k × k))).leftDerivedZeroIsoSelf.inv.app (ModuleCat.of k (k × k)))
        ≫
        ((tor_flip_iso (ModuleCat k) 0).app (ModuleCat.of k (k × k))).hom.app
          (ModuleCat.of k (k × k))
        ≫
        (tensorRight (ModuleCat.of k (k × k))).fromLeftDerivedZero.app (ModuleCat.of k (k × k)) ≠
      𝟙 ((ModuleCat.of k (k × k)) ⊗ (ModuleCat.of k (k × k))) := by
  let M : ModuleCat k := ModuleCat.of k (k × k)
  rw [tor_zero_self_flip_via_tensor_braiding M]
  intro hβ
  have hxy := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hβ)
    (TensorProduct.tmul k ((1 : k), 0) ((0 : k), 1))
  have hswap :
      TensorProduct.tmul k ((0 : k), 1) ((1 : k), 0) =
        (TensorProduct.tmul k ((1 : k), 0) ((0 : k), 1) : TensorProduct k (k × k) (k × k)) := by
    simpa [M] using hxy
  exact rankTwoTensor_swap_ne hswap.symm

/-- Remark 10.75.6: the canonical endomorphism of `Tor_i^R(M, M)` coming from the symmetry of
Lemma `10.75.5` is generally not the identity after the canonical degree-`0` identifications with
tensor product; this already fails in degree `0`. -/
theorem tor_zero_self_flip_not_universally_identity :
    ¬ ∀ M : ModuleCat k,
      ((tensorLeft M).leftDerivedZeroIsoSelf.inv.app M) ≫
          ((tor_flip_iso (ModuleCat k) 0).app M).hom.app M ≫
          (tensorRight M).fromLeftDerivedZero.app M =
        𝟙 (M ⊗ M) := by
  intro h
  exact tor_zero_self_flip_not_identity_on_free_rankTwo (h (ModuleCat.of k (k × k)))

end

/-! ### Lemma_10_75_7 (from Chap10) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open ChainComplex
open HomologicalComplex

universe u

namespace ModuleCat

section

variable {R : Type u} [CommRing R]
variable (M N : ModuleCat R) [Module.Finite R M]

/-- Helper for Lemma 10.75.7: `Tor` in degree `p` is computed by the homology of a finite free
resolution of the second variable tensored with the first variable. -/
noncomputable def tor_iso_homology_tensorized_resolution
    {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj N)
    [ChainComplex.IsFiniteFreeResolution π] (p : ℕ) :
    (((Tor (ModuleCat R) p).obj M).obj N) ≅
      ((((tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        F).homology p := by
  -- Convert the chosen finite free resolution into the projective resolution used by `Tor`.
  simpa [Tor] using
    (ChainComplex.IsFreeResolution.toProjectiveResolution (M := N) π).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat R)).obj M) p

/-- Helper for Lemma 10.75.7: tensoring a finite free resolution with a finite module stays
termwise finite. -/
lemma tensorized_resolution_termwise_finite
    {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj N)
    [ChainComplex.IsFiniteFreeResolution π] (n : ℕ) :
    Module.Finite R
      (((((tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          F).X n) := by
  -- The resolution gives finiteness of `F_n`, and tensor products of finite modules stay finite.
  letI : Module.Finite R (F.X n) := ChainComplex.IsFiniteFreeResolution.finite π n
  simpa using
    (Module.Finite.tensorProduct (R := R) (M := (M : Type u)) (N := (F.X n : Type u)))

/-- Helper for Lemma 10.75.7: the homology of a termwise finite chain complex of modules is
finite. -/
lemma homology_finite_of_termwise_finite
    [IsNoetherianRing R] (C : ChainComplex (ModuleCat R) ℕ) [∀ n, Module.Finite R (C.X n)]
    (p : ℕ) :
    Module.Finite R (C.homology p) := by
  -- The opcycles are finite because they are a quotient of the finite module `C.X p`.
  letI : Module.Finite R (C.opcycles p) := by
    exact
      Module.Finite.of_surjective (C.pOpcycles p).hom ((ModuleCat.epi_iff_surjective _).1
        inferInstance)
  -- The homology is finite because it injects into the finite module of opcycles.
  exact
    Module.Finite.of_injective (C.homologyι p).hom ((ModuleCat.mono_iff_injective _).1
      inferInstance)

section

variable [IsNoetherianRing R]
variable [Module.Finite R N]

-- Proof sketch: choose a projective resolution of `N` by finite free modules using
-- `module_exists_finite_free_resolution`; tensor it with `M`, so every term remains a finite
-- module by `Module.Finite.tensorProduct`; then identify `Tor` as the homology of this complex and
-- use that subquotients of finite modules over a Noetherian ring are finite.
/-- Library-facing form of Lemma 10.75.7 (Tag `0AZ4`): over a Noetherian commutative ring, the
`p`-th `Tor` of two finite modules is finite. -/
theorem finite_tor (p : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) p).obj M).obj N) := by
  -- Resolve `N` by finite free modules exactly as in Lemma 10.71.1.
  rcases module_exists_finite_free_resolution (R := R) (M := N) with ⟨F, π, hπ⟩
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let T :=
    ((((tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj F)
  let e : (((Tor (ModuleCat R) p).obj M).obj N) ≅ T.homology p :=
    tor_iso_homology_tensorized_resolution (R := R) (M := M) (N := N) π p
  -- Every term of the tensorized resolution is finite.
  letI (n : ℕ) : Module.Finite R (T.X n) := by
    simpa [T] using tensorized_resolution_termwise_finite (R := R) (M := M) (N := N) π n
  -- The homology is therefore finite, and the comparison isomorphism transports finiteness back.
  letI : Module.Finite R (T.homology p) := homology_finite_of_termwise_finite (R := R) T p
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- Typeclass support for finiteness of `Tor_p^R(M, N)` under the hypotheses of
`ModuleCat.finite_tor`. -/
instance (p : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) p).obj M).obj N) :=
  finite_tor M N p

end

end

end ModuleCat

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (M N : ModuleCat R) [Module.Finite R M] [Module.Finite R N]

/-- Lemma 10.75.7 (Tag 0AZ4): if `R` is Noetherian and `M`, `N` are finite `R`-modules, then
`Tor_p^R(M, N)` is a finite `R`-module for every `p`. -/
@[stacks 0AZ4]
theorem Lemma_10_75_7 (p : ℕ) :
    Module.Finite R (((Tor (ModuleCat R) p).obj M).obj N) :=
  ModuleCat.finite_tor M N p

end

/-! ### Lemma_10_75_8 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits Equiv
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

set_option quotPrecheck false in
local notation "Tor[" i "](" N ")" => (((Tor (ModuleCat R) i).obj (ModuleCat.of R M)).obj N)
set_option quotPrecheck false in
local notation "Tor₁(" N ")" => Tor[1](N)
set_option quotPrecheck false in
local notation "Tor₁[" R "](" N ")" => Tor[1](ModuleCat.of R N)

/- Domain triage:
- primary domain: commutative algebra of flat modules and Tor-vanishing criteria;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Module.Flat.iff_rTensor_injective'`,
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`,
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`;
- best owner abstraction: the canonical owner is `Module.Flat`, with the chapter-local Tor/kernel
  bridge supplying the quotient-by-ideal reformulations;
- primitive data: the commutative ring `R` and the `R`-module `M`;
- derived API: the five-way `List.TFAE` packaging of flatness, higher Tor-vanishing, and the two
  quotient-ideal tests.

Source/core/bridge triage:
- `source-facing`: the Stacks-style five-way flatness criterion recorded as a `TFAE`;
- `core/canonical`: `Module.Flat` and the owner theorems `Module.Flat.iff_rTensor_injective'` and
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`;
- `bridge/view`: `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`, which converts the
  quotient-side `Tor₁` condition to the canonical tensor-kernel test.
-/

-- Proof sketch: use the derived-functor definition of `Tor`. If `M` is flat, then tensoring with
-- `M` is exact, so all higher left-derived functors vanish. The implications from vanishing for all
-- `i > 0` to the special `Tor₁` vanishing conditions are immediate. For the converse, apply the
-- six-term exact sequence of Lemma `10.75.2` to `0 → I → R → R/I → 0`; vanishing of
-- `Tor₁^R(M, R/I)` makes `I ⊗[R] M → M` injective, and Lemma `10.39.5` then yields flatness.
/-- Lemma 10.75.8: for an `R`-module `M`, the following are equivalent: `M` is flat over `R`; all
higher functors `Tor_i^R(M, -)` for `i > 0` vanish; `Tor_1^R(M, -)` vanishes; `Tor_1^R(M, R/I)`
vanishes for every ideal `I`; and it suffices to check this for finitely generated ideals `I`. -/
theorem flat_tfae_tor_vanishing_criteria :
    List.TFAE
      [ Module.Flat R M,
        ∀ i : ℕ, 0 < i → ∀ N : ModuleCat R,
          IsZero (Tor[i](N)),
        ∀ N : ModuleCat R, IsZero (Tor₁(N)),
        ∀ I : Ideal R,
          IsZero (Tor₁[R](R ⧸ I)),
        ∀ I : Ideal R, I.FG →
          IsZero (Tor₁[R](R ⧸ I)) ] := by
  tfae_have 1 → 2 := by
    intro hflat i hi N
    sorry
  tfae_have 2 → 3 := by
    intro h N
    simpa using h 1 (Nat.succ_pos 0) N
  tfae_have 3 → 4 := by
    intro h I
    simpa using h (ModuleCat.of R (R ⧸ I))
  tfae_have 4 → 5 := by
    intro h I _
    exact h I
  tfae_have 5 → 1 := by
    intro hTor
    rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
    intro I hI
    let μ :
        I ⊗[R] M →ₗ[R] M :=
      TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
    have htor :
        Tor₁[R](R ⧸ I) ≃ₗ[R] LinearMap.ker μ :=
      tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module I
    have hker_subsingleton : Subsingleton (LinearMap.ker μ) := by
      exact (subsingleton_congr htor.toEquiv).mp
        ((ModuleCat.isZero_iff_subsingleton).1 (hTor I hI))
    exact LinearMap.ker_eq_bot.mp <| Submodule.subsingleton_iff_eq_bot.mp hker_subsingleton
  tfae_finish

end

/-! ### Remark_10_75_9 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

universe u

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

set_option quotPrecheck false in
notation "Tor₁[" R "](" M ", " N ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R N))

/- Domain triage:
- primary domain: the low-degree `Tor₁`/tensor exact sequence for a short exact sequence of
  `R`-modules, specialized to `0 → I → R → R ⧸ I → 0`;
- sampled owner declarations of the same kind:
  `CategoryTheory.Tor`,
  `ModuleCat.torTensorSixTermSequence_exact`,
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`,
  `LinearMap.lid_comp_rTensor`;
- best owner abstraction: the core/canonical owners are `CategoryTheory.Tor (ModuleCat R) 1` for
  the homological term, surfaced below as `Tor₁[R](M, N)`, and the canonical tensor multiplication
  map
  `TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)`;
- primitive data: the ring `R`, the `R`-module `M`, and the ideal `I`;
- derived API: the comparison equivalence identifying the specific `Tor₁` term with the kernel of
  the canonical map.

Source/core/bridge triage:
- `source-facing`: the Stacks remark identifying `Tor₁^R(M, R/I)` with the kernel of
  `I ⊗[R] M → M`;
- `core/canonical`: `CategoryTheory.Tor`, `ModuleCat.torTensorSixTermSequence_exact`,
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`, and `LinearMap.lid_comp_rTensor`;
- `bridge/view`: the comparison equivalence below. This should be exposed directly as the canonical
  object, not wrapped in `Nonempty`.
-/

-- Proof sketch: apply the six-term exact sequence for `0 → I → R → R/I → 0`; after identifying
-- `R ⊗[R] M` with `M` via `TensorProduct.lid`, exactness identifies `Tor₁^R(M, R/I)` with the
-- kernel of the canonical multiplication map `I ⊗[R] M → M`.
/-- Remark 10.75.9: for an ideal `I`, the proof of Lemma 10.75.8 identifies
`Tor₁^R(M, R/I)` with the kernel of the canonical map `I ⊗[R] M → M`. -/
noncomputable def tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (I : Ideal R) :
    Tor₁[R](M, R ⧸ I) ≃ₗ[R]
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)) := by
  let μ : I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  change Tor₁[R](M, R ⧸ I) ≃ₗ[R] LinearMap.ker μ
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk I.subtype I.mkQ (by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa using (LinearMap.exact_subtype_mkQ I)
    · exact (ModuleCat.mono_iff_injective _).2 I.injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).2 I.mkQ_surjective
  let T := ModuleCat.torTensorSixTermSequence (ModuleCat.of R M) hS
  have hT : T.Exact := ModuleCat.torTensorSixTermSequence_exact (ModuleCat.of R M) hS
  have hTorR :
      IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R R)) := by
    simpa using
      CategoryTheory.isZero_Tor_succ_of_projective
        (ModuleCat R) (ModuleCat.of R M) (ModuleCat.of R R) 0
  have hmap12 : T.map' 1 2 = 0 := hTorR.eq_of_src _ _
  have hmono23 : Mono (T.map' 2 3) := by
    have : Mono (T.sc hT.toIsComplex 1).g := (hT.exact 1).mono_g (by simpa using hmap12)
    simpa using this
  have hExact23 : Function.Exact (T.map' 2 3).hom (T.map' 3 4).hom := by
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (T.sc hT.toIsComplex 2)).1
        (hT.exact 2)
  have hmap34' : T.map' 3 4 = MonoidalCategoryStruct.whiskerLeft (ModuleCat.of R M) S.f := by
    dsimp [T]
    unfold ModuleCat.torTensorSixTermSequence ComposableArrows.mk₅ ComposableArrows.mk₄
    rfl
  have hmap34 : (T.map' 3 4).hom = I.subtype.lTensor M := by
    rw [hmap34']
    change ModuleCat.Hom.hom
        (MonoidalCategoryStruct.whiskerLeft (ModuleCat.of R M) (ModuleCat.ofHom I.subtype)) =
      I.subtype.lTensor M
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  have hμ :
      μ.comp (TensorProduct.comm R M I).toLinearMap =
        (TensorProduct.rid R M).toLinearMap.comp (T.map' 3 4).hom := by
    have hcommLid :
        (TensorProduct.lid R M).toLinearMap.comp (TensorProduct.comm R M R).toLinearMap =
          (TensorProduct.rid R M).toLinearMap := by
      exact congrArg LinearEquiv.toLinearMap TensorProduct.comm_trans_lid
    dsimp [μ]
    rw [← LinearMap.lid_comp_rTensor]
    change
      (TensorProduct.lid R M).toLinearMap.comp
          ((I.subtype.rTensor M).comp (TensorProduct.comm R M I).toLinearMap) =
        (TensorProduct.rid R M).toLinearMap.comp (T.map' 3 4).hom
    rw [LinearMap.rTensor_comp_comm]
    change
      (TensorProduct.lid R M).toLinearMap.comp
          ((TensorProduct.comm R M R).toLinearMap.comp (I.subtype.lTensor M)) =
        (TensorProduct.rid R M).toLinearMap.comp (T.map' 3 4).hom
    rw [hmap34, ← LinearMap.comp_assoc, hcommLid]
    rfl
  have hμ_exact :
      Function.Exact
        ((TensorProduct.comm R M I).toLinearMap.comp (T.map' 2 3).hom)
        μ := by
    let e₁ : ↑(T.obj ⟨2, by decide⟩) ≃ₗ[R] ↑(T.obj ⟨2, by decide⟩) := LinearEquiv.refl R _
    let e₂ : ↑(T.obj ⟨3, by decide⟩) ≃ₗ[R] I ⊗[R] M := by
      change M ⊗[R] I ≃ₗ[R] I ⊗[R] M
      exact TensorProduct.comm R M I
    let e₃ : ↑(T.obj ⟨4, by decide⟩) ≃ₗ[R] M := by
      change M ⊗[R] R ≃ₗ[R] M
      exact TensorProduct.rid R M
    have h12 :
        ((TensorProduct.comm R M I).toLinearMap.comp (T.map' 2 3).hom) ∘ₗ e₁.toLinearMap =
          e₂.toLinearMap ∘ₗ (T.map' 2 3).hom := by
      ext x
      rfl
    have h23 :
        μ ∘ₗ e₂.toLinearMap =
          e₃.toLinearMap ∘ₗ (T.map' 3 4).hom := by
      simpa [LinearMap.comp_assoc] using hμ
    exact (Function.Exact.iff_of_ladder_linearEquiv h12 h23).2 hExact23
  have hμ_injective :
      Function.Injective ((TensorProduct.comm R M I).toLinearMap.comp (T.map' 2 3).hom) :=
    (TensorProduct.comm R M I).injective.comp ((ModuleCat.mono_iff_injective _).1 hmono23)
  let hker :
      IsLimit
        (KernelFork.ofι
          (ModuleCat.ofHom ((TensorProduct.comm R M I).toLinearMap.comp (T.map' 2 3).hom))
          (ModuleCat.hom_ext hμ_exact.linearMap_comp_eq_zero)) :=
    ModuleCat.isLimitKernelFork
      (ModuleCat.ofHom ((TensorProduct.comm R M I).toLinearMap.comp (T.map' 2 3).hom))
      (ModuleCat.ofHom μ)
      hμ_exact hμ_injective
  exact
    (((limit.isoLimitCone ⟨_, hker⟩).symm ≪≫
      ModuleCat.kernelIsoKer (ModuleCat.ofHom μ)).toLinearEquiv)

end
