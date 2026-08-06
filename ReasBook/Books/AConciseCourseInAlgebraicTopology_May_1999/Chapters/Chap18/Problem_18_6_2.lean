module

public import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.GroupCohomologyMonoidal
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RepresentationTheory.Rep.Basic

public section

open CategoryTheory MonoidalCategory

noncomputable section

-- Semantic recall via `lean_leansearch`: `groupCohomologyIsoExt` is the canonical owner for the
-- `H^*(K(π, 1); A) ≃ Ext^*_{ℤ[π]}(ℤ, A)` identification, while `Rep.barComplex`,
-- `Rep.standardComplex`, and `Rep.barComplex.isoStandardComplex` expose the diagonal-resolution
-- chain models available in the current environment.

variable {π : Type} [Group π]

/- Problem 18.6.2 (1): the canonical comparison identifying `groupCohomology A n` with
`Ext^n_{ℤ[π]}(ℤ, A)` is `groupCohomologyIsoExt A n`. -/
#check groupCohomologyIsoExt

/- The `n`th term of the standard resolution of the trivial `ℤ`-linear `π`-representation is
canonically `Rep.ofMulAction ℤ π (Fin (n + 1) → π)` via `Rep.standardComplex.xIso ℤ π n`. -/
#check Rep.standardComplex.xIso

/-- The cochain complex `Hom(Rep.standardComplex ℤ π, A)` computing group cohomology from the
standard resolution. -/
def diagonalStandardCochainComplex (A : Rep ℤ π) : CochainComplex (ModuleCat ℤ) ℕ :=
  let _ : CategoryTheory.Linear ℤ (Rep ℤ π) := Rep.instLinear;
  (Rep.standardResolution ℤ π).complex.linearYonedaObj ℤ A

/-- Comparison isomorphism from `groupCohomology A n` to the cohomology of the diagonal standard
complex `(Rep.standardComplex ℤ π).linearYonedaObj ℤ A`. -/
def groupCohomologyIsoDiagonalStandardComplex (A : Rep ℤ π) (n : ℕ) :
    groupCohomology A n ≅ (diagonalStandardCochainComplex A).homology n :=
  groupCohomologyIso A n (Rep.standardResolution ℤ π)

/-- The forward comparison map from `groupCohomology A n` to the cohomology of the diagonal
standard-resolution model. -/
def groupCohomologyToDiagonalStandardComplex (A : Rep ℤ π) (n : ℕ) :
    groupCohomology A n ⟶ (diagonalStandardCochainComplex A).homology n :=
  (groupCohomologyIsoDiagonalStandardComplex A n).hom

/-- The inverse comparison map from the diagonal standard-resolution model back to
`groupCohomology A n`. -/
def diagonalStandardComplexToGroupCohomology (A : Rep ℤ π) (n : ℕ) :
    (diagonalStandardCochainComplex A).homology n ⟶ groupCohomology A n :=
  (groupCohomologyIsoDiagonalStandardComplex A n).inv

/-- Bilinear products on the graded cohomology groups `groupCohomology A n`. -/
def GroupCohomologyProduct (A : Rep ℤ π) : Type _ :=
  ∀ p q : ℕ,
    groupCohomology A p ⊗ groupCohomology A q ⟶ groupCohomology A (p + q)

/-- Bilinear products on the diagonal standard-resolution cohomology model for `A`. -/
def DiagonalStandardComplexProduct (A : Rep ℤ π) : Type _ :=
  ∀ p q : ℕ,
    (diagonalStandardCochainComplex A).homology p ⊗
      (diagonalStandardCochainComplex A).homology q ⟶
      (diagonalStandardCochainComplex A).homology (p + q)

/-- Tensor comparison induced by `groupCohomologyIsoDiagonalStandardComplex` in bidegree
`(p, q)`. -/
def groupCohomologyIsoDiagonalStandardComplexTensor (A : Rep ℤ π) (p q : ℕ) :
    groupCohomology A p ⊗ groupCohomology A q ⟶
      (diagonalStandardCochainComplex A).homology p ⊗
        (diagonalStandardCochainComplex A).homology q :=
  groupCohomologyToDiagonalStandardComplex A p ⊗ₘ
    groupCohomologyToDiagonalStandardComplex A q

/-- Compatibility of a product on the diagonal standard-resolution model with a chosen product on
`groupCohomology A` under the comparison isomorphism
`groupCohomologyIsoDiagonalStandardComplex`. -/
def diagonalStandardComplexProductCompatible
    (A : Rep ℤ π) (cupProduct : GroupCohomologyProduct A)
    (diagonalProduct : DiagonalStandardComplexProduct A) :
    Prop :=
  ∀ p q : ℕ,
    CommSq
      (groupCohomologyIsoDiagonalStandardComplexTensor A p q)
      (cupProduct p q)
      (diagonalProduct p q)
      (groupCohomologyToDiagonalStandardComplex A (p + q))

/-- Bilinear products on the terms of the standard-resolution cochain complex
`(Rep.standardComplex ℤ π).linearYonedaObj ℤ A`. -/
def DiagonalStandardComplexCochainProduct (A : Rep ℤ π) : Type _ :=
  ∀ p q : ℕ,
    (diagonalStandardCochainComplex A).X p ⊗
      (diagonalStandardCochainComplex A).X q ⟶
      (diagonalStandardCochainComplex A).X (p + q)

/-- Bilinear products on the cocycle objects of the standard-resolution cochain complex
`(Rep.standardComplex ℤ π).linearYonedaObj ℤ A`. -/
def DiagonalStandardComplexCycleProduct (A : Rep ℤ π) : Type _ :=
  ∀ p q : ℕ,
    (diagonalStandardCochainComplex A).cycles p ⊗
      (diagonalStandardCochainComplex A).cycles q ⟶
      (diagonalStandardCochainComplex A).cycles (p + q)

/-- The cycle inclusion of the diagonal standard-resolution cochain complex in degree `n`. -/
def diagonalStandardComplexCycleInclusion (A : Rep ℤ π) (n : ℕ) :
    (diagonalStandardCochainComplex A).cycles n ⟶ (diagonalStandardCochainComplex A).X n :=
  (diagonalStandardCochainComplex A).iCycles n

/-- Tensor comparison induced by the cycle inclusions `iCycles` in bidegree `(p, q)`. -/
def diagonalStandardComplexCyclesTensorInclusion (A : Rep ℤ π) (p q : ℕ) :
    (diagonalStandardCochainComplex A).cycles p ⊗
      (diagonalStandardCochainComplex A).cycles q ⟶
      (diagonalStandardCochainComplex A).X p ⊗
        (diagonalStandardCochainComplex A).X q :=
  diagonalStandardComplexCycleInclusion A p ⊗ₘ diagonalStandardComplexCycleInclusion A q

/-- A cochain-level product on `(Rep.standardComplex ℤ π).linearYonedaObj ℤ A` restricts to a
chosen cocycle-level product if the cycle inclusions `iCycles` intertwine the two families. -/
def diagonalStandardComplexCochainProductRestrictsToCycles
    (A : Rep ℤ π) (cochainProduct : DiagonalStandardComplexCochainProduct A)
    (cycleProduct : DiagonalStandardComplexCycleProduct A) : Prop :=
  ∀ p q : ℕ,
    CommSq
      (cycleProduct p q)
      (diagonalStandardComplexCyclesTensorInclusion A p q)
      (diagonalStandardComplexCycleInclusion A (p + q))
      (cochainProduct p q)

/-- The quotient map from diagonal standard-resolution cycles to cohomology in degree `n`. -/
def diagonalStandardComplexHomologyProjection (A : Rep ℤ π) (n : ℕ) :
    (diagonalStandardCochainComplex A).cycles n ⟶
      (diagonalStandardCochainComplex A).homology n :=
  (diagonalStandardCochainComplex A).homologyπ n

/-- Tensor comparison induced by the quotient maps `homologyπ` in bidegree `(p, q)`. -/
def diagonalStandardComplexCyclesTensorToHomology (A : Rep ℤ π) (p q : ℕ) :
    (diagonalStandardCochainComplex A).cycles p ⊗
      (diagonalStandardCochainComplex A).cycles q ⟶
      (diagonalStandardCochainComplex A).homology p ⊗
        (diagonalStandardCochainComplex A).homology q :=
  diagonalStandardComplexHomologyProjection A p ⊗ₘ
    diagonalStandardComplexHomologyProjection A q

/-- A cocycle-level product on the standard-resolution model induces a chosen cohomology product
if the quotient maps `homologyπ` intertwine the two families. -/
def diagonalStandardComplexCycleProductInduces
    (A : Rep ℤ π) (cycleProduct : DiagonalStandardComplexCycleProduct A)
    (diagonalProduct : DiagonalStandardComplexProduct A) : Prop :=
  ∀ p q : ℕ,
    CommSq
      (cycleProduct p q)
      (diagonalStandardComplexCyclesTensorToHomology A p q)
      (diagonalStandardComplexHomologyProjection A (p + q))
      (diagonalProduct p q)

/-- A coefficient pairing `A ⊗ A ⟶ A` used to define cup / Yoneda products on
`groupCohomology A`. -/
abbrev GroupCohomologyCoefficientPairing (A : Rep ℤ π) : Type _ :=
  ((A : Rep ℤ π) ⊗ (A : Rep ℤ π)) ⟶ A

/-- A bidegree `(p, q)` diagonal approximation on `Rep.standardComplex ℤ π`, i.e. a family of
maps `P_(p + q) ⟶ P_p ⊗ P_q` for the standard resolution `P = Rep.standardComplex ℤ π`. -/
abbrev StandardResolutionDiagonalApproximation : Type _ :=
  ∀ p q : ℕ,
    (Rep.standardComplex ℤ π).X (p + q) ⟶
      ((Rep.standardComplex ℤ π).X p ⊗ (Rep.standardComplex ℤ π).X q)

/-- Helper for Problem 18.6.2: the bilinear cochain kernel determined by a coefficient pairing and
a diagonal approximation on the standard resolution. -/
private def diagonalStandardComplexCochainKernel
    (A : Rep ℤ π) (pairing : GroupCohomologyCoefficientPairing A)
    (diagonalApproximation : StandardResolutionDiagonalApproximation (π := π))
    (p q : ℕ) (m : (diagonalStandardCochainComplex A).X p)
    (n : (diagonalStandardCochainComplex A).X q) :
    (diagonalStandardCochainComplex A).X (p + q) :=
  diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing

/-- Helper for Problem 18.6.2: the cochain kernel induced by a diagonal approximation is additive
in its left cochain variable. -/
private lemma diagonalStandardComplexCochainProductOf_add_left
    (A : Rep ℤ π) (pairing : GroupCohomologyCoefficientPairing A)
    (diagonalApproximation : StandardResolutionDiagonalApproximation (π := π))
    (p q : ℕ) (f₁ f₂ : (Rep.standardComplex ℤ π).X p ⟶ A)
    (g : (Rep.standardComplex ℤ π).X q ⟶ A) :
    diagonalApproximation p q ≫ ((f₁ + f₂) ⊗ₘ g) ≫ pairing =
      diagonalApproximation p q ≫ (f₁ ⊗ₘ g) ≫ pairing +
        diagonalApproximation p q ≫ (f₂ ⊗ₘ g) ≫ pairing := by
  -- Rewrite the tensor factor through the left sum, then distribute both outer compositions.
  rw [CategoryTheory.MonoidalPreadditive.add_tensor]
  simp only [Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Problem 18.6.2: the `Module ℤ` scalar on `Rep` morphisms agrees with the ambient
`zsmul`, so later whisker and composition lemmas can be compared in one scalar world. -/
private lemma repHom_moduleIntSmul_eq_zsmul
    {M N : Rep ℤ π} (a : ℤ) (f : M ⟶ N) :
    @HSMul.hSMul ℤ (M ⟶ N) (M ⟶ N)
        (@instHSMul _ _ ((inferInstance : Module ℤ (M ⟶ N)).toDistribSMul.toSMul)) a f =
      a • f := by
  -- Convert the module-induced scalar to the canonical additive `zsmul`.
  simpa using (int_smul_eq_zsmul (inferInstance : Module ℤ (M ⟶ N)) a f)

/-- Helper for Problem 18.6.2: the `Module ℤ` scalar on a `ModuleCat` carrier agrees with the
ambient additive `zsmul`. -/
private lemma moduleCat_moduleIntSmul_eq_zsmul
    {M : ModuleCat ℤ} (a : ℤ) (m : M) :
    @HSMul.hSMul ℤ M M
        (@instHSMul _ _ ((inferInstance : Module ℤ M).toDistribSMul.toSMul)) a m =
      a • m := by
  -- Convert the module-induced scalar to the canonical additive `zsmul`.
  simpa using (int_smul_eq_zsmul (inferInstance : Module ℤ M) a m)

/-- Helper for Problem 18.6.2: the `Module ℤ` scalar on an intertwining map agrees with the
ambient additive `zsmul`. -/
private lemma intertwiningMap_moduleIntSmul_eq_zsmul
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module ℤ V] [Module ℤ W]
    {ρ : Representation ℤ π V} {σ : Representation ℤ π W}
    (a : ℤ) (f : ρ.IntertwiningMap σ) :
    @HSMul.hSMul ℤ (ρ.IntertwiningMap σ) (ρ.IntertwiningMap σ)
        (@instHSMul _ _
          ((inferInstance : Module ℤ (ρ.IntertwiningMap σ)).toDistribSMul.toSMul)) a f =
      a • f := by
  -- Convert the module-induced scalar on intertwining maps to the canonical additive `zsmul`.
  simpa using (int_smul_eq_zsmul (inferInstance : Module ℤ (ρ.IntertwiningMap σ)) a f)

/-- Helper for Problem 18.6.2: the generic `ℤ`-scalar action on an intertwining map coming from
the coefficient-ring structure agrees with the ambient additive `zsmul`. -/
private lemma intertwiningMap_ringSmulInt_eq_zsmul
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module ℤ V] [Module ℤ W]
    {ρ : Representation ℤ π V} {σ : Representation ℤ π W}
    (a : ℤ) (f : ρ.IntertwiningMap σ) :
    @HSMul.hSMul ℤ (ρ.IntertwiningMap σ) (ρ.IntertwiningMap σ)
        (@instHSMul _ _ (Representation.IntertwiningMap.instSMul (ρ := ρ) (σ := σ))) a f =
      a • f := by
  -- Both scalar structures scale the same underlying linear map, so the resulting intertwining maps
  -- agree pointwise.
  ext v
  rw [Representation.IntertwiningMap.toLinearMap_smul]
  simpa using (int_smul_eq_zsmul (inferInstance : Module ℤ W) a (f v))

/-- Helper for Problem 18.6.2: the cochain kernel induced by a diagonal approximation is
`ℤ`-linear in its left cochain variable. -/
private lemma diagonalStandardComplexTensorHom_zsmul_left
    (A : Rep ℤ π) (p q : ℕ) (a : ℤ)
    (m : (Rep.standardComplex ℤ π).X p ⟶ A)
    (n : (Rep.standardComplex ℤ π).X q ⟶ A) :
    ((a • m) ⊗ₘ n) = a • (m ⊗ₘ n) := by
  -- Route correction: bypass the unavailable `MonoidalLinear` instance by comparing underlying
  -- intertwining maps, where tensoring is explicitly `ℤ`-linear.
  refine Rep.hom_ext ?_
  -- After rewriting both `Rep` morphisms to functions, tensor-product induction reduces the
  -- equality to pure tensors, where scalar linearity is immediate.
  -- Local instance justification (module ambiguity): both `↑A` and `↑(A ⊗ A)` carry the
  -- representation module structures as well as generic `AddCommGroup.toIntModule` fallbacks; pin
  -- the representation instances so the tensor rewrites elaborate in the intended scalar world.
  letI : Module ℤ ↑A := A.hV2
  letI : Module ℤ ↑(A ⊗ A) := (A ⊗ A).hV2
  exact
    (Representation.IntertwiningMap.toFun_injective
      (ρ := ((Rep.standardComplex ℤ π).X p ⊗ (Rep.standardComplex ℤ π).X q).ρ)
      (σ := (A ⊗ A).ρ)) <| by
    funext z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro x y
      rfl
    · intro z₁ z₂ hz₁ hz₂
      have hz₁' :
          (TensorProduct.map (Rep.Hom.hom (a • m)).toLinearMap (Rep.Hom.hom n).toLinearMap) z₁ =
            (Rep.Hom.hom (a • (m ⊗ₘ n))) z₁ := by
        simpa [Rep.hom_tensorHom, Rep.zsmul_hom] using hz₁
      have hz₂' :
          (TensorProduct.map (Rep.Hom.hom (a • m)).toLinearMap (Rep.Hom.hom n).toLinearMap) z₂ =
            (Rep.Hom.hom (a • (m ⊗ₘ n))) z₂ := by
        simpa [Rep.hom_tensorHom, Rep.zsmul_hom] using hz₂
      simp [hz₁', hz₂']

/-- Helper for Problem 18.6.2: the cochain kernel induced by a diagonal approximation is
`ℤ`-linear in its left cochain variable. -/
private lemma diagonalStandardComplexCochainProductOf_zsmul_left
    (A : Rep ℤ π) (pairing : GroupCohomologyCoefficientPairing A)
    (diagonalApproximation : StandardResolutionDiagonalApproximation (π := π))
    (p q : ℕ) (a : ℤ) (m : (diagonalStandardCochainComplex A).X p)
    (n : (diagonalStandardCochainComplex A).X q) :
    diagonalApproximation p q ≫ ((a • m) ⊗ₘ n) ≫ pairing =
      a • (diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing) := by
  let m' : (Rep.standardComplex ℤ π).X p ⟶ A := m
  let n' : (Rep.standardComplex ℤ π).X q ⟶ A := n
  -- Reduce the cochain variables to the underlying `Rep` morphisms and use the isolated tensor
  -- linearity bridge before pushing the scalar through composition.
  simpa [m', n'] using
    calc
      diagonalApproximation p q ≫ ((a • m') ⊗ₘ n') ≫ pairing
          = diagonalApproximation p q ≫ (a • (m' ⊗ₘ n')) ≫ pairing := by
              rw [diagonalStandardComplexTensorHom_zsmul_left A p q a m' n']
      _ = a • (diagonalApproximation p q ≫ (m' ⊗ₘ n') ≫ pairing) := by
              simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]

/-- Helper for Problem 18.6.2: the cochain kernel induced by a diagonal approximation is additive
in its right cochain variable. -/
private lemma diagonalStandardComplexCochainProductOf_add_right
    (A : Rep ℤ π) (pairing : GroupCohomologyCoefficientPairing A)
    (diagonalApproximation : StandardResolutionDiagonalApproximation (π := π))
    (p q : ℕ) (f : (Rep.standardComplex ℤ π).X p ⟶ A)
    (g₁ g₂ : (Rep.standardComplex ℤ π).X q ⟶ A) :
    diagonalApproximation p q ≫ (f ⊗ₘ (g₁ + g₂)) ≫ pairing =
      diagonalApproximation p q ≫ (f ⊗ₘ g₁) ≫ pairing +
        diagonalApproximation p q ≫ (f ⊗ₘ g₂) ≫ pairing := by
  -- Rewrite the tensor factor through the right sum, then distribute both outer compositions.
  rw [CategoryTheory.MonoidalPreadditive.tensor_add]
  simp only [Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Problem 18.6.2: the cochain kernel induced by a diagonal approximation is
`ℤ`-linear in its right cochain variable. -/
private lemma repHom_apply_add
    {X Y : Rep ℤ π} (f : X ⟶ Y) (u v : X) :
    Rep.Hom.hom f (u + v) = Rep.Hom.hom f u + Rep.Hom.hom f v := by
  -- The underlying intertwining map is linear, so evaluation preserves addition.
  simp

/-- Helper for Problem 18.6.2: the cochain kernel induced by a diagonal approximation is
`ℤ`-linear in its right cochain variable. -/
private lemma diagonalStandardComplexTensorHom_zsmul_right
    (A : Rep ℤ π) (p q : ℕ) (a : ℤ)
    (m : (Rep.standardComplex ℤ π).X p ⟶ A)
    (n : (Rep.standardComplex ℤ π).X q ⟶ A) :
    (m ⊗ₘ (a • n)) = a • (m ⊗ₘ n) :=
by
  -- Rephrase the tensor morphisms using `Rep.ofHom`, so the owner theorem on intertwining maps
  -- and the scalar action both live in the same `SMul` world.
  -- Local instance justification (module ambiguity): both `↑A` and `↑(A ⊗ A)` carry the
  -- representation module structures as well as generic `AddCommGroup.toIntModule` fallbacks; pin
  -- the representation instances so the `ofHom` comparison uses the intended scalar world.
  letI : Module ℤ ↑A := A.hV2
  letI : Module ℤ ↑(A ⊗ A) := (A ⊗ A).hV2
  -- Unfold the `Rep` tensor morphisms to `Rep.ofHom`, where the intertwining-map statement is
  -- exactly the desired equality.
  change Rep.ofHom ((Rep.Hom.hom m).tensor (a • Rep.Hom.hom n)) =
      Rep.ofHom (a • ((Rep.Hom.hom m).tensor (Rep.Hom.hom n)))
  -- Rewrite the ambient `zsmul` spellings to the generic ring-scalar spellings used by the owner
  -- tensor-linearity lemma.
  rw [← intertwiningMap_ringSmulInt_eq_zsmul
        (ρ := ((Rep.standardComplex ℤ π).X q).ρ) (σ := A.ρ) a (Rep.Hom.hom n)]
  rw [← intertwiningMap_ringSmulInt_eq_zsmul
        (ρ := ((Rep.standardComplex ℤ π).X p ⊗ (Rep.standardComplex ℤ π).X q).ρ)
        (σ := (A ⊗ A).ρ) a ((Rep.Hom.hom m).tensor (Rep.Hom.hom n))]
  exact
    congrArg (fun f ↦ Rep.ofHom f)
      (Representation.IntertwiningMap.tensor_smul_right (f := m.hom) (a := a) (g := n.hom))

/-- Helper for Problem 18.6.2: once the tensor factor is rewritten, `ℤ`-scalars pass through the
two outer `Rep` compositions defining the cochain kernel. -/
private lemma diagonalStandardComplexCochainKernel_smul_comp
    (A : Rep ℤ π) (pairing : GroupCohomologyCoefficientPairing A)
    (diagonalApproximation : StandardResolutionDiagonalApproximation (π := π))
    (p q : ℕ) (a : ℤ)
    (t : (Rep.standardComplex ℤ π).X p ⊗ (Rep.standardComplex ℤ π).X q ⟶ A ⊗ A) :
    diagonalApproximation p q ≫ (a • t) ≫ pairing =
      a • (diagonalApproximation p q ≫ t ≫ pairing) := by
  -- Push the scalar through the left and then the right composition using `Rep` linearity.
  calc
    diagonalApproximation p q ≫ (a • t) ≫ pairing
        = (a • (diagonalApproximation p q ≫ t)) ≫ pairing := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ f ≫ pairing) (Rep.comp_smul (diagonalApproximation p q) a t)
    _ = a • (diagonalApproximation p q ≫ t ≫ pairing) := by
            simpa [Category.assoc] using
              (Rep.smul_comp a (diagonalApproximation p q ≫ t) pairing)

/-- Helper for Problem 18.6.2: the cochain kernel induced by a diagonal approximation is
`ℤ`-linear in its right cochain variable. -/
private lemma diagonalStandardComplexCochainProductOf_zsmul_right
    (A : Rep ℤ π) (pairing : GroupCohomologyCoefficientPairing A)
    (diagonalApproximation : StandardResolutionDiagonalApproximation (π := π))
    (p q : ℕ) (a : ℤ) (m : (diagonalStandardCochainComplex A).X p)
    (n : (diagonalStandardCochainComplex A).X q) :
    diagonalApproximation p q ≫ (m ⊗ₘ (a • n)) ≫ pairing =
      a • (diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing) := by
  let m' : (Rep.standardComplex ℤ π).X p ⟶ A := m
  let n' : (Rep.standardComplex ℤ π).X q ⟶ A := n
  -- Reduce the cochain variables to the underlying `Rep` morphisms and use the isolated tensor
  -- linearity bridge before pushing the scalar through composition.
  simpa [m', n'] using
    calc
      diagonalApproximation p q ≫ (m' ⊗ₘ (a • n')) ≫ pairing
          = diagonalApproximation p q ≫ (a • (m' ⊗ₘ n')) ≫ pairing := by
              rw [diagonalStandardComplexTensorHom_zsmul_right A p q a m' n']
      _ = a • (diagonalApproximation p q ≫ (m' ⊗ₘ n') ≫ pairing) := by
              simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]

/-- Helper for Problem 18.6.2: the left scalar witness for `tensorLift` obtained by fixing the
module-induced `SMul` on the cochain carriers. -/
private lemma diagonalStandardComplexCochainProductOf_tensorLiftModule_smul_left
    (A : Rep ℤ π) (pairing : GroupCohomologyCoefficientPairing A)
    (diagonalApproximation : StandardResolutionDiagonalApproximation (π := π))
    (p q : ℕ) (a : ℤ) (m : (diagonalStandardCochainComplex A).X p)
    (n : (diagonalStandardCochainComplex A).X q) :
    diagonalApproximation p q ≫
        ((@HSMul.hSMul ℤ (↑((diagonalStandardCochainComplex A).X p))
            (↑((diagonalStandardCochainComplex A).X p))
            (@instHSMul _ _
              ((diagonalStandardCochainComplex A).X p).isModule.toDistribSMul.toSMul) a m) ⊗ₘ n) ≫
          pairing =
      @HSMul.hSMul ℤ (↑((diagonalStandardCochainComplex A).X (p + q)))
        (↑((diagonalStandardCochainComplex A).X (p + q)))
        (@instHSMul _ _
          ((diagonalStandardCochainComplex A).X (p + q)).isModule.toDistribSMul.toSMul) a
        (diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing) := by
  -- Rewrite the explicit `ModuleCat` scalar witnesses to the ambient `zsmul`, then invoke the
  -- already established left-linearity of the cochain kernel.
  rw [moduleCat_moduleIntSmul_eq_zsmul]
  calc
    diagonalApproximation p q ≫ ((a • m) ⊗ₘ n) ≫ pairing
        = a • (diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing) := by
            exact
              diagonalStandardComplexCochainProductOf_zsmul_left
                A pairing diagonalApproximation p q a m n
    _ =
        @HSMul.hSMul ℤ (↑((diagonalStandardCochainComplex A).X (p + q)))
          (↑((diagonalStandardCochainComplex A).X (p + q)))
          (@instHSMul _ _
            ((diagonalStandardCochainComplex A).X (p + q)).isModule.toDistribSMul.toSMul) a
          (diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing) := by
            symm
            exact
              moduleCat_moduleIntSmul_eq_zsmul
                (M := (diagonalStandardCochainComplex A).X (p + q))
                a (diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing)

/-- Helper for Problem 18.6.2: the right scalar witness for `tensorLift` obtained by fixing the
module-induced `SMul` on the cochain carriers. -/
private lemma diagonalStandardComplexCochainProductOf_tensorLiftModule_smul_right
    (A : Rep ℤ π) (pairing : GroupCohomologyCoefficientPairing A)
    (diagonalApproximation : StandardResolutionDiagonalApproximation (π := π))
    (p q : ℕ) (a : ℤ) (m : (diagonalStandardCochainComplex A).X p)
    (n : (diagonalStandardCochainComplex A).X q) :
    diagonalApproximation p q ≫
        (m ⊗ₘ (@HSMul.hSMul ℤ (↑((diagonalStandardCochainComplex A).X q))
            (↑((diagonalStandardCochainComplex A).X q))
            (@instHSMul _ _
              ((diagonalStandardCochainComplex A).X q).isModule.toDistribSMul.toSMul) a n)) ≫
          pairing =
      @HSMul.hSMul ℤ (↑((diagonalStandardCochainComplex A).X (p + q)))
        (↑((diagonalStandardCochainComplex A).X (p + q)))
        (@instHSMul _ _
          ((diagonalStandardCochainComplex A).X (p + q)).isModule.toDistribSMul.toSMul) a
        (diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing) := by
  -- Rewrite the explicit `ModuleCat` scalar witnesses to the ambient `zsmul`, then invoke the
  -- already established right-linearity of the cochain kernel.
  rw [moduleCat_moduleIntSmul_eq_zsmul]
  calc
    diagonalApproximation p q ≫ (m ⊗ₘ (a • n)) ≫ pairing
        = a • (diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing) := by
            exact
              diagonalStandardComplexCochainProductOf_zsmul_right
                A pairing diagonalApproximation p q a m n
    _ =
        @HSMul.hSMul ℤ (↑((diagonalStandardCochainComplex A).X (p + q)))
          (↑((diagonalStandardCochainComplex A).X (p + q)))
          (@instHSMul _ _
            ((diagonalStandardCochainComplex A).X (p + q)).isModule.toDistribSMul.toSMul) a
          (diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing) := by
            symm
            exact
              moduleCat_moduleIntSmul_eq_zsmul
                (M := (diagonalStandardCochainComplex A).X (p + q))
                a (diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing)

/-- The cochain-level product on `(Rep.standardComplex ℤ π).linearYonedaObj ℤ A` induced by a
coefficient pairing `A ⊗ A ⟶ A` and a diagonal approximation on the standard resolution. -/
def diagonalStandardComplexCochainProductOf
    (A : Rep ℤ π) (pairing : GroupCohomologyCoefficientPairing A)
    (diagonalApproximation :
      ∀ p q : ℕ,
        (Rep.standardComplex ℤ π).X (p + q) ⟶
          ((Rep.standardComplex ℤ π).X p ⊗ (Rep.standardComplex ℤ π).X q)) :
    DiagonalStandardComplexCochainProduct A :=
  fun p q ↦
    -- Package the explicit bilinear kernel in the `Rep` morphism world, where the additivity and
    -- scalar witnesses already have the canonical linear shapes required by `tensorLift`.
    ModuleCat.MonoidalCategory.tensorLift
      (fun m n ↦ diagonalApproximation p q ≫ (m ⊗ₘ n) ≫ pairing)
      (diagonalStandardComplexCochainProductOf_add_left A pairing diagonalApproximation p q)
      (diagonalStandardComplexCochainProductOf_tensorLiftModule_smul_left
        A pairing diagonalApproximation p q)
      (diagonalStandardComplexCochainProductOf_add_right A pairing diagonalApproximation p q)
      (diagonalStandardComplexCochainProductOf_tensorLiftModule_smul_right
        A pairing diagonalApproximation p q)

/-- A product on the cohomology of the diagonal standard-resolution model is induced by a
coefficient pairing and diagonal approximation if the cochain product they define descends first to
cocycles and then to cohomology. -/
def diagonalStandardComplexProductOf
    (A : Rep ℤ π) (pairing : GroupCohomologyCoefficientPairing A)
    (diagonalApproximation :
      ∀ p q : ℕ,
        (Rep.standardComplex ℤ π).X (p + q) ⟶
          ((Rep.standardComplex ℤ π).X p ⊗ (Rep.standardComplex ℤ π).X q))
    (cycleProduct : DiagonalStandardComplexCycleProduct A)
    (diagonalProduct : DiagonalStandardComplexProduct A) : Prop :=
  diagonalStandardComplexCochainProductRestrictsToCycles
      A (diagonalStandardComplexCochainProductOf A pairing diagonalApproximation) cycleProduct ∧
    diagonalStandardComplexCycleProductInduces A cycleProduct diagonalProduct

/-- The product on `groupCohomology A` transported from a chosen product on the diagonal
standard-resolution cohomology model of `A` by `groupCohomologyIsoDiagonalStandardComplex`. -/
def groupCohomologyDiagonalStandardProduct
    (A : Rep ℤ π) (diagonalProduct : DiagonalStandardComplexProduct A) :
    GroupCohomologyProduct A :=
  fun p q ↦
    groupCohomologyIsoDiagonalStandardComplexTensor A p q ≫ diagonalProduct p q ≫
      diagonalStandardComplexToGroupCohomology A (p + q)

/-- Problem 18.6.2 (2): the product on `groupCohomology A` transported from a chosen product on
the diagonal standard-resolution cohomology model is compatible with that model product under
`groupCohomologyIsoDiagonalStandardComplex`. -/
theorem groupCohomologyDiagonalStandardProduct_compatible
    (A : Rep ℤ π) (diagonalProduct : DiagonalStandardComplexProduct A) :
    diagonalStandardComplexProductCompatible
      A (groupCohomologyDiagonalStandardProduct A diagonalProduct) diagonalProduct := by
  intro p q
  refine ⟨?_⟩
  -- Unfold the transported product and cancel the comparison isomorphism in degree `p + q`.
  rw [groupCohomologyDiagonalStandardProduct, diagonalStandardComplexToGroupCohomology,
    groupCohomologyToDiagonalStandardComplex]
  simp [Category.assoc]
