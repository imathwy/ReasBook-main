import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Tactic
import StacksProject_2024.Chap20.«20_25_3_1»
import StacksProject_2024.Chap22.Definition_22_3_1

open CategoryTheory CategoryTheory.GradedObject.Monoidal CategoryTheory.MonoidalCategory
open ComplexShape HomologicalComplex
open scoped TensorProduct

noncomputable section

universe u

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]
variable (A B : CochainDGAlgebra R)
variable [HasTensor A.toCochainComplex B.toCochainComplex]

/-- Companion data for Definition 22.3.4: the tensor-product differential graded algebra is built
on the canonical total tensor complex `HomologicalComplex.tensorObj A.toCochainComplex
B.toCochainComplex`. -/
private abbrev tensorProductComplex : CochainComplex (ModuleCat R) ℤ :=
  HomologicalComplex.tensorObj A.toCochainComplex B.toCochainComplex

/-- The Koszul-signed swap on a homogeneous tensor summand of two graded `R`-module objects. -/
private def tensorKoszulBraidingComponent
    (V W : CategoryTheory.GradedObject ℤ (ModuleCat R)) (p q : ℤ) :
    V p ⊗ W q ⟶ W q ⊗ V p :=
  (p * q).negOnePow • (β_ (V p) (W q)).hom

/-- The homogeneous multiplication of a cochain differential graded algebra, viewed as a morphism
out of the tensor product of the two graded pieces. -/
private abbrev mulHom (A : CochainDGAlgebra R) (p q : ℤ) :
    A.X p ⊗ A.X q ⟶ A.X (p + q) :=
  ModuleCat.ofHom (TensorProduct.lift (A.mul p q))

private def tensorProductUnitHom :
    ModuleCat.of R R ⟶ (tensorProductComplex A B).X 0 :=
  ModuleCat.ofHom
      { toFun := fun r ↦ r • (A.one ⊗ₜ[R] B.one)
        map_add' := by
          intro r s
          simp [add_smul]
        map_smul' := by
          intro r s
          simp [smul_smul] } ≫
    ιTensorObj A.toCochainComplex B.toCochainComplex 0 0 0 rfl

private def tensorProductMulComponentHom (p q p' q' : ℤ) :
    ((A.X p ⊗ B.X q) ⊗ (A.X p' ⊗ B.X q')) ⟶
      (tensorProductComplex A B).X ((p + q) + (p' + q')) :=
  (α_ (A.X p) (B.X q) (A.X p' ⊗ B.X q')).hom ≫
    (A.X p ◁ (α_ (B.X q) (A.X p') (B.X q')).inv) ≫
    (A.X p ◁ (tensorKoszulBraidingComponent B.toCochainComplex.X A.toCochainComplex.X q p' ▷
      B.X q')) ≫
    (A.X p ◁ (α_ (A.X p') (B.X q) (B.X q')).hom) ≫
    (α_ (A.X p) (A.X p') (B.X q ⊗ B.X q')).inv ≫
    (mulHom A p p' ⊗ₘ mulHom B q q') ≫
      ιTensorObj A.toCochainComplex B.toCochainComplex
        (p + p') (q + q') ((p + q) + (p' + q')) (by abel_nf)

private abbrev tensorProductMulCurriedComponent (p q p' q' : ℤ) :
    ↑(A.X p ⊗ B.X q) →ₗ[R] ↑(A.X p' ⊗ B.X q') →ₗ[R]
      ↑((tensorProductComplex A B).X ((p + q) + (p' + q'))) :=
  TensorProduct.curry (tensorProductMulComponentHom A B p q p' q').hom

private def tensorProductRightMulComponent
    (n m p q : ℤ) (hpq : p + q = n) (x : ↑(A.X p ⊗ B.X q))
    (p' q' : ℤ) (hp'q' : (up ℤ).π (up ℤ) (up ℤ) (p', q') = m) :
    A.X p' ⊗ B.X q' ⟶ (tensorProductComplex A B).X (n + m) :=
  ModuleCat.ofHom (tensorProductMulCurriedComponent A B p q p' q' x) ≫
    eqToHom (by
      have hm : p' + q' = m := by simpa using hp'q'
      apply congrArg ((tensorProductComplex A B).X)
      omega)

private abbrev tensorProductRightMulFamily
    (n m p q : ℤ) (hpq : p + q = n) (x : ↑(A.X p ⊗ B.X q))
    (p' q' : ℤ) (hp'q' : (up ℤ).π (up ℤ) (up ℤ) (p', q') = m) :
    A.X p' ⊗ B.X q' ⟶ (tensorProductComplex A B).X (n + m) :=
  tensorProductRightMulComponent A B n m p q hpq x p' q' hp'q'

private theorem tensorProductRightMulComponent_add
    (n m p q : ℤ) (hpq : p + q = n) (x y : ↑(A.X p ⊗ B.X q))
    (p' q' : ℤ) (hp'q' : (up ℤ).π (up ℤ) (up ℤ) (p', q') = m) :
    tensorProductRightMulComponent A B n m p q hpq (x + y) p' q' hp'q' =
      tensorProductRightMulComponent A B n m p q hpq x p' q' hp'q' +
        tensorProductRightMulComponent A B n m p q hpq y p' q' hp'q' := by
  ext z
  simp [tensorProductRightMulComponent, tensorProductMulCurriedComponent, LinearMap.add_apply]

private theorem tensorProductRightMulComponent_smul
    (n m p q : ℤ) (hpq : p + q = n) (r : R) (x : ↑(A.X p ⊗ B.X q))
    (p' q' : ℤ) (hp'q' : (up ℤ).π (up ℤ) (up ℤ) (p', q') = m) :
    tensorProductRightMulComponent A B n m p q hpq (r • x) p' q' hp'q' =
      r • tensorProductRightMulComponent A B n m p q hpq x p' q' hp'q' := by
  ext z
  simp [tensorProductRightMulComponent, tensorProductMulCurriedComponent, LinearMap.smul_apply]

private def tensorProductRightMulDesc
    (n m p q : ℤ) (hpq : p + q = n) (x : ↑(A.X p ⊗ B.X q)) :
    (tensorProductComplex A B).X m ⟶ (tensorProductComplex A B).X (n + m) :=
  mapBifunctorDesc (tensorProductRightMulFamily A B n m p q hpq x)

private def tensorProductRightMulOnSummand (n m p q : ℤ) (hpq : p + q = n) :
    A.X p ⊗ B.X q ⟶ ModuleCat.of R
      (((tensorProductComplex A B).X m) →ₗ[R] (tensorProductComplex A B).X (n + m)) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ (tensorProductRightMulDesc A B n m p q hpq x).hom
      map_add' := by
        intro x y
        ext z
        have hmor :
            tensorProductRightMulDesc A B n m p q hpq (x + y) =
              tensorProductRightMulDesc A B n m p q hpq x +
                tensorProductRightMulDesc A B n m p q hpq y := by
          apply HomologicalComplex.mapBifunctor.hom_ext
          intro p' q' hp'q'
          unfold tensorProductRightMulDesc
          change
            ιMapBifunctor A.toCochainComplex B.toCochainComplex (curriedTensor (ModuleCat R))
                (up ℤ) p' q' m hp'q' ≫
                mapBifunctorDesc
                  (fun p' q' hp'q' ↦
                    tensorProductRightMulComponent A B n m p q hpq (x + y) p' q' hp'q') =
              ιMapBifunctor A.toCochainComplex B.toCochainComplex (curriedTensor (ModuleCat R))
                (up ℤ) p' q' m hp'q' ≫
                  (mapBifunctorDesc
                      (fun p' q' hp'q' ↦
                        tensorProductRightMulComponent A B n m p q hpq x p' q' hp'q') +
                    mapBifunctorDesc
                      (fun p' q' hp'q' ↦
                        tensorProductRightMulComponent A B n m p q hpq y p' q' hp'q'))
          rw [Preadditive.comp_add, HomologicalComplex.ι_mapBifunctorDesc,
            HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
          exact tensorProductRightMulComponent_add A B n m p q hpq x y p' q' hp'q'
        simpa using congrArg
          (fun f : (tensorProductComplex A B).X m ⟶ (tensorProductComplex A B).X (n + m) ↦
            f.hom z)
          hmor
      map_smul' := by
        intro r x
        ext z
        have hmor :
            tensorProductRightMulDesc A B n m p q hpq (r • x) =
              r • tensorProductRightMulDesc A B n m p q hpq x := by
          apply HomologicalComplex.mapBifunctor.hom_ext
          intro p' q' hp'q'
          unfold tensorProductRightMulDesc
          change
            ιMapBifunctor A.toCochainComplex B.toCochainComplex (curriedTensor (ModuleCat R))
                (up ℤ) p' q' m hp'q' ≫
                mapBifunctorDesc
                  (fun p' q' hp'q' ↦
                    tensorProductRightMulComponent A B n m p q hpq (r • x) p' q' hp'q') =
              ιMapBifunctor A.toCochainComplex B.toCochainComplex (curriedTensor (ModuleCat R))
                (up ℤ) p' q' m hp'q' ≫
                  (r •
                    mapBifunctorDesc
                      (fun p' q' hp'q' ↦
                        tensorProductRightMulComponent A B n m p q hpq x p' q' hp'q'))
          have hcomp :
              ιMapBifunctor A.toCochainComplex B.toCochainComplex (curriedTensor (ModuleCat R))
                  (up ℤ) p' q' m hp'q' ≫
                  (r •
                    mapBifunctorDesc
                      (fun p' q' hp'q' ↦
                        tensorProductRightMulComponent A B n m p q hpq x p' q' hp'q')) =
                r •
                  (ιMapBifunctor A.toCochainComplex B.toCochainComplex
                    (curriedTensor (ModuleCat R)) (up ℤ) p' q' m hp'q' ≫
                    mapBifunctorDesc
                      (fun p' q' hp'q' ↦
                        tensorProductRightMulComponent A B n m p q hpq x p' q' hp'q')) := by
            simpa using
              CategoryTheory.Linear.comp_smul
                _
                _
                _
                (ιMapBifunctor A.toCochainComplex B.toCochainComplex
                  (curriedTensor (ModuleCat R)) (up ℤ) p' q' m hp'q')
                r
                (mapBifunctorDesc
                  (fun p' q' hp'q' ↦
                    tensorProductRightMulComponent A B n m p q hpq x p' q' hp'q'))
          rw [hcomp, HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
          exact tensorProductRightMulComponent_smul A B n m p q hpq r x p' q' hp'q'
        simpa using congrArg
          (fun f : (tensorProductComplex A B).X m ⟶ (tensorProductComplex A B).X (n + m) ↦
            f.hom z)
          hmor }

private abbrev tensorProductMulFamily (n m p q : ℤ) (hpq : p + q = n) :
    A.X p ⊗ B.X q ⟶ ModuleCat.of R
      (((tensorProductComplex A B).X m) →ₗ[R] (tensorProductComplex A B).X (n + m)) :=
  tensorProductRightMulOnSummand A B n m p q hpq

private def tensorProductMulDesc (n m : ℤ) :
    (tensorProductComplex A B).X n ⟶ ModuleCat.of R
      (((tensorProductComplex A B).X m) →ₗ[R] (tensorProductComplex A B).X (n + m)) :=
  mapBifunctorDesc (tensorProductMulFamily A B n m)

/-- Companion data for Definition 22.3.4: the unit in the tensor-product differential graded
algebra is the pure tensor of the units of `A` and `B`, placed in total degree `0`. -/
private def tensorProductOne : (tensorProductComplex A B).X 0 :=
  (tensorProductUnitHom A B).hom 1

/-- Companion data for Definition 22.3.4: the homogeneous multiplication on the tensor-product
differential graded algebra is induced by the Koszul-signed swap of the middle factors followed by
the multiplications of `A` and `B`. -/
private def tensorProductMul (n m : ℤ) :
    (tensorProductComplex A B).X n →ₗ[R]
      (tensorProductComplex A B).X m →ₗ[R] (tensorProductComplex A B).X (n + m) :=
  (tensorProductMulDesc A B n m).hom

/-- Helper for Definition 22.3.4: the explicit summand-level value of the tensor-product
multiplication on homogeneous tensors. -/
private abbrev tensorProductMulOnSummandsValue
    (p q p' q' : ℤ) (x : ↑(A.X p ⊗ B.X q)) (y : ↑(A.X p' ⊗ B.X q')) :
    (tensorProductComplex A B).X ((p + q) + (p' + q')) :=
  (tensorProductMulComponentHom A B p q p' q').hom (x ⊗ₜ[R] y)

/-- Helper for Definition 22.3.4: before bundling the tensor-product owner, the raw homogeneous
multiplication on the canonical tensor complex satisfies the expected Koszul-signed summand
formula. -/
private theorem tensorProductMul_apply_on_summands_raw
    (p q p' q' : ℤ) (x : ↑(A.X p ⊗ B.X q)) (y : ↑(A.X p' ⊗ B.X q')) :
    tensorProductMul A B (p + q) (p' + q')
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom x)
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom y) =
        tensorProductMulOnSummandsValue A B p q p' q' x y := by
  -- Proof comment: evaluate the outer `mapBifunctorDesc` on the chosen left summand.
  have hleftMor :
      ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl ≫
          tensorProductMulDesc A B (p + q) (p' + q') =
        tensorProductRightMulOnSummand A B (p + q) (p' + q') p q rfl := by
    simpa [tensorProductMulDesc, tensorProductMulFamily, HomologicalComplex.ιTensorObj] using
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := A.toCochainComplex) (K₂ := B.toCochainComplex)
        (F := curriedTensor (ModuleCat R)) (c := up ℤ)
        (A := ModuleCat.of R
          (((tensorProductComplex A B).X (p' + q')) →ₗ[R]
            (tensorProductComplex A B).X ((p + q) + (p' + q'))))
        (j := p + q) (f := tensorProductMulFamily A B (p + q) (p' + q')) p q rfl)
  have hleft :
      (tensorProductMulDesc A B (p + q) (p' + q')).hom
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom x)
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom y) =
        (tensorProductRightMulDesc A B (p + q) (p' + q') p q rfl x).hom
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom y) := by
    have hleftEval :
        (tensorProductMulDesc A B (p + q) (p' + q')).hom
            ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom x) =
          (tensorProductRightMulOnSummand A B (p + q) (p' + q') p q rfl).hom x := by
      exact congrArg
        (fun f :
          ((A.X p ⊗ B.X q : ModuleCat R) ⟶
            ModuleCat.of R
              (((tensorProductComplex A B).X (p' + q')) →ₗ[R]
                (tensorProductComplex A B).X ((p + q) + (p' + q')))) ↦
          f.hom x)
        hleftMor
    simpa [tensorProductRightMulOnSummand] using congrArg
      (fun f :
        ((tensorProductComplex A B).X (p' + q')) →ₗ[R]
          (tensorProductComplex A B).X ((p + q) + (p' + q')) ↦
        f ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom y))
      hleftEval
  -- Proof comment: evaluate the inner descender on the chosen right summand.
  have hrightMor :
      ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl ≫
          tensorProductRightMulDesc A B (p + q) (p' + q') p q rfl x =
        tensorProductRightMulComponent A B (p + q) (p' + q') p q rfl x p' q' rfl := by
    simpa [tensorProductRightMulDesc, tensorProductRightMulFamily, HomologicalComplex.ιTensorObj]
      using
        (HomologicalComplex.ι_mapBifunctorDesc
          (K₁ := A.toCochainComplex) (K₂ := B.toCochainComplex)
          (F := curriedTensor (ModuleCat R)) (c := up ℤ)
          (A := (tensorProductComplex A B).X ((p + q) + (p' + q')))
          (j := p' + q')
          (f := tensorProductRightMulFamily A B (p + q) (p' + q') p q rfl x)
          p' q' rfl)
  have hright :
      (tensorProductRightMulDesc A B (p + q) (p' + q') p q rfl x).hom
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom y) =
        ((tensorProductRightMulComponent A B (p + q) (p' + q') p q rfl x p' q' rfl).hom) y := by
    exact congrArg
      (fun f :
        ((A.X p' ⊗ B.X q' : ModuleCat R) ⟶
          (tensorProductComplex A B).X ((p + q) + (p' + q'))) ↦
        f.hom y)
      hrightMor
  -- Proof comment: unfold the explicit component only at the final step.
  calc
    tensorProductMul A B (p + q) (p' + q')
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom x)
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom y) =
      ((tensorProductRightMulComponent A B (p + q) (p' + q') p q rfl x p' q' rfl).hom) y := by
        exact hleft.trans hright
    _ = tensorProductMulOnSummandsValue A B p q p' q' x y := by
      simp [tensorProductMulOnSummandsValue, tensorProductRightMulComponent,
        tensorProductMulCurriedComponent]

/-- Helper for Definition 22.3.4: casting a product of two `negOnePow` coefficients from `ℤ` to
`R` multiplies the individual cast coefficients. -/
private theorem castNegOnePowMul (a b : ℤ) :
    ((((a.negOnePow * b.negOnePow : ℤ)) : R)) = ((a.negOnePow : R) * (b.negOnePow : R)) := by
  -- Proof comment: `Int.cast_mul` applies directly once both factors are written in `ℤ`.
  simpa using
    (Int.cast_mul a.negOnePow b.negOnePow :
      ((((a.negOnePow * b.negOnePow : ℤ)) : R)) = ((a.negOnePow : R) * (b.negOnePow : R)))

/-- Helper for Definition 22.3.4: casting `(-1)^(a + b)` from `ℤ` to `R` yields the product of
the two cast coefficients. -/
private theorem castNegOnePowAdd (a b : ℤ) :
    ((((a + b).negOnePow : ℤ) : R)) = ((a.negOnePow : R) * (b.negOnePow : R)) := by
  -- Proof comment: rewrite `(-1)^(a + b)` multiplicatively in `ℤ`, then cast the product.
  rw [Int.negOnePow_add]
  exact castNegOnePowMul (R := R) a b

/-- Helper for Definition 22.3.4: the two Koszul coefficients in the associativity computation
combine to the coefficient on the regrouped product. -/
private theorem tensorProductMulAssocSign (q q' p' p'' : ℤ) :
    (((q * p').negOnePow : R) * (((q + q') * p'').negOnePow : R)) =
      (((q * (p' + p'')).negOnePow : R) * ((q' * p'').negOnePow : R)) := by
  -- Proof comment: expand both regrouped exponents once, then compare the resulting factors in
  -- the commutative coefficient ring.
  rw [show (q + q') * p'' = q * p'' + q' * p'' by ring]
  rw [castNegOnePowAdd (R := R) (q * p'') (q' * p'')]
  rw [show q * (p' + p'') = q * p' + q * p'' by ring]
  rw [castNegOnePowAdd (R := R) (q * p') (q * p'')]
  ring

/-- Helper for Definition 22.3.4: shifting the left `B`-degree by the differential contributes the
expected extra factor `(-1)^{p'}`. -/
private theorem tensorProductMulShiftLeftSign (q p' : ℤ) :
    (((((q + 1) * p').negOnePow : ℤ) : R)) =
      (((q * p').negOnePow : R) * (p'.negOnePow : R)) := by
  -- Proof comment: rewrite the shifted exponent as one extra copy of `p'`, then split the sign.
  rw [show (q + 1) * p' = q * p' + p' by ring]
  exact castNegOnePowAdd (R := R) (q * p') p'

/-- Helper for Definition 22.3.4: shifting the right `A`-degree by the differential contributes
the expected extra factor `(-1)^q`. -/
private theorem tensorProductMulShiftRightSign (q p' : ℤ) :
    ((((q * (p' + 1)).negOnePow : ℤ) : R)) =
      (((q * p').negOnePow : R) * (q.negOnePow : R)) := by
  -- Proof comment: rewrite the shifted exponent as one extra copy of `q`, then split the sign.
  rw [show q * (p' + 1) = q * p' + q by ring]
  exact castNegOnePowAdd (R := R) (q * p') q

/-- Helper for Definition 22.3.4: any `(-1)^n` coefficient squares to `1` after mapping into
the coefficient ring. -/
private theorem negOnePow_mul_self (n : ℤ) :
    (((n.negOnePow : ℤ) : R) * ((n.negOnePow : ℤ) : R)) = 1 := by
  -- Proof comment: `n.negOnePow` is always either `1` or `-1`, so its square is `1`.
  rcases Int.even_or_odd n with hEven | hOdd
  · simp [Int.negOnePow_even, hEven]
  · simp [Int.negOnePow_odd, hOdd]

/-- Helper for Definition 22.3.4: transport in the total tensor complex preserves addition on
each homogeneous piece. -/
private theorem tensorProductXCast_add {i i' : ℤ} (h : i = i')
    (x y : (tensorProductComplex A B).X i) :
    cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u)) h) (x + y) =
      cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u)) h) x +
        cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u)) h) y := by
  -- Proof comment: once the degree equality is identified, the cast is definitional.
  cases h
  rfl

/-- Helper for Definition 22.3.4: transport in the total tensor complex commutes with scalar
multiplication on each homogeneous piece. -/
private theorem tensorProductXCast_smul {i i' : ℤ} (h : i = i') (r : R)
    (x : (tensorProductComplex A B).X i) :
    cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u)) h) (r • x) =
      r • cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u)) h) x := by
  -- Proof comment: once the degree equality is identified, the cast is definitional.
  cases h
  rfl

/-- Helper for Definition 22.3.4: casts in the tensor-product complex depend only on their
endpoints, not on the chosen proof term of the degree equality. -/
private theorem tensorProductXCast_congr {i i' : ℤ}
    (h h' : i = i') (x : (tensorProductComplex A B).X i) :
    cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u)) h) x =
      cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u)) h') x := by
  -- Proof comment: all such casts are definitionally identical after substituting the endpoint
  -- equality.
  cases h
  cases h'
  rfl

/-- Helper for Definition 22.3.4: applying an `eqToHom` in the tensor-product complex is the
corresponding type-level cast on the underlying homogeneous element. -/
private theorem tensorProductXEqToHom_apply {i i' : ℤ}
    (h : i = i') (x : (tensorProductComplex A B).X i) :
    (ModuleCat.Hom.hom (eqToHom (congrArg (tensorProductComplex A B).X h))) x =
      cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u)) h) x := by
  -- Proof comment: after substituting the degree equality, the transport is definitional.
  cases h
  rfl

/-- Helper for Definition 22.3.4: after changing only the total-degree witness, a summand
inclusion evaluates to the same element of the tensor totalization. -/
private theorem tensorProductSummandCast_apply
    (p q n n' : ℤ) (h : n = n') (hpq : p + q = n) (hpq' : p + q = n')
    (x : ↑(A.X p ⊗ B.X q)) :
    cast (congrArg (fun t : ℤ ↦ ((tensorProductComplex A B).X t : Type u)) h)
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p q n hpq).hom x) =
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p q n' hpq').hom x) := by
  -- Proof comment: only the target degree changes, so the summand inclusion is definitionally
  -- the same after substituting the equality.
  subst n'
  cases hpq
  cases hpq'
  rfl

/-- Helper for Definition 22.3.4: changing the source summand indices of an included pure tensor
only transports the two homogeneous factors. -/
private theorem tensorProductSummandSourceCast_apply
    {p p' q q' n : ℤ} (hp : p = p') (hq : q = q')
    (hpq : p + q = n) (hp'q' : p' + q' = n) (a : A.X p) (b : B.X q) :
    (ιTensorObj A.toCochainComplex B.toCochainComplex p q n hpq).hom (a ⊗ₜ[R] b) =
      (ιTensorObj A.toCochainComplex B.toCochainComplex p' q' n hp'q').hom
        ((cast (congrArg (fun t : ℤ ↦ (A.X t : Type u)) hp) a) ⊗ₜ[R]
          (cast (congrArg (fun t : ℤ ↦ (B.X t : Type u)) hq) b)) := by
  -- Proof comment: after substituting the source equalities, only the witness for the common
  -- target degree remains, and both inclusions are definitionally identical.
  subst p'
  subst q'
  cases hpq
  cases hp'q'
  rfl

/-- Helper for Definition 22.3.4: on homogeneous pure tensors, the raw tensor-product
multiplication is the expected Koszul-signed pure tensor. -/
private theorem tensorProductMulOnSummandsValue_eq
    (p q p' q' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    tensorProductMulOnSummandsValue A B p q p' q' (a ⊗ₜ[R] b) (a' ⊗ₜ[R] b') =
      ((q * p').negOnePow : R) •
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') (q + q')
            ((p + q) + (p' + q')) (by abel_nf)).hom
          ((A.mul p p' a a') ⊗ₜ[R] (B.mul q q' b b'))) := by
  -- Proof comment: unfold the component composite once and let the `ModuleCat` tensor formulas
  -- evaluate the associator, braiding, and bilinear lifts on the chosen pure tensor.
  -- TODO: after exposing the middle `tensorμ`-style permutation as a named helper, this should
  -- become a flat `simp` evaluation of the associator/braiding composite on a pure tensor.
  sorry

/-- Helper for Definition 22.3.4: on homogeneous pure tensors, the raw tensor-product
multiplication is the expected Koszul-signed pure tensor. -/
private theorem tensorProductMul_apply_on_pureTensors
    (n m p q p' q' : ℤ) (hpq : p + q = n) (hp'q' : p' + q' = m)
    (hppqq : (p + p') + (q + q') = n + m)
    (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    tensorProductMul A B n m
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p q n hpq).hom (a ⊗ₜ[R] b))
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' m hp'q').hom (a' ⊗ₜ[R] b')) =
        ((q * p').negOnePow : R) •
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') (q + q') (n + m) hppqq).hom
            ((A.mul p p' a a') ⊗ₜ[R] (B.mul q q' b b'))) := by
  subst n
  subst m
  -- Proof comment: first evaluate the descender-level multiplication on the chosen summands, then
  -- rewrite that value by the pure-tensor component formula, and finally replace only the proof
  -- term witnessing the target total degree.
  have hcast :
      ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') (q + q')
          ((p + q) + (p' + q')) (by abel_nf)).hom
        ((A.mul p p' a a') ⊗ₜ[R] (B.mul q q' b b'))) =
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') (q + q')
          ((p + q) + (p' + q')) hppqq).hom
          ((A.mul p p' a a') ⊗ₜ[R] (B.mul q q' b b'))) := by
    simpa using
      (tensorProductSummandCast_apply (A := A) (B := B) (p := p + p') (q := q + q')
        (n := (p + q) + (p' + q')) (n' := (p + q) + (p' + q')) rfl (by abel_nf) hppqq
        ((A.mul p p' a a') ⊗ₜ[R] (B.mul q q' b b')))
  calc
    tensorProductMul A B (p + q) (p' + q')
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom (a ⊗ₜ[R] b))
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom
          (a' ⊗ₜ[R] b')) =
      tensorProductMulOnSummandsValue A B p q p' q' (a ⊗ₜ[R] b) (a' ⊗ₜ[R] b') := by
        simpa using
          (tensorProductMul_apply_on_summands_raw (A := A) (B := B) p q p' q'
            (a ⊗ₜ[R] b) (a' ⊗ₜ[R] b'))
    _ =
      ((q * p').negOnePow : R) •
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') (q + q')
            ((p + q) + (p' + q')) (by abel_nf)).hom
          ((A.mul p p' a a') ⊗ₜ[R] (B.mul q q' b b'))) := by
        simpa using
          (tensorProductMulOnSummandsValue_eq (A := A) (B := B) p q p' q' a b a' b')
    _ =
      ((q * p').negOnePow : R) •
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') (q + q')
            ((p + q) + (p' + q')) hppqq).hom
          ((A.mul p p' a a') ⊗ₜ[R] (B.mul q q' b b'))) := by
        rw [hcast]

/-- Helper for Definition 22.3.4: on homogeneous pure tensors, the tensor-product differential is
`d_A ⊗ 1 + (-1)^p (1 ⊗ d_B)`. -/
private theorem tensorProductComplex_d_apply_on_pureTensors
    (n p q : ℤ) (hpq : p + q = n) (hp1q : (p + 1) + q = n + 1)
    (hpq1 : p + (q + 1) = n + 1) (a : A.X p) (b : B.X q) :
    (tensorProductComplex A B).d n (n + 1)
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p q n hpq).hom (a ⊗ₜ[R] b)) =
      ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + 1) q (n + 1) hp1q).hom
          (A.d p a ⊗ₜ[R] b)) +
        p.negOnePow •
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p (q + 1) (n + 1) hpq1).hom
            (a ⊗ₜ[R] B.d q b)) := by
  subst n
  -- Proof comment: evaluate the tensor differential component formula on the chosen pure tensor.
  have hd :=
    congrArg
      (fun f :
        A.X p ⊗ B.X q ⟶ (tensorProductComplex A B).X (p + q + 1) ↦
        f.hom (a ⊗ₜ[R] b))
      (tensorObj_d_on_summand_eq (K := A.toCochainComplex) (L := B.toCochainComplex) p q)
  simpa [tensorProductComplex, CochainDGAlgebra.d, Category.assoc] using hd

/-- Helper for Definition 22.3.4: the left-associated pure-tensor product term used in the
associativity comparison. -/
private def tensorProductMulAssocPureLeft
    (p q p' q' p'' q'' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q')
    (a'' : A.X p'') (b'' : B.X q'') :
    (tensorProductComplex A B).X ((p + q) + ((p' + q') + (p'' + q''))) :=
  cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u))
      (add_assoc (p + q) (p' + q') (p'' + q'')))
    (tensorProductMul A B ((p + q) + (p' + q')) (p'' + q'')
      (tensorProductMul A B (p + q) (p' + q')
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom
          (a ⊗ₜ[R] b))
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom
          (a' ⊗ₜ[R] b')))
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p'' q'' (p'' + q'') rfl).hom
        (a'' ⊗ₜ[R] b'')))

/-- Helper for Definition 22.3.4: the right-associated pure-tensor product term used in the
associativity comparison. -/
private def tensorProductMulAssocPureRight
    (p q p' q' p'' q'' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q')
    (a'' : A.X p'') (b'' : B.X q'') :
    (tensorProductComplex A B).X ((p + q) + ((p' + q') + (p'' + q''))) :=
  tensorProductMul A B (p + q) ((p' + q') + (p'' + q''))
    ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom
      (a ⊗ₜ[R] b))
    (tensorProductMul A B (p' + q') (p'' + q'')
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom
        (a' ⊗ₜ[R] b'))
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p'' q'' (p'' + q'') rfl).hom
        (a'' ⊗ₜ[R] b'')))

/-- Helper for Definition 22.3.4: the left-associated pure product rewrites to a single common
summand with the product of the two Koszul coefficients. -/
private theorem tensorProductMulAssocPureLeft_normalized
    (p q p' q' p'' q'' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q')
    (a'' : A.X p'') (b'' : B.X q'') :
    tensorProductMulAssocPureLeft A B p q p' q' p'' q'' a b a' b' a'' b'' =
      ((((q * p').negOnePow : R) * (((q + q') * p'').negOnePow : R)) •
        ((ιTensorObj A.toCochainComplex B.toCochainComplex ((p + p') + p'')
            ((q + q') + q'') ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
            ((A.mul (p + p') p'' (A.mul p p' a a') a'') ⊗ₜ[R]
              (B.mul (q + q') q'' (B.mul q q' b b') b'')))) := by
  -- Proof comment: compute the inner product on pure tensors, push its scalar through the outer
  -- multiplication, then evaluate the outer pure product and cast once to the common total degree.
  -- TODO: normalize the outer casted scalar action with `tensorProductXCast_smul`, then rewrite
  -- the inner and outer pure products through `tensorProductMul_apply_on_pureTensors`.
  sorry

/-- Helper for Definition 22.3.4: the right-associated pure product rewrites to the same common
summand with the regrouped Koszul coefficients. -/
private theorem tensorProductMulAssocPureRight_normalized
    (p q p' q' p'' q'' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q')
    (a'' : A.X p'') (b'' : B.X q'') :
    tensorProductMulAssocPureRight A B p q p' q' p'' q'' a b a' b' a'' b'' =
      ((((q * (p' + p'')).negOnePow : R) * ((q' * p'').negOnePow : R)) •
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + (p' + p''))
            (q + (q' + q'')) ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
          ((A.mul p (p' + p'') a (A.mul p' p'' a' a'')) ⊗ₜ[R]
            (B.mul q (q' + q'') b (B.mul q' q'' b' b''))))) := by
  -- Proof comment: evaluate the inner right-associated product first, push its scalar through the
  -- second argument of the outer multiplication, then compute the outer pure product.
  unfold tensorProductMulAssocPureRight
  have hinner :
      tensorProductMul A B (p' + q') (p'' + q'')
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom
          (a' ⊗ₜ[R] b'))
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p'' q'' (p'' + q'') rfl).hom
          (a'' ⊗ₜ[R] b'')) =
        ((q' * p'').negOnePow : R) •
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p' + p'') (q' + q'')
              ((p' + q') + (p'' + q'')) (by abel_nf)).hom
            ((A.mul p' p'' a' a'') ⊗ₜ[R] (B.mul q' q'' b' b''))) := by
    simpa using
      (tensorProductMul_apply_on_pureTensors (A := A) (B := B) (n := p' + q')
        (m := p'' + q'') (p := p') (q := q') (p' := p'') (q' := q'') rfl rfl (by abel_nf)
        a' b' a'' b'')
  have houter :
      tensorProductMul A B (p + q) ((p' + q') + (p'' + q''))
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom
          (a ⊗ₜ[R] b))
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p' + p'') (q' + q'')
            ((p' + q') + (p'' + q'')) (by abel_nf)).hom
          ((A.mul p' p'' a' a'') ⊗ₜ[R] (B.mul q' q'' b' b''))) =
        ((q * (p' + p'')).negOnePow : R) •
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + (p' + p''))
              (q + (q' + q'')) ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
            ((A.mul p (p' + p'') a (A.mul p' p'' a' a'')) ⊗ₜ[R]
              (B.mul q (q' + q'') b (B.mul q' q'' b' b'')))) := by
    simpa using
      (tensorProductMul_apply_on_pureTensors (A := A) (B := B) (n := p + q)
        (m := (p' + q') + (p'' + q'')) (p := p) (q := q) (p' := p' + p'')
        (q' := q' + q'') rfl (by abel_nf) (by abel_nf) a b (A.mul p' p'' a' a'')
        (B.mul q' q'' b' b''))
  calc
    tensorProductMul A B (p + q) ((p' + q') + (p'' + q''))
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom
          (a ⊗ₜ[R] b))
        (tensorProductMul A B (p' + q') (p'' + q'')
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom
            (a' ⊗ₜ[R] b'))
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p'' q'' (p'' + q'') rfl).hom
            (a'' ⊗ₜ[R] b''))) =
      tensorProductMul A B (p + q) ((p' + q') + (p'' + q''))
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom
          (a ⊗ₜ[R] b))
        (((q' * p'').negOnePow : R) •
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p' + p'') (q' + q'')
              ((p' + q') + (p'' + q'')) (by abel_nf)).hom
            ((A.mul p' p'' a' a'') ⊗ₜ[R] (B.mul q' q'' b' b'')))) := by
      rw [hinner]
    _ =
      ((q' * p'').negOnePow : R) •
        tensorProductMul A B (p + q) ((p' + q') + (p'' + q''))
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom
            (a ⊗ₜ[R] b))
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p' + p'') (q' + q'')
              ((p' + q') + (p'' + q'')) (by abel_nf)).hom
            ((A.mul p' p'' a' a'') ⊗ₜ[R] (B.mul q' q'' b' b''))) := by
      simp
    _ =
      ((q' * p'').negOnePow : R) •
        (((q * (p' + p'')).negOnePow : R) •
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + (p' + p''))
              (q + (q' + q'')) ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
            ((A.mul p (p' + p'') a (A.mul p' p'' a' a'')) ⊗ₜ[R]
              (B.mul q (q' + q'') b (B.mul q' q'' b' b''))))) := by
      rw [houter]
    _ =
      ((((q' * p'').negOnePow : R) * ((q * (p' + p'')).negOnePow : R)) •
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + (p' + p''))
            (q + (q' + q'')) ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
          ((A.mul p (p' + p'') a (A.mul p' p'' a' a'')) ⊗ₜ[R]
            (B.mul q (q' + q'') b (B.mul q' q'' b' b''))))) := by
      rw [smul_smul]
    _ =
      ((((q * (p' + p'')).negOnePow : R) * ((q' * p'').negOnePow : R)) •
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + (p' + p''))
            (q + (q' + q'')) ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
          ((A.mul p (p' + p'') a (A.mul p' p'' a' a'')) ⊗ₜ[R]
            (B.mul q (q' + q'') b (B.mul q' q'' b' b''))))) := by
      ring_nf

/-- Helper for Definition 22.3.4: the tensor-product multiplication is associative on homogeneous
pure tensors once both sides are rewritten to one common source summand and total degree. -/
private theorem tensorProductMulAssocOnPureTensors
    (p q p' q' p'' q'' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q')
    (a'' : A.X p'') (b'' : B.X q'') :
    tensorProductMulAssocPureLeft A B p q p' q' p'' q'' a b a' b' a'' b'' =
      tensorProductMulAssocPureRight A B p q p' q' p'' q'' a b a' b' a'' b'' := by
  -- Proof comment: normalize both iterated products to one final summand, rewrite the source
  -- factors with the associativity laws in `A` and `B`, then compare the two scalar coefficients.
  have hsource :
      ((ιTensorObj A.toCochainComplex B.toCochainComplex ((p + p') + p'') ((q + q') + q'')
          ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
        ((A.mul (p + p') p'' (A.mul p p' a a') a'') ⊗ₜ[R]
          (B.mul (q + q') q'' (B.mul q q' b b') b''))) =
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + (p' + p'')) (q + (q' + q''))
            ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
          ((cast (congrArg (fun t : ℤ ↦ (A.X t : Type u)) (add_assoc p p' p''))
              (A.mul (p + p') p'' (A.mul p p' a a') a'')) ⊗ₜ[R]
            (cast (congrArg (fun t : ℤ ↦ (B.X t : Type u)) (add_assoc q q' q''))
              (B.mul (q + q') q'' (B.mul q q' b b') b'')))) := by
    simpa using
      (tensorProductSummandSourceCast_apply (A := A) (B := B) (p := (p + p') + p'')
        (p' := p + (p' + p'')) (q := (q + q') + q'') (q' := q + (q' + q''))
        (n := (p + q) + ((p' + q') + (p'' + q''))) (hp := add_assoc p p' p'')
        (hq := add_assoc q q' q'') (hpq := by abel_nf) (hp'q' := by abel_nf)
        (a := A.mul (p + p') p'' (A.mul p p' a a') a'')
        (b := B.mul (q + q') q'' (B.mul q q' b b') b''))
  have hA :
      cast (congrArg (fun t : ℤ ↦ (A.X t : Type u)) (add_assoc p p' p''))
        (A.mul (p + p') p'' (A.mul p p' a a') a'') =
          A.mul p (p' + p'') a (A.mul p' p'' a' a'') := by
    simpa using (A.mul_assoc_apply p p' p'' a a' a'')
  have hB :
      cast (congrArg (fun t : ℤ ↦ (B.X t : Type u)) (add_assoc q q' q''))
        (B.mul (q + q') q'' (B.mul q q' b b') b'') =
          B.mul q (q' + q'') b (B.mul q' q'' b' b'') := by
    simpa using (B.mul_assoc_apply q q' q'' b b' b'')
  calc
    tensorProductMulAssocPureLeft A B p q p' q' p'' q'' a b a' b' a'' b'' =
      ((((q * p').negOnePow : R) * (((q + q') * p'').negOnePow : R)) •
        ((ιTensorObj A.toCochainComplex B.toCochainComplex ((p + p') + p'')
            ((q + q') + q'') ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
          ((A.mul (p + p') p'' (A.mul p p' a a') a'') ⊗ₜ[R]
            (B.mul (q + q') q'' (B.mul q q' b b') b'')))) := by
      simpa using
        (tensorProductMulAssocPureLeft_normalized (A := A) (B := B) p q p' q' p'' q''
          a b a' b' a'' b'')
    _ =
      ((((q * p').negOnePow : R) * (((q + q') * p'').negOnePow : R)) •
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + (p' + p'')) (q + (q' + q''))
            ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
          ((A.mul p (p' + p'') a (A.mul p' p'' a' a'')) ⊗ₜ[R]
            (B.mul q (q' + q'') b (B.mul q' q'' b' b''))))) := by
      rw [hsource, hA, hB]
    _ =
      ((((q * (p' + p'')).negOnePow : R) * ((q' * p'').negOnePow : R)) •
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + (p' + p'')) (q + (q' + q''))
            ((p + q) + ((p' + q') + (p'' + q''))) (by abel_nf)).hom
          ((A.mul p (p' + p'') a (A.mul p' p'' a' a'')) ⊗ₜ[R]
            (B.mul q (q' + q'') b (B.mul q' q'' b' b''))))) := by
      rw [tensorProductMulAssocSign]
    _ =
      tensorProductMulAssocPureRight A B p q p' q' p'' q'' a b a' b' a'' b'' := by
      symm
      simpa using
        (tensorProductMulAssocPureRight_normalized (A := A) (B := B) p q p' q' p'' q''
          a b a' b' a'' b'')

/-- Helper for Definition 22.3.4: the differential of the product of two pure tensors. -/
private def tensorProductLeibnizPureLeft
    (p q p' q' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    (tensorProductComplex A B).X (((p + q) + (p' + q')) + 1) :=
  (tensorProductComplex A B).d ((p + q) + (p' + q')) (((p + q) + (p' + q')) + 1)
    (tensorProductMul A B (p + q) (p' + q')
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom
        (a ⊗ₜ[R] b))
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom
        (a' ⊗ₜ[R] b')))

/-- Helper for Definition 22.3.4: the Leibniz-rule expansion for the product of two pure tensors.
-/
private def tensorProductLeibnizPureRight
    (p q p' q' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    (tensorProductComplex A B).X (((p + q) + (p' + q')) + 1) :=
  cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u))
      (cochainDGAlgebra_leftLeibniz_index (p + q) (p' + q')))
    (tensorProductMul A B ((p + q) + 1) (p' + q')
      ((tensorProductComplex A B).d (p + q) (p + q + 1)
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom
          (a ⊗ₜ[R] b)))
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom
        (a' ⊗ₜ[R] b'))) +
    ((p + q).negOnePow : R) •
      cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u))
          (cochainDGAlgebra_rightLeibniz_index (p + q) (p' + q')))
        (tensorProductMul A B (p + q) ((p' + q') + 1)
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom
            (a ⊗ₜ[R] b))
          ((tensorProductComplex A B).d (p' + q') (p' + q' + 1)
            ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom
              (a' ⊗ₜ[R] b'))))

/-- Helper for Definition 22.3.4: a single common four-branch normal form for the pure Leibniz
comparison in total degree `((p + q) + (p' + q')) + 1`. -/
private def tensorProductLeibnizPureNormalized
    (p q p' q' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    (tensorProductComplex A B).X (((p + q) + (p' + q')) + 1) :=
  ((q * p').negOnePow : R) •
      ((ιTensorObj A.toCochainComplex B.toCochainComplex ((p + 1) + p') (q + q')
          (((p + q) + (p' + q')) + 1) (by abel_nf)).hom
        ((A.mul (p + 1) p' (A.d p a) a') ⊗ₜ[R] (B.mul q q' b b'))) +
    (((q * p').negOnePow : R) * (p.negOnePow : R)) •
      ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + (p' + 1)) (q + q')
          (((p + q) + (p' + q')) + 1) (by abel_nf)).hom
        ((A.mul p (p' + 1) a (A.d p' a')) ⊗ₜ[R] (B.mul q q' b b'))) +
    (((q * p').negOnePow : R) * (((p + p').negOnePow : ℤ) : R)) •
      ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') ((q + 1) + q')
          (((p + q) + (p' + q')) + 1) (by abel_nf)).hom
        ((A.mul p p' a a') ⊗ₜ[R] (B.mul (q + 1) q' (B.d q b) b'))) +
    ((((q * p').negOnePow : R) * (((p + p').negOnePow : ℤ) : R)) * (q.negOnePow : R)) •
      ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') (q + (q' + 1))
          (((p + q) + (p' + q')) + 1) (by abel_nf)).hom
        ((A.mul p p' a a') ⊗ₜ[R] (B.mul q (q' + 1) b (B.d q' b'))))

/-- Helper for Definition 22.3.4: the third normalized Leibniz coefficient is the product-side
`(-1)^{q p'}` sign together with the cochain sign `(-1)^{p + p'}`. -/
private theorem tensorProductLeibnizThirdCoeff (p q p' : ℤ) :
    ((q * p').negOnePow : R) * (((p + p').negOnePow : ℤ) : R) =
      (((q * p').negOnePow : R) * (p.negOnePow : R)) * (p'.negOnePow : R) := by
  -- Proof comment: split the cochain sign `(-1)^{p + p'}` once, then reorder coefficients in the
  -- commutative base ring.
  rw [castNegOnePowAdd (R := R) p p']
  ring

/-- Helper for Definition 22.3.4: the right-hand Leibniz term where the second pure tensor
contributes `d a'` simplifies to the left-normalized coefficient. -/
private theorem tensorProductLeibnizRightSecondCoeff (p q p' : ℤ) :
    ((p + q).negOnePow : R) * ((((q * (p' + 1)).negOnePow : ℤ) : R)) =
      ((q * p').negOnePow : R) * (p.negOnePow : R) := by
  -- Proof comment: the shifted multiplication sign contributes one extra `(-1)^q`, which cancels
  -- the `(-1)^q` coming from the outer Leibniz sign.
  rw [tensorProductMulShiftRightSign (R := R) q p']
  rw [castNegOnePowAdd (R := R) p q]
  calc
    (p.negOnePow : R) * (q.negOnePow : R) * (((q * p').negOnePow : R) * (q.negOnePow : R)) =
      (p.negOnePow : R) * (((q.negOnePow : R) * (q.negOnePow : R)) * ((q * p').negOnePow : R)) := by
        ring
    _ = (p.negOnePow : R) * ((q * p').negOnePow : R) := by
      rw [negOnePow_mul_self (R := R) q]
      ring
    _ = ((q * p').negOnePow : R) * (p.negOnePow : R) := by
      ring

/-- Helper for Definition 22.3.4: the right-hand Leibniz term where the first pure tensor
contributes `d b` simplifies to the left-normalized third coefficient. -/
private theorem tensorProductLeibnizRightThirdCoeff (p q p' : ℤ) :
    (p.negOnePow : R) * ((((q + 1) * p').negOnePow : ℤ) : R) =
      ((q * p').negOnePow : R) * (((p + p').negOnePow : ℤ) : R) := by
  -- Proof comment: shifting the left `B`-degree contributes one extra `(-1)^{p'}`, and that
  -- combines with the existing `(-1)^p` into `(-1)^{p + p'}`.
  rw [tensorProductMulShiftLeftSign (R := R) q p']
  rw [castNegOnePowAdd (R := R) p p']
  ring

/-- Helper for Definition 22.3.4: the right-hand Leibniz term where the second pure tensor
contributes `d b'` simplifies to the left-normalized fourth coefficient. -/
private theorem tensorProductLeibnizRightFourthCoeff (p q p' : ℤ) :
    (((p + q).negOnePow : R) * (p'.negOnePow : R)) * ((q * p').negOnePow : R) =
      (((q * p').negOnePow : R) * (((p + p').negOnePow : ℤ) : R)) * (q.negOnePow : R) := by
  -- Proof comment: split both cochain signs once and use `(-1)^q * (-1)^q = 1` to remove the
  -- duplicated `q`-factor.
  rw [castNegOnePowAdd (R := R) p q]
  rw [castNegOnePowAdd (R := R) p p']
  ring

/-- Helper for Definition 22.3.4: after differentiating the `A`-factor of the already multiplied
pure tensor, the two resulting terms match the first two normalized Leibniz branches. -/
private theorem tensorProductLeibnizProductDifferentialA
    (p q p' q' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    ((ιTensorObj A.toCochainComplex B.toCochainComplex ((p + p') + 1) (q + q')
        (((p + q) + (p' + q')) + 1) (by abel_nf)).hom
      ((A.d (p + p') (A.mul p p' a a')) ⊗ₜ[R] (B.mul q q' b b'))) =
      ((ιTensorObj A.toCochainComplex B.toCochainComplex ((p + 1) + p') (q + q')
          (((p + q) + (p' + q')) + 1) (by abel_nf)).hom
        ((A.mul (p + 1) p' (A.d p a) a') ⊗ₜ[R] (B.mul q q' b b'))) +
        p.negOnePow •
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + (p' + 1)) (q + q')
              (((p + q) + (p' + q')) + 1) (by abel_nf)).hom
            ((A.mul p (p' + 1) a (A.d p' a')) ⊗ₜ[R] (B.mul q q' b b'))) := by
  -- Proof comment: apply `A.leibniz_apply` before entering the tensor totalization, then rewrite
  -- each transported source summand to the normalized `((p + 1) + p')` and `(p + (p' + 1))`
  -- source indices.
  -- TODO: apply `A.leibniz_apply` before entering the tensor totalization, distribute the pure
  -- tensor over the resulting sum, and rewrite the two transported source summands via
  -- `tensorProductSummandSourceCast_apply`.
  sorry

/-- Helper for Definition 22.3.4: after differentiating the `B`-factor of the already multiplied
pure tensor, the two resulting terms match the last two normalized Leibniz branches. -/
private theorem tensorProductLeibnizProductDifferentialB
    (p q p' q' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') ((q + q') + 1)
        (((p + q) + (p' + q')) + 1) (by abel_nf)).hom
      ((A.mul p p' a a') ⊗ₜ[R] (B.d (q + q') (B.mul q q' b b')))) =
      ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') ((q + 1) + q')
          (((p + q) + (p' + q')) + 1) (by abel_nf)).hom
        ((A.mul p p' a a') ⊗ₜ[R] (B.mul (q + 1) q' (B.d q b) b'))) +
        q.negOnePow •
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + p') (q + (q' + 1))
              (((p + q) + (p' + q')) + 1) (by abel_nf)).hom
            ((A.mul p p' a a') ⊗ₜ[R] (B.mul q (q' + 1) b (B.d q' b')))) := by
  -- Proof comment: this is the same normalization on the `B`-factor, now using `B.leibniz_apply`
  -- and changing only the second source index of the summand inclusion.
  -- TODO: apply `B.leibniz_apply` before entering the tensor totalization, distribute the fixed
  -- left tensor factor over the sum, and normalize the two `B`-source transports by
  -- `tensorProductSummandSourceCast_apply`.
  sorry

/-- Helper for Definition 22.3.4: the product-then-differentiate pure Leibniz term rewrites to
the common four-branch normal form. -/
private theorem tensorProductLeibnizPureLeft_normalized
    (p q p' q' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    tensorProductLeibnizPureLeft A B p q p' q' a b a' b' =
      tensorProductLeibnizPureNormalized A B p q p' q' a b a' b' := by
  -- Proof comment: compute the pure product once, differentiate that pure tensor, and then
  -- replace the differentiated `A`- and `B`-branches by the two branch-expansion lemmas.
  -- TODO: rewrite the pure product once, apply the tensor differential to that pure tensor, and
  -- then substitute the two differentiated-product branch lemmas.
  sorry

/-- Helper for Definition 22.3.4: the differentiate-then-multiply pure Leibniz term rewrites to
the same common four-branch normal form. -/
private theorem tensorProductLeibnizPureRight_normalized
    (p q p' q' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    tensorProductLeibnizPureRight A B p q p' q' a b a' b' =
      tensorProductLeibnizPureNormalized A B p q p' q' a b a' b' := by
  -- Proof comment: expand both input differentials on pure tensors, distribute the two products,
  -- and rewrite each of the four resulting pure branches to the common normal form.
  -- TODO: expand both differentials by `tensorProductComplex_d_apply_on_pureTensors`, distribute
  -- the two multiplications over the resulting sums, rewrite each of the four pure branches by
  -- `tensorProductMul_apply_on_pureTensors`, and normalize the coefficient casts with
  -- `tensorProductLeibnizRightSecondCoeff`, `tensorProductLeibnizThirdCoeff`, and
  -- `tensorProductLeibnizRightFourthCoeff`.
  sorry

/-- Helper for Definition 22.3.4: the tensor-product differential satisfies the cochain Leibniz
rule on homogeneous pure tensors once the four resulting branches are normalized to one common
source-summand shape. -/
private theorem tensorProductLeibnizOnPureTensors
    (p q p' q' : ℤ) (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    tensorProductLeibnizPureLeft A B p q p' q' a b a' b' =
      tensorProductLeibnizPureRight A B p q p' q' a b a' b' := by
  -- Route correction: the outer homogeneous Leibniz induction is already correct; the remaining
  -- work is the pure case, where both sides are rewritten to
  -- `tensorProductLeibnizPureNormalized` and then compared by transitivity.
  calc
    tensorProductLeibnizPureLeft A B p q p' q' a b a' b' =
        tensorProductLeibnizPureNormalized A B p q p' q' a b a' b' := by
      -- Proof comment: normalize the product-then-differentiate side to the common four-term form.
      simpa using
        (tensorProductLeibnizPureLeft_normalized (A := A) (B := B) p q p' q' a b a' b')
    _ =
        tensorProductLeibnizPureRight A B p q p' q' a b a' b' := by
      -- Proof comment: normalize the differentiate-then-product side to the same four-term form.
      symm
      simpa using
        (tensorProductLeibnizPureRight_normalized (A := A) (B := B) p q p' q' a b a' b')

/-- Helper for Definition 22.3.4: left multiplication by the tensor-product unit, viewed as an
endomorphism of the total degree-`n` term. -/
private def tensorProductOneMulHom (n : ℤ) :
    (tensorProductComplex A B).X n ⟶ (tensorProductComplex A B).X n :=
  ModuleCat.ofHom ((tensorProductMulDesc A B 0 n).hom (tensorProductOne A B)) ≫
    eqToHom (congrArg (tensorProductComplex A B).X (zero_add n))

/-- Helper for Definition 22.3.4: left multiplication by the tensor-product unit fixes each
chosen homogeneous summand. -/
private theorem tensorProductOneMulOnSummand
    (n p q : ℤ) (h : p + q = n) (x : ↑(A.X p ⊗ B.X q)) :
    (ιTensorObj A.toCochainComplex B.toCochainComplex p q n h ≫
        tensorProductOneMulHom A B n).hom x =
      (ιTensorObj A.toCochainComplex B.toCochainComplex p q n h).hom x := by
  -- Proof comment: reduce to pure tensors and compute left multiplication by the tensor-product
  -- unit using the pure-tensor multiplication formula.
  -- TODO: reduce to pure tensors, compute left multiplication by the tensor-product unit on a
  -- pure tensor, and then transport the source indices back using the unit laws in `A` and `B`.
  sorry

/-- Helper for Definition 22.3.4: the left-unit endomorphism on total degree `n` is the identity.
-/
private theorem tensorProductOneMulHom_eq_id (n : ℤ) :
    tensorProductOneMulHom A B n = 𝟙 ((tensorProductComplex A B).X n) := by
  -- Proof comment: the tensor totalization is generated by the summand inclusions `ιTensorObj`.
  refine HomologicalComplex.mapBifunctor.hom_ext (j := n) (fun p q h ↦ ?_)
  ext x
  simpa [Category.assoc] using tensorProductOneMulOnSummand A B n p q h x

/-- Helper for Definition 22.3.4: right multiplication by the tensor-product unit, viewed as an
endomorphism of the total degree-`n` term. -/
private def tensorProductMulOneHom (n : ℤ) :
    (tensorProductComplex A B).X n ⟶ (tensorProductComplex A B).X n :=
  tensorProductMulDesc A B n 0 ≫
    ModuleCat.ofHom
      { toFun := fun f ↦ f (tensorProductOne A B)
        map_add' := by
          intro f g
          rfl
        map_smul' := by
          intro r f
          rfl } ≫
    eqToHom (congrArg (tensorProductComplex A B).X (add_zero n))

/-- Helper for Definition 22.3.4: right multiplication by the tensor-product unit fixes each
chosen homogeneous summand. -/
private theorem tensorProductMulOneOnSummand
    (n p q : ℤ) (h : p + q = n) (x : ↑(A.X p ⊗ B.X q)) :
    (ιTensorObj A.toCochainComplex B.toCochainComplex p q n h ≫
        tensorProductMulOneHom A B n).hom x =
      (ιTensorObj A.toCochainComplex B.toCochainComplex p q n h).hom x := by
  -- Proof comment: again reduce to pure tensors, but now use the multiplication formula for
  -- `(a ⊗ b) * (A.one ⊗ B.one)` and transport the source indices back with the right unit laws.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [tensorProductMulOneHom]
  · intro a b
    have hone :
        tensorProductOne A B =
          (ιTensorObj A.toCochainComplex B.toCochainComplex 0 0 0 rfl).hom
            (A.one ⊗ₜ[R] B.one) := by
      simp [tensorProductOne, tensorProductUnitHom]
    have hmul :
        tensorProductMul A B n 0
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p q n h).hom (a ⊗ₜ[R] b))
          (tensorProductOne A B) =
            ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + 0) (q + 0) (n + 0)
                (by simpa [h] using h)).hom
              ((A.mul p 0 a A.one) ⊗ₜ[R] (B.mul q 0 b B.one))) := by
      rw [hone]
      simpa using
        (tensorProductMul_apply_on_pureTensors (A := A) (B := B) (n := n) (m := 0)
          (p := p) (q := q) (p' := 0) (q' := 0) h rfl (by simpa [h] using h) a b A.one B.one)
    have htarget :
        cast (congrArg (fun i : ℤ ↦ ((tensorProductComplex A B).X i : Type u)) (add_zero n))
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + 0) (q + 0) (n + 0)
              (by simpa [h] using h)).hom
            ((A.mul p 0 a A.one) ⊗ₜ[R] (B.mul q 0 b B.one))) =
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + 0) (q + 0) n
              (by simpa [h] using h)).hom
            ((A.mul p 0 a A.one) ⊗ₜ[R] (B.mul q 0 b B.one))) := by
      simpa using
        (tensorProductSummandCast_apply (A := A) (B := B) (p := p + 0) (q := q + 0)
          (n := n + 0) (n' := n) (add_zero n) (by simpa [h] using h) (by simpa [h] using h)
          ((A.mul p 0 a A.one) ⊗ₜ[R] (B.mul q 0 b B.one)))
    have hsource :
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + 0) (q + 0) n
            (by simpa [h] using h)).hom
          ((A.mul p 0 a A.one) ⊗ₜ[R] (B.mul q 0 b B.one))) =
          ((ιTensorObj A.toCochainComplex B.toCochainComplex p q n h).hom
            ((cast (congrArg (fun t : ℤ ↦ (A.X t : Type u)) (add_zero p))
                (A.mul p 0 a A.one)) ⊗ₜ[R]
              (cast (congrArg (fun t : ℤ ↦ (B.X t : Type u)) (add_zero q))
                (B.mul q 0 b B.one)))) := by
      simpa using
        (tensorProductSummandSourceCast_apply (A := A) (B := B) (p := p + 0) (p' := p)
          (q := q + 0) (q' := q) (n := n) (hp := add_zero p) (hq := add_zero q)
          (hpq := by simpa [h] using h) (hp'q' := h) (a := A.mul p 0 a A.one)
          (b := B.mul q 0 b B.one))
    have ha :
        cast (congrArg (fun t : ℤ ↦ (A.X t : Type u)) (add_zero p))
          (A.mul p 0 a A.one) = a := by
      simpa using (A.mul_one_apply p a)
    have hb :
        cast (congrArg (fun t : ℤ ↦ (B.X t : Type u)) (add_zero q))
          (B.mul q 0 b B.one) = b := by
      simpa using (B.mul_one_apply q b)
    calc
      (ιTensorObj A.toCochainComplex B.toCochainComplex p q n h ≫
          tensorProductMulOneHom A B n).hom (a ⊗ₜ[R] b) =
        cast (congrArg (fun i : ℤ ↦ ((tensorProductComplex A B).X i : Type u)) (add_zero n))
          (((ModuleCat.Hom.hom (tensorProductMulDesc A B n 0))
              ((ιTensorObj A.toCochainComplex B.toCochainComplex p q n h).hom (a ⊗ₜ[R] b)))
            (tensorProductOne A B)) := by
          simpa [tensorProductMulOneHom, tensorProductMul, tensorProductXEqToHom_apply]
      _ =
        cast (congrArg (fun i : ℤ ↦ ((tensorProductComplex A B).X i : Type u)) (add_zero n))
          (tensorProductMul A B n 0
            ((ιTensorObj A.toCochainComplex B.toCochainComplex p q n h).hom (a ⊗ₜ[R] b))
            (tensorProductOne A B)) := by
          rfl
      _ =
        cast (congrArg (fun i : ℤ ↦ ((tensorProductComplex A B).X i : Type u)) (add_zero n))
          ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + 0) (q + 0) (n + 0)
              (by simpa [h] using h)).hom
            ((A.mul p 0 a A.one) ⊗ₜ[R] (B.mul q 0 b B.one))) := by
          rw [hmul]
      _ =
        ((ιTensorObj A.toCochainComplex B.toCochainComplex (p + 0) (q + 0) n
            (by simpa [h] using h)).hom
          ((A.mul p 0 a A.one) ⊗ₜ[R] (B.mul q 0 b B.one))) := htarget
      _ =
        ((ιTensorObj A.toCochainComplex B.toCochainComplex p q n h).hom
          ((cast (congrArg (fun t : ℤ ↦ (A.X t : Type u)) (add_zero p))
              (A.mul p 0 a A.one)) ⊗ₜ[R]
            (cast (congrArg (fun t : ℤ ↦ (B.X t : Type u)) (add_zero q))
              (B.mul q 0 b B.one)))) := hsource
      _ = (ιTensorObj A.toCochainComplex B.toCochainComplex p q n h).hom (a ⊗ₜ[R] b) := by
          rw [ha, hb]
  · intro x y hx hy
    simpa using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Definition 22.3.4: the right-unit endomorphism on total degree `n` is the identity.
-/
private theorem tensorProductMulOneHom_eq_id (n : ℤ) :
    tensorProductMulOneHom A B n = 𝟙 ((tensorProductComplex A B).X n) := by
  -- Proof comment: the tensor totalization is generated by the summand inclusions `ιTensorObj`.
  refine HomologicalComplex.mapBifunctor.hom_ext (j := n) (fun p q h ↦ ?_)
  ext x
  simpa [Category.assoc] using tensorProductMulOneOnSummand A B n p q h x

/-- Helper for Definition 22.3.4: the tensor-product multiplication is associative on homogeneous
elements. -/
private theorem tensorProductMul_assoc
    (i j k : ℤ) (a : (tensorProductComplex A B).X i) (b : (tensorProductComplex A B).X j)
    (c : (tensorProductComplex A B).X k) :
    cast (congrArg (fun n : ℤ ↦ ((tensorProductComplex A B).X n : Type u)) (add_assoc i j k))
      (tensorProductMul A B (i + j) k (tensorProductMul A B i j a b) c) =
        tensorProductMul A B i (j + k) a (tensorProductMul A B j k b c) := by
  -- Proof comment: the total tensor complex is generated by the homogeneous summands in each
  -- degree, so associativity reduces to the pure-tensor computation by three nested inductions.
  -- TODO: once the pure associativity normalization lemmas are repaired, reduce the general
  -- associativity statement to the pure-tensor case by the standard nested induction.
  sorry

/-- Helper for Definition 22.3.4: the tensor-product unit acts by left multiplication as the
identity on each homogeneous piece. -/
private theorem tensorProduct_one_mul (n : ℤ) (a : (tensorProductComplex A B).X n) :
    cast (congrArg (fun i : ℤ ↦ ((tensorProductComplex A B).X i : Type u)) (zero_add n))
      (tensorProductMul A B 0 n (tensorProductOne A B) a) = a := by
  -- Proof comment: evaluate the left-unit endomorphism equality at `a`.
  have h :=
    congrArg
      (fun f : (tensorProductComplex A B).X n ⟶ (tensorProductComplex A B).X n ↦
        f.hom a)
      (tensorProductOneMulHom_eq_id (A := A) (B := B) n)
  simpa [tensorProductOneMulHom, tensorProductMul, tensorProductXEqToHom_apply] using h

/-- Helper for Definition 22.3.4: the tensor-product unit acts by right multiplication as the
identity on each homogeneous piece. -/
private theorem tensorProduct_mul_one (n : ℤ) (a : (tensorProductComplex A B).X n) :
    cast (congrArg (fun i : ℤ ↦ ((tensorProductComplex A B).X i : Type u)) (add_zero n))
      (tensorProductMul A B n 0 a (tensorProductOne A B)) = a := by
  -- Proof comment: this is the same endomorphism-equality argument for right multiplication by
  -- the unit.
  have h :=
    congrArg
      (fun f : (tensorProductComplex A B).X n ⟶ (tensorProductComplex A B).X n ↦
        f.hom a)
      (tensorProductMulOneHom_eq_id (A := A) (B := B) n)
  simpa [tensorProductMulOneHom, tensorProductXEqToHom_apply] using h

/-- Helper for Definition 22.3.4: the tensor-product differential satisfies the cochain Leibniz
rule on homogeneous elements. -/
private theorem tensorProduct_leibniz
    (n m : ℤ) (a : (tensorProductComplex A B).X n) (b : (tensorProductComplex A B).X m) :
    (tensorProductComplex A B).d (n + m) (n + m + 1) (tensorProductMul A B n m a b) =
      cast (congrArg (fun i : ℤ ↦ ((tensorProductComplex A B).X i : Type u))
        (cochainDGAlgebra_leftLeibniz_index n m))
        (tensorProductMul A B (n + 1) m ((tensorProductComplex A B).d n (n + 1) a) b) +
      n.negOnePow •
        cast (congrArg (fun i : ℤ ↦ ((tensorProductComplex A B).X i : Type u))
          (cochainDGAlgebra_rightLeibniz_index n m))
          (tensorProductMul A B n (m + 1) a ((tensorProductComplex A B).d m (m + 1) b)) := by
  -- Proof comment: the tensor totalization is generated in each degree by the chosen summands, so
  -- the homogeneous Leibniz rule reduces to the pure-tensor computation by two nested inductions.
  -- TODO: once the pure Leibniz theorem is stabilized, reduce the general homogeneous Leibniz
  -- rule to pure tensors by the standard two-step induction on the tensor summands.
  sorry

/-- Definition 22.3.4: the tensor product of cochain differential graded algebras. Its underlying
cochain complex is the canonical total tensor complex, with unit given by the pure tensor of the
units and multiplication given by the Koszul-signed middle swap followed by the multiplications of
`A` and `B`. -/
@[stacks 065W]
def tensorProduct : CochainDGAlgebra R where
  toCochainComplex := tensorProductComplex A B
  one := tensorProductOne A B
  mul := tensorProductMul A B
  mul_assoc := tensorProductMul_assoc (A := A) (B := B)
  one_mul := tensorProduct_one_mul (A := A) (B := B)
  mul_one := tensorProduct_mul_one (A := A) (B := B)
  leibniz := tensorProduct_leibniz (A := A) (B := B)

/-
Textbook notation for the tensor product differential graded algebra `A ⊗[R] B`.
-/
set_option quotPrecheck false in
scoped[TensorProduct] notation:70 A:70 " ⊗[" R:70 "] " B:71 =>
  @CochainDGAlgebra.tensorProduct R _ A B

/-- The tensor product differential graded algebra has the canonical total tensor complex as its
underlying cochain complex. -/
@[simp] theorem tensorProduct_toCochainComplex :
    (A ⊗[R] B).toCochainComplex =
      HomologicalComplex.tensorObj A.toCochainComplex B.toCochainComplex :=
  rfl

/-- The unit on `A ⊗[R] B` is the image of `A.one ⊗ₜ[R] B.one` in total degree `0`. -/
@[simp] theorem tensorProduct_one_eq :
    (A ⊗[R] B).one =
      (ιTensorObj A.toCochainComplex B.toCochainComplex 0 0 0 rfl).hom (A.one ⊗ₜ[R] B.one) := by
  simp [tensorProduct, tensorProductOne, tensorProductUnitHom]

/-- Companion to Definition 22.3.4: on homogeneous pure tensors, the multiplication on the
tensor-product construction is given by the Koszul-signed swap of the middle factors followed by
the multiplications of `A` and `B` on the corresponding homogeneous summands. -/
theorem tensorProduct_mul_apply_on_summands
    (p q p' q' : ℤ) (x : ↑(A.X p ⊗ B.X q)) (y : ↑(A.X p' ⊗ B.X q')) :
    (A ⊗[R] B).mul (p + q) (p' + q')
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl).hom x)
      ((ιTensorObj A.toCochainComplex B.toCochainComplex p' q' (p' + q') rfl).hom y) =
        ((α_ (A.X p) (B.X q) (A.X p' ⊗ B.X q')).hom ≫
          (A.X p ◁ (α_ (B.X q) (A.X p') (B.X q')).inv) ≫
          (A.X p ◁
            (((q * p').negOnePow • (β_ (B.X q) (A.X p')).hom) ▷ B.X q')) ≫
          (A.X p ◁ (α_ (A.X p') (B.X q) (B.X q')).hom) ≫
          (α_ (A.X p) (A.X p') (B.X q ⊗ B.X q')).inv ≫
          (ModuleCat.ofHom (TensorProduct.lift (A.mul p p')) ⊗ₘ
            ModuleCat.ofHom (TensorProduct.lift (B.mul q q'))) ≫
          ιTensorObj A.toCochainComplex B.toCochainComplex
            (p + p') (q + q') ((p + q) + (p' + q')) (by abel_nf)).hom (x ⊗ₜ[R] y) := by
  -- Proof comment: the public statement is exactly the raw summand formula with the private
  -- companion abbreviation unfolded once.
  simpa [tensorProduct, tensorProductMulOnSummandsValue, tensorProductMulComponentHom,
    tensorKoszulBraidingComponent, mulHom, Int.negOnePow] using
    (tensorProductMul_apply_on_summands_raw (A := A) (B := B) p q p' q' x y)

/-- On the `(p, q)` summand of the tensor-product complex, the canonical differential is
`d_A ⊗ 1 + (-1)^p (1 ⊗ d_B)`. -/
theorem tensorProduct_d_on_summand_eq (p q : ℤ) :
    ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl ≫
        (A ⊗[R] B).d (p + q) =
      (A.d p ⊗ₘ 𝟙 (B.X q)) ≫
          ιTensorObj A.toCochainComplex B.toCochainComplex
            (p + 1) q (p + q + 1) (by abel_nf) +
        p.negOnePow •
          (((𝟙 (A.X p)) ⊗ₘ B.d q) ≫
            ιTensorObj A.toCochainComplex B.toCochainComplex
              p (q + 1) (p + q + 1) (by abel_nf)) := by
  have h :
      ιTensorObj A.toCochainComplex B.toCochainComplex p q (p + q) rfl ≫
          (tensorObj A.toCochainComplex B.toCochainComplex).d (p + q) (p + q + 1) =
        (A.d p ⊗ₘ 𝟙 (B.X q)) ≫
            ιTensorObj A.toCochainComplex B.toCochainComplex
              (p + 1) q (p + q + 1) (by abel_nf) +
          p.negOnePow •
            (((𝟙 (A.X p)) ⊗ₘ B.d q) ≫
              ιTensorObj A.toCochainComplex B.toCochainComplex
                p (q + 1) (p + q + 1) (by abel_nf)) :=
    tensorObj_d_on_summand_eq p q
  simpa [CochainDGAlgebra.d, tensorProduct] using h

end CochainDGAlgebra
