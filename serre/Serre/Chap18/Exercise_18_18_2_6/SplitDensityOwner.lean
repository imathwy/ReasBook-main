import Serre.Chap18.Exercise_18_18_2_6.CommonKernelQuotient
import Serre.Chap18.Exercise_18_18_2_6.MatrixCornerActions
import Serre.Chap18.Exercise_18_18_2_6.ProductIdempotentDecomposition
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section

universe v w

namespace Representation

section EquivalenceCriterion

variable {k : Type} [Field k]
variable {G : Type v} [Monoid G]
variable {A : Type*} [Ring A] [Algebra k A] [Module.Finite k A] [IsSemisimpleRing A]
variable {V W : Type w}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Helper for Exercise 18-18.2-6: the exterior-trace invariant on `k[G]` already yields ordinary
trace equality on the lifted common image algebra. -/
lemma trace_eq_of_hexteriorTrace_one_on_lift
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hexteriorTrace : ∀ n (a : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a)) :
    ∀ a : MonoidAlgebra k G, LinearMap.trace k V (φV (liftι a)) =
      LinearMap.trace k W (φW (liftι a)) := by
  intro a
  -- The source proof uses only the `n = 1` exterior trace, which recovers the ordinary trace.
  have hchar : ρ.character = ρ'.character := by
    ext g
    have h1 := hexteriorTrace 1 (MonoidAlgebra.of k G g)
    simpa [Representation.character, Representation.nthExteriorPower,
      Representation.asAlgebraHom_of, trace_exteriorPower_map_one] using h1
  have htrace :=
    trace_eq_asAlgebraHom_of_character_eq (ρ := ρ) (ρ' := ρ') hchar a
  -- Re-express the descended action through the compatibility with the quotient lift.
  have hVa : φV (liftι a) = ρ.asAlgebraHom a := by
    simpa [AlgHom.comp_apply] using
      congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k V ↦ f a) hφV
  have hWa : φW (liftι a) = ρ'.asAlgebraHom a := by
    simpa [AlgHom.comp_apply] using
      congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k W ↦ f a) hφW
  simpa [hVa, hWa] using htrace

/-- Helper for Exercise 18-18.2-6: equality of the ambient `k`-dimensions of finite-dimensional
`D`-modules forces equality of their `D`-dimensions. -/
lemma finrank_over_divisionRing_eq_of_baseField_finrank_eq
    {D : Type*} [DivisionRing D] [Algebra k D] [Module.Finite k D]
    {X Y : Type*} [AddCommGroup X] [Module D X] [FiniteDimensional D X]
    [Module k X] [IsScalarTower k D X]
    [AddCommGroup Y] [Module D Y] [FiniteDimensional D Y]
    [Module k Y] [IsScalarTower k D Y]
    (h : Module.finrank k X = Module.finrank k Y) :
    Module.finrank D X = Module.finrank D Y := by
  have hX := Module.finrank_mul_finrank k D X
  have hY := Module.finrank_mul_finrank k D Y
  rw [h, ← hY] at hX
  -- Cancel the positive scalar-extension factor `finrank k D`.
  have hDpos : 0 < Module.finrank k D := by
    simpa using (Module.finrank_pos (R := k) (M := D))
  exact Nat.eq_of_mul_eq_mul_left hDpos hX

/-- Helper for Exercise 18-18.2-6: evaluating the ambient trace equality on the primitive
projector in the `i`-th Wedderburn factor identifies the corresponding Morita corner dimensions
after coercion to the base field `k`. -/
lemma corner_baseField_finrank_eq_of_wedderburn_primitive_projector
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (htrace : ∀ b : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i),
      LinearMap.trace k M (DistribSMul.toLinearMap k M b) =
        LinearMap.trace k N (DistribSMul.toLinearMap k N b))
    (i : Fin n) :
    let XiM :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let XiN :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (D i) XiM :=
      Module.compHom XiM
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : Module (D i) XiN :=
      Module.compHom XiN
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
        (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM)
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
        (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN)
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : IsScalarTower k (D i) XiM :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
    let _ : IsScalarTower k (D i) XiN :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
    (Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) : k) =
      Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
  let XiM :=
    pi_coordinate_submodule
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
  let XiN :=
    pi_coordinate_submodule
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
  let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
    pi_coordinate_submodule_factorModule
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
  let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
    pi_coordinate_submodule_factorModule
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
  let _ : Module (D i) XiM :=
    Module.compHom XiM
      (Matrix.scalarAlgHom (Fin (d i)) k :
        D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
  let _ : Module (D i) XiN :=
    Module.compHom XiN
      (Matrix.scalarAlgHom (Fin (d i)) k :
        D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
  let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
    MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
      (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM)
  let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
    MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
      (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN)
  let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
    pi_coordinate_submodule_factor_isScalarTower
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
  let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
    pi_coordinate_submodule_factor_isScalarTower
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
  let _ : IsScalarTower k (D i) XiM :=
    isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
  let _ : IsScalarTower k (D i) XiN :=
    isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
  let _ : FiniteDimensional k XiM := FiniteDimensional.of_injective
    ((pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i).subtype
      |>.restrictScalars k)
    Subtype.val_injective
  let _ : FiniteDimensional k XiN := FiniteDimensional.of_injective
    ((pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i).subtype
      |>.restrictScalars k)
    Subtype.val_injective
  let b : Π j, Matrix (Fin (d j)) (Fin (d j)) (D j) :=
    Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))
  have hM :
      LinearMap.trace k M (DistribSMul.toLinearMap k M b) =
        Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) := by
    -- First isolate the `i`-th product factor, then read the primitive corner trace as the
    -- dimension of the corresponding Morita coefficient module.
    calc
      LinearMap.trace k M (DistribSMul.toLinearMap k M b) =
          LinearMap.trace k XiM
            (DistribSMul.toLinearMap k XiM
              (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))) := by
            simpa [XiM, b] using
              trace_pi_single_action_eq_trace_coordinate_action
                (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
                (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))
      _ = Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) := by
            simpa [XiM] using
              trace_matrix_corner_action_eq_finrank_toModuleCatObj
                (k := k) (D := D i) (m := d i) (M := XiM) (j := (0 : Fin (d i)))
  have hN :
      LinearMap.trace k N (DistribSMul.toLinearMap k N b) =
        Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
    -- The same primitive projector computation holds on the second module.
    calc
      LinearMap.trace k N (DistribSMul.toLinearMap k N b) =
          LinearMap.trace k XiN
            (DistribSMul.toLinearMap k XiN
              (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))) := by
            simpa [XiN, b] using
              trace_pi_single_action_eq_trace_coordinate_action
                (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
                (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))
      _ = Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
            simpa [XiN] using
              trace_matrix_corner_action_eq_finrank_toModuleCatObj
                (k := k) (D := D i) (m := d i) (M := XiN) (j := (0 : Fin (d i)))
  -- Specializing the ambient trace equality at the primitive projector gives the corner
  -- multiplicity equality over the base field.
  simpa [XiM, XiN] using hM.symm.trans ((htrace b).trans hN)

/-- Helper for Exercise 18-18.2-6: once a chosen lift exists for every point of the semisimple
image algebra, the `n = 1` exterior-trace specialization descends to ordinary trace equality on
that target algebra. -/
lemma trace_eq_on_target_of_surjective_lift
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hexteriorTrace : ∀ n (a : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a)) :
    ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) := by
  -- Choose a lift and apply the already-proved `n = 1` specialization on `k[G]`.
  intro a
  rcases hlift a with ⟨t, rfl⟩
  exact
    trace_eq_of_hexteriorTrace_one_on_lift
      (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW hexteriorTrace t

/-- Helper for Exercise 18-18.2-6: once the common image algebra `A` is split by a Wedderburn
equivalence `eA : A ≃ₐ[k] B`, the already-descended ordinary trace identity transports directly to
the product algebra `B`. -/
lemma trace_eq_on_split_product_of_trace_eq
    {B : Type*} [Ring B] [Algebra k B]
    {X Y : Type*}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    [Module A X] [Module A Y]
    [IsScalarTower k A X] [IsScalarTower k A Y]
    (eA : A ≃ₐ[k] B)
    (htraceA : ∀ a : A,
      LinearMap.trace k X (DistribSMul.toLinearMap k X a) =
        LinearMap.trace k Y (DistribSMul.toLinearMap k Y a)) :
    let _ : Module B X := Module.compHom X eA.symm.toRingHom
    let _ : Module B Y := Module.compHom Y eA.symm.toRingHom
    let _ : IsScalarTower k B X :=
      IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := X) fun r x ↦ by
        change (eA.symm ((algebraMap k B) r)) • x = r • x
        rw [eA.symm.commutes]
        exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
    let _ : IsScalarTower k B Y :=
      IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := Y) fun r y ↦ by
        change (eA.symm ((algebraMap k B) r)) • y = r • y
        rw [eA.symm.commutes]
        exact IsScalarTower.algebraMap_smul (R := k) (A := A) r y
    ∀ b : B,
      LinearMap.trace k X (DistribSMul.toLinearMap k X b) =
        LinearMap.trace k Y (DistribSMul.toLinearMap k Y b) := by
  -- The transported `B`-action is defined through `eA.symm`, so the trace identity on `A`
  -- immediately rewrites to the corresponding one on the split product.
  simpa using fun b : B ↦ htraceA (eA.symm b)

/-- Helper for Exercise 18-18.2-6: once the Morita corner modules in each Wedderburn factor have
the same division-ring dimension, the ambient modules over the product of matrix algebras are
already linearly equivalent. -/
theorem nonempty_linearEquiv_of_corner_finrank_eq_on_pi_matrix_divisionRing
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (hcorner : ∀ i : Fin n,
      let XiM :=
        pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let XiN :=
        pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        pi_coordinate_submodule_factorModule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        pi_coordinate_submodule_factorModule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : Module (D i) XiM :=
        Module.compHom XiM
          (Matrix.scalarAlgHom (Fin (d i)) k :
            D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
      let _ : Module (D i) XiN :=
        Module.compHom XiN
          (Matrix.scalarAlgHom (Fin (d i)) k :
            D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
      let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
          (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM)
      let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
          (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN)
      let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        pi_coordinate_submodule_factor_isScalarTower
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        pi_coordinate_submodule_factor_isScalarTower
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) =
        Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i)))) :
    Nonempty (M ≃ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)] N) := by
  let eM :=
    pi_idempotent_linearEquiv
      (k := k) (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) (D i)) (M := M)
  let eN :=
    pi_idempotent_linearEquiv
      (k := k) (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) (D i)) (M := N)
  let ecoord :
      ∀ i : Fin n,
        pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i ≃ₗ[Π j,
              Matrix (Fin (d j)) (Fin (d j)) (D j)]
            pi_coordinate_submodule
              (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i := by
    intro i
    let XiM :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let XiN :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (D i) XiM :=
      Module.compHom XiM
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : Module (D i) XiN :=
      Module.compHom XiN
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM
    let NN : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i)) MM
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i)) NN
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : FiniteDimensional k XiM := FiniteDimensional.of_injective
      ((pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i).subtype
        |>.restrictScalars k)
      Subtype.val_injective
    let _ : FiniteDimensional k XiN := FiniteDimensional.of_injective
      ((pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i).subtype
        |>.restrictScalars k)
      Subtype.val_injective
    let _ : FiniteDimensional (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) :=
      finiteDimensional_toModuleCatObj_of_matrix_module
        (k := k) (D := D i) (m := d i) (M := XiM) (j := 0)
    let _ : FiniteDimensional (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) :=
      finiteDimensional_toModuleCatObj_of_matrix_module
        (k := k) (D := D i) (m := d i) (M := XiN) (j := 0)
    let _ : Module.Free (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) :=
      Module.Free.of_divisionRing
        (K := D i) (V := MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i)))
    let _ : Module.Free (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) :=
      Module.Free.of_divisionRing
        (K := D i) (V := MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i)))
    let ecorner :
        MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i)) ≃ₗ[D i]
          MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i)) :=
      LinearEquiv.ofFinrankEq
        (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i)))
        (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i)))
        (by simpa [XiM, XiN] using hcorner i)
    let eXi :
        XiM ≃ₗ[Matrix (Fin (d i)) (Fin (d i)) (D i)] XiN :=
      (toModuleCatFromModuleCatLinearEquiv (R := D i) (M := MM) 0).trans
        ((matrix_module_linearEquiv_of_linearEquiv (n := Fin (d i)) ecorner).trans
          (toModuleCatFromModuleCatLinearEquiv (R := D i) (M := NN) 0).symm)
    -- Each product coordinate becomes product-linear because the ambient action factors through
    -- that single coordinate.
    simpa [XiM, XiN] using
      (coordinate_linearEquiv_is_product_linear
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) (N := N) i eXi)
  -- Decompose both modules into coordinate summands, apply the factorwise matrix equivalences,
  -- and reassemble.
  exact
    ⟨eM.trans ((LinearEquiv.piCongrRight ecoord).trans eN.symm)⟩

/-- Helper for Exercise 18-18.2-6: once the exterior-trace data is available on lifts from the
common finite-dimensional semisimple image algebra, the remaining source-faithful step is to
split `A`, isolate primitive matrix projectors, and recover the simple multiplicities factorwise. -/
theorem nonempty_linearEquiv_of_exterior_trace_eq_on_finite_semisimple_image
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (hexteriorTrace : ∀ n (a : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a)) :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    Nonempty (V ≃ₗ[A] W) := by
  let _ := hV
  let _ := hW
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
      change (φV (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
  let _ : IsScalarTower k A W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r x ↦ by
      change (φW (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k W ↦ f x) (φW.commutes r)
  have htraceA :
      ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) :=
    trace_eq_on_target_of_surjective_lift
      (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW hlift hexteriorTrace
  -- Route correction: the old theorem tried to work with determinant or trace identities on all
  -- `a : A`. Serre's proof only evaluates the descended invariant on lifts of primitive
  -- projectors in a Wedderburn decomposition of `A`.
  have hlift_primitive : ∀ a : A, ∃ t : MonoidAlgebra k G, liftι t = a := hlift
  classical
  obtain ⟨n, D, d, _, _, _, hd, ⟨eA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite (R₀ := k) (R := A)
  let B := Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) (D i)
  let _ : Module B V := Module.compHom V eA.symm.toRingHom
  let _ : Module B W := Module.compHom W eA.symm.toRingHom
  let _ : IsScalarTower k B V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := V) fun r x ↦ by
      change (eA.symm ((algebraMap k B) r)) • x = r • x
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
  let _ : IsScalarTower k B W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := W) fun r x ↦ by
      change (eA.symm ((algebraMap k B) r)) • x = r • x
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
  have hcorner :
      ∀ i : Fin n,
        let XiV :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
        let XiW :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
        let _ : Module (D i) XiV :=
          Module.compHom XiV
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : Module (D i) XiW :=
          Module.compHom XiW
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
            (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV)
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
            (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW)
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
        Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiV (0 : Fin (d i))) =
          Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiW (0 : Fin (d i))) := by
    intro i
    let XiV :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
    let XiW :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
    let _ : Module (D i) XiV :=
      Module.compHom XiV
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : Module (D i) XiW :=
      Module.compHom XiW
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
        (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV)
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
        (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW)
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
    let _ : IsScalarTower k (D i) XiV :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiV)
    let _ : IsScalarTower k (D i) XiW :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiW)
    have htraceB :
        ∀ b : B,
          LinearMap.trace k V (DistribSMul.toLinearMap k V b) =
            LinearMap.trace k W (DistribSMul.toLinearMap k W b) := by
      -- Transport the trace identity from `A` to the split Wedderburn product before probing the
      -- primitive projector.
      simpa [B] using
        trace_eq_on_split_product_of_trace_eq
          (k := k) (A := A) (B := B) (X := V) (Y := W) eA htraceA
    have hcorner_cast :
        ((Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiV (0 : Fin (d i))) : ℕ) : k) =
          Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiW (0 : Fin (d i))) := by
      -- The primitive projector already gives equality of the corner dimensions after coercion
      -- to `k`.
      simpa using
        corner_baseField_finrank_eq_of_wedderburn_primitive_projector
          (k := k) (D := D) (d := d) (M := V) (N := W) htraceB i
    -- TODO: Serre's source route needs a valid bridge from the descended primitive projector in
    -- `A` to equality of reverse characteristic polynomials on its chosen lifts. The tempting
    -- rewrite `((ρ.nthExteriorPower n).asAlgebraHom t) = exteriorPower.map n (ρ.asAlgebraHom t)`
    -- is false because exterior power is not additive on `k[G]`, so ordinary trace equality on
    -- `A` still leaves only the weaker cast equality `hcorner_cast`.
    sorry
  have hBlinear : Nonempty (V ≃ₗ[B] W) := by
    simpa [B] using
      nonempty_linearEquiv_of_corner_finrank_eq_on_pi_matrix_divisionRing
        (k := k) (D := D) (d := d) (M := V) (N := W) hcorner
  rcases hBlinear with ⟨eB⟩
  let eAlinear : V ≃ₗ[A] W :=
    { toFun := eB
      invFun := eB.symm
      left_inv := eB.left_inv
      right_inv := eB.right_inv
      map_add' := eB.map_add
      map_smul' := by
        intro a x
        have hVsmul : (eA a : B) • x = a • x := by
          change (eA.symm (eA a)) • x = a • x
          simp
        have hWsmul : (eA a : B) • eB x = a • eB x := by
          change (eA.symm (eA a)) • eB x = a • eB x
          simp
        calc
          eB (a • x) = eB ((eA a : B) • x) := by rw [hVsmul]
          _ = (eA a : B) • eB x := eB.map_smul (eA a) x
          _ = a • eB x := hWsmul }
  exact ⟨eAlinear⟩

end EquivalenceCriterion

end Representation
