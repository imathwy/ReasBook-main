import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_132_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u

section

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

/- Domain sampling:
- primary domain: relative algebraic de Rham differentials under tensor-product base change;
- sampled owner declarations: `KaehlerDifferential.tensorKaehlerEquiv`,
  `exteriorPowerDeRhamMap`, `DeRhamFamily`, and `DescendsExteriorPowerDifferential`;
- source/core/bridge triage:
  * source-facing: the base-changed de Rham differential family on
    `(A' ⊗[A] B) ⊗[B] Ω[B⁄A]`;
  * core/canonical: the recursive owner `deRhamDifferentialFamily A' (A' ⊗[A] B)`;
  * bridge/view: transport of that owner across `KaehlerDifferential.tensorKaehlerEquiv`.
- primitive data: the degree-`1` comparison map `KaehlerDifferential.tensorKaehlerEquiv`;
- derived API: the induced degreewise maps on forms and the commuting-with-differentials theorem.
-/

local notation "B'" => A' ⊗[A] B
local notation "Ωbase" => B' ⊗[B] Ω[B⁄A]
local notation "e" => KaehlerDifferential.tensorKaehlerEquiv A A' B B'

local instance : Algebra B B' := Algebra.TensorProduct.rightAlgebra

local instance baseChangeExteriorPowerModule
    (M : Type u) [AddCommGroup M] [Module B' M] [Module A' M] [IsScalarTower A' B' M]
    (n : ℕ) : Module A' (⋀[B']^n M) :=
  Module.compHom _ (algebraMap A' B')

local instance baseChangeExteriorPowerIsScalarTower
    (M : Type u) [AddCommGroup M] [Module B' M] [Module A' M] [IsScalarTower A' B' M]
    (n : ℕ) : IsScalarTower A' B' (⋀[B']^n M) := by
  let _ : Module A' (⋀[B']^n M) := baseChangeExteriorPowerModule M n
  exact IsScalarTower.of_compHom A' B' (⋀[B']^n M)

private theorem exteriorPowerDeRhamMap_comp
    {M N P : Type u}
    [AddCommGroup M] [Module B' M] [Module A' M] [IsScalarTower A' B' M]
    [AddCommGroup N] [Module B' N] [Module A' N] [IsScalarTower A' B' N]
    [AddCommGroup P] [Module B' P] [Module A' P] [IsScalarTower A' B' P]
    (f : M →ₗ[B'] N) (g : N →ₗ[B'] P) (p : ℕ) :
    exteriorPowerDeRhamMap A' (g.comp f) p =
      (exteriorPowerDeRhamMap A' g p).comp (exteriorPowerDeRhamMap A' f p) := by
  cases p with
  | zero =>
      ext x
      rfl
  | succ p =>
      cases p with
      | zero =>
          ext x
          rfl
      | succ p =>
          rw [exteriorPowerDeRhamMap, exteriorPowerDeRhamMap, exteriorPowerDeRhamMap,
            exteriorPower.map_comp]
          rfl

private theorem exteriorPowerDeRhamMap_id
    {M : Type u} [AddCommGroup M] [Module B' M] [Module A' M] [IsScalarTower A' B' M]
    (p : ℕ) :
    exteriorPowerDeRhamMap A' (LinearMap.id : M →ₗ[B'] M) p = LinearMap.id := by
  cases p with
  | zero =>
      ext x
      rfl
  | succ p =>
      cases p with
      | zero =>
          ext x
          rfl
      | succ p =>
          rw [exteriorPowerDeRhamMap, exteriorPower.map_id]
          rfl

private theorem baseChange_map_comp_symm (p : ℕ) :
    (exteriorPowerDeRhamMap A' (e).toLinearMap p).comp
      (exteriorPowerDeRhamMap A' (e).symm.toLinearMap p) =
    LinearMap.id := by
  rw [← exteriorPowerDeRhamMap_comp]
  have h :
      (e).toLinearMap.comp (e).symm.toLinearMap =
        LinearMap.id := by
    ext x
    simp
  rw [h, exteriorPowerDeRhamMap_id]

/-- Transport a recursive differential family on `Ω^•[(A' ⊗[A] B)⁄A']` across the canonical
base-change equivalence on Kähler differentials. This is the bridge/view layer; the source-facing
canonical specialization is `baseChangeDeRhamDifferentialFamily`. -/
noncomputable def baseChangeTransportDifferentialFamily
    (δ : DeRhamFamily A' B' Ω[B'⁄A']) : DeRhamFamily A' B' Ωbase :=
  fun p ↦
    (exteriorPowerDeRhamMap A' (e).symm.toLinearMap (p + 1)).comp
      ((δ p).comp (exteriorPowerDeRhamMap A' (e).toLinearMap p))

/-- The bridge/view transport commutes with the canonical base-change comparison on forms. -/
theorem baseChangeTransportDifferentialFamily_descendsExteriorPowerDifferential
    (δ : DeRhamFamily A' B' Ω[B'⁄A']) :
    DescendsExteriorPowerDifferential (e).toLinearMap
      (baseChangeTransportDifferentialFamily δ) δ := by
  intro p
  simp only [baseChangeTransportDifferentialFamily]
  conv_rhs =>
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
  rw [baseChange_map_comp_symm]
  simp

/-- If a transported differential family squares to zero on `Ω^•[(A' ⊗[A] B)⁄A']`, then its
base-changed transport also squares to zero. -/
theorem baseChangeTransportDifferentialFamily_square_zero
    (δ : DeRhamFamily A' B' Ω[B'⁄A'])
    (hδ : ∀ p : ℕ, (δ (p + 1)).comp (δ p) = 0)
    (p : ℕ) :
    ((baseChangeTransportDifferentialFamily δ) (p + 1)).comp
      ((baseChangeTransportDifferentialFamily δ) p) = 0 := by
    ext x
    simp only [baseChangeTransportDifferentialFamily, LinearMap.comp_apply]
    have hmid :
        exteriorPowerDeRhamMap A' (e).toLinearMap (p + 1)
            ((exteriorPowerDeRhamMap A' (e).symm.toLinearMap (p + 1))
              ((δ p) ((exteriorPowerDeRhamMap A' (e).toLinearMap p) x))) =
          (δ p) ((exteriorPowerDeRhamMap A' (e).toLinearMap p) x) := by
      simpa using
        LinearMap.congr_fun
          (baseChange_map_comp_symm (p + 1))
          ((δ p) ((exteriorPowerDeRhamMap A' (e).toLinearMap p) x))
    rw [hmid]
    have hzero := LinearMap.congr_fun (hδ p)
      ((exteriorPowerDeRhamMap A' (e).toLinearMap p) x)
    have hzero' :
        (δ (p + 1)) ((δ p) ((exteriorPowerDeRhamMap A' (e).toLinearMap p) x)) = 0 := by
      simpa [LinearMap.comp_apply] using hzero
    rw [hzero']
    simp

variable (A A' B)

/-- The source-facing base-changed de Rham differential family on
`(A' ⊗[A] B) ⊗[B] Ω[B⁄A]`, obtained by transporting the canonical de Rham differential family on
`Ω^•[(A' ⊗[A] B)⁄A']` across the standard base-change equivalence. -/
noncomputable def baseChangeDeRhamDifferentialFamily : DeRhamFamily A' B' Ωbase :=
  baseChangeTransportDifferentialFamily (deRhamDifferentialFamily A' B')

variable {A A' B}

/-- The base-changed canonical de Rham differential family squares to zero, so it indeed forms the
source-facing base-changed de Rham complex. -/
theorem baseChangeDeRhamDifferentialFamily_square_zero (p : ℕ) :
    (baseChangeDeRhamDifferentialFamily A A' B (p + 1)).comp
      (baseChangeDeRhamDifferentialFamily A A' B p) = 0 := by
  simpa [baseChangeDeRhamDifferentialFamily] using
    baseChangeTransportDifferentialFamily_square_zero
      (deRhamDifferentialFamily A' B')
      (fun q ↦
        (isExteriorPowerDeRhamDifferential_deRhamDifferentialFamily A' B').square_zero q)
      p

/-- Lemma 10.132.1: the canonical base-change map on Kähler differentials identifies the canonical
de Rham differential family on the base-changed forms with the canonical de Rham differential
family on `Ω^•[(A' ⊗[A] B)⁄A']`. -/
theorem baseChangeDeRhamDifferentialFamily_descendsExteriorPowerDifferential :
    DescendsExteriorPowerDifferential (e).toLinearMap
      (baseChangeDeRhamDifferentialFamily A A' B)
      (deRhamDifferentialFamily A' B') := by
  simpa [baseChangeDeRhamDifferentialFamily] using
    baseChangeTransportDifferentialFamily_descendsExteriorPowerDifferential
      (deRhamDifferentialFamily A' B')

end
