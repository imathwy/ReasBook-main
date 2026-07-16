import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_168_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

/-
Domain sampling:
* Primary domain: finite-type and finite descent for algebra-map base change along directed ring
  colimits.
* Relevant owner declarations inspected:
  - `Algebra.TensorProduct.map`
  - `Ring.DirectLimit.of`
  - `finite_type_surjectivity_descends` from `Lemma_10_127_7`
  - `DirectedFiniteTypeHomApproximation.stageBaseChangeMap` from `Lemma_10_127_14`
* Best owner abstraction:
  - `source-facing`: the finite and finite-type descent statements below
  - `core/canonical`: base change along a stage map or the direct-limit map, expressed by
    `Algebra.TensorProduct.map`
  - `bridge/view`: the chosen directed-system presentation of the colimit
* Primitive vs. derived:
  - primitive data: the directed system, the distinguished stage `i0`, and the algebra map `φ₀`
  - derived API: the stagewise and direct-limit tensor-product base-change maps
-/

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (G : ι → Type v) [∀ i, CommRing (G i)]
variable (f : ∀ i j, i ≤ j → G i →+* G j)
variable [DirectedSystem G fun i j hij ↦ f i j hij]
variable (i0 : ι)
variable {B₀ : Type w} [CommRing B₀] [Algebra (G i0) B₀]
variable {C₀ : Type w} [CommRing C₀] [Algebra (G i0) C₀]
variable (φ₀ : B₀ →ₐ[G i0] C₀)

local notation "G∞" => Ring.DirectLimit G (fun i j hij ↦ f i j hij)

/-- The stagewise base-changed map is of finite type whenever `φ₀` is of finite type. -/
-- Proof sketch: Finite type is stable under base change, applied to the base change of `φ₀`
-- along `G i0 → G i`.
theorem stage_base_change_hom_finiteType (hφ₀ : φ₀.FiniteType) {i : ι} (hi : i0 ≤ i) :
    letI : Algebra (G i0) (G i) := (f i0 i hi).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G i))).FiniteType := sorry

/-- The colimit base-changed map is of finite type whenever `φ₀` is of finite type. -/
-- Proof sketch: Finite type is stable under base change, applied to the canonical map
-- `G i0 → Ring.DirectLimit G f`.
theorem direct_limit_base_change_hom_finiteType (hφ₀ : φ₀.FiniteType) :
    letI : Algebra (G i0) G∞ := (Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) G∞)).FiniteType := sorry

/-- Lemma 10.168.3: if the base change of `φ₀` to the directed colimit ring is finite and `φ₀`
is of finite type, then after passing to some stage `i ≥ i0` the corresponding base-changed map
is already finite. -/
-- Proof sketch: Choose finitely many generators of `C₀` over `B₀`. The finiteness of the colimit
-- base change gives monic relations for their images over the direct limit. Descend the finitely
-- many coefficients and relations to some stage using directedness, then conclude that the stage
-- base change is finite.
theorem exists_ge_finite_stage_base_change_hom_of_direct_limit_finite
    (hfinite :
      letI : Algebra (G i0) G∞ := (Ring.DirectLimit.of G (fun i j hij ↦ f i j hij) i0).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) G∞)).Finite)
    (hφ₀ : φ₀.FiniteType) :
    ∃ (i : ι) (hi : i0 ≤ i),
      letI : Algebra (G i0) (G i) := (f i0 i hi).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (G i0) (G i))).Finite := sorry

end
