import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1

-- Declarations for this item will be appended below by the statement pipeline.

open Module MvPolynomial

universe u

noncomputable section

section

variable (k : Type u) [Field k]

local notation "Pxy" => MvPolynomial (Fin 2) k
local notation "x" => (X (0 : Fin 2) : Pxy)
local notation "y" => (X (1 : Fin 2) : Pxy)

/- Domain-style sampling:
- primary domain: subalgebras and ideals as module owners, together with module duality,
  reflexivity, and LinearRepresentations_Serre_1977's condition `(S_2)`;
- sampled owner declarations:
  `Subalgebra.moduleLeft`,
  `SMulMemClass.toModule`,
  `LinearMap.module`,
  `Module.IsReflexive`;
- best owner abstraction: the source-facing data are the explicit subalgebra `R` and ideal `𝔪`,
  while the ambient and dual module structures should come from the canonical owner layer rather
  than bespoke local instances;
- source/core/bridge triage:
  `source-facing`: the explicit ring `R = k[y, x^2, xy, x^3]`, the ideal
  `𝔪 = (y, x^2, xy, x^3)`, and the displayed identifications
  `Hom_R(k[x, y], R) = 𝔪` and `Hom_R(𝔪, R) = k[x, y]`;
  `core/canonical`: `Subalgebra.adjoin`, `Ideal.span`, `Subalgebra.moduleLeft`,
  `SMulMemClass.toModule`, `LinearMap.module`, `Module.IsReflexive`, and
  `Module.SerreConditionS`;
  `bridge/view`: the local notations `Pxy`, `x`, `y`, and `R`.

Primitive data are the explicit subalgebra and ideal. The module structures on `Pxy`, `𝔪`, and
their duals are derived API from the owner layer above, and reflexivity and the `(S_2)` statement
are further derived API on top of that source-facing data.
-/

/-- The ring `R = k[y, x^2, xy, x^3]`, modeled as a `k`-subalgebra of `k[x, y]`. -/
def reflexiveCounterexampleRing :
    Subalgebra k Pxy :=
  Algebra.adjoin k
    ({ y, x ^ 2, x * y, x ^ 3 } : Set Pxy)

local notation "R" => reflexiveCounterexampleRing k

private theorem reflexiveCounterexampleY_mem_ring :
    y ∈ R :=
  Algebra.subset_adjoin (by simp)

private theorem reflexiveCounterexampleXSq_mem_ring :
    x ^ 2 ∈ R :=
  Algebra.subset_adjoin (by simp)

private theorem reflexiveCounterexampleXY_mem_ring :
    x * y ∈ R :=
  Algebra.subset_adjoin (by simp)

private theorem reflexiveCounterexampleXCube_mem_ring :
    x ^ 3 ∈ R :=
  Algebra.subset_adjoin (by simp)

private noncomputable def reflexiveCounterexampleIdealGeneratorY :
    R := by
  refine ⟨y, reflexiveCounterexampleY_mem_ring k⟩

private noncomputable def reflexiveCounterexampleIdealGeneratorXSq :
    R := by
  refine ⟨x ^ 2, reflexiveCounterexampleXSq_mem_ring k⟩

private noncomputable def reflexiveCounterexampleIdealGeneratorXY :
    R := by
  refine ⟨x * y, reflexiveCounterexampleXY_mem_ring k⟩

private noncomputable def reflexiveCounterexampleIdealGeneratorXCube :
    R := by
  refine ⟨x ^ 3, reflexiveCounterexampleXCube_mem_ring k⟩

private def reflexiveCounterexampleIdealGeneratorSet : Set R :=
  { reflexiveCounterexampleIdealGeneratorY k,
    reflexiveCounterexampleIdealGeneratorXSq k,
    reflexiveCounterexampleIdealGeneratorXY k,
    reflexiveCounterexampleIdealGeneratorXCube k }

/-- The ideal `𝔪 = (y, x^2, xy, x^3)` inside `R = k[y, x^2, xy, x^3]`. -/
def reflexiveCounterexampleIdeal :
    Ideal R :=
  Ideal.span (reflexiveCounterexampleIdealGeneratorSet k)

local notation "𝔪" => reflexiveCounterexampleIdeal k

local instance : Module R R :=
  Semiring.toModule

local instance : Module R Pxy :=
  Subalgebra.moduleLeft R

local instance : Module R ↥𝔪 :=
  SMulMemClass.toModule 𝔪

local instance : Module R (Module.Dual R Pxy) :=
  LinearMap.module

local instance : Module R (Module.Dual R ↥𝔪) :=
  LinearMap.module

private noncomputable def reflexiveCounterexampleYInIdeal :
    𝔪 := by
  refine ⟨reflexiveCounterexampleIdealGeneratorY k, ?_⟩
  exact Ideal.subset_span (by
    simp [reflexiveCounterexampleIdealGeneratorSet])

private abbrev reflexiveCounterexampleDivideYExponent
    (d : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  d.update (1 : Fin 2) (d (1 : Fin 2) - 1)

private noncomputable def reflexiveCounterexampleDivideByY
    (p : Pxy) : Pxy :=
  ∑ d ∈ p.support.filter (fun d ↦ 0 < d (1 : Fin 2)),
    monomial (reflexiveCounterexampleDivideYExponent d) (p.coeff d)

-- Proof sketch: multiplication by an element of `𝔪` sends every polynomial to `R`, yielding the
-- displayed map `𝔪 → Hom_R(k[x, y], R)`.
private noncomputable def reflexiveCounterexampleIdealToAmbientDual :
    ↥𝔪 →ₗ[R] Module.Dual R Pxy :=
  { toFun := fun a ↦
      { toFun := fun p ↦
          ⟨((a : R) : Pxy) * p, by
            sorry⟩
        map_add' := by
          intro p q
          ext
          simp [mul_add]
        map_smul' := by
          intro r p
          sorry }
    map_add' := by
      intro a b
      sorry
    map_smul' := by
      intro r a
      sorry }

-- Proof sketch: the example identifies an `R`-linear functional on `k[x, y]` by its value at `1`,
-- and that value lies in `𝔪`.
private noncomputable def reflexiveCounterexampleAmbientDualToIdeal :
    Module.Dual R Pxy →ₗ[R] ↥𝔪 :=
  { toFun := fun φ ↦
      ⟨φ 1, by
        sorry⟩
    map_add' := by
      intro φ ψ
      sorry
    map_smul' := by
      intro r φ
      sorry }

-- Proof sketch: these two explicit maps are inverse `R`-linear identifications.
/-- The displayed `R`-linear identification `Hom_R(k[x, y], R) ≃ 𝔪`. -/
noncomputable def reflexiveCounterexampleAmbientDualEquivIdeal :
    Module.Dual R Pxy ≃ₗ[R] ↥𝔪 :=
  { toFun := reflexiveCounterexampleAmbientDualToIdeal k
    invFun := reflexiveCounterexampleIdealToAmbientDual k
    left_inv := by
      intro φ
      apply LinearMap.ext
      intro p
      sorry
    right_inv := by
      intro a
      apply Subtype.ext
      simp [reflexiveCounterexampleAmbientDualToIdeal,
        reflexiveCounterexampleIdealToAmbientDual]
    map_add' := by
      intro φ ψ
      sorry
    map_smul' := by
      intro r φ
      sorry }

-- Proof sketch: multiplication by an ambient polynomial gives an `R`-linear functional on `𝔪`,
-- and the inverse recovers the ambient polynomial by dividing the value on `y` by `y`.
private noncomputable def reflexiveCounterexampleAmbientToIdealDual :
    Pxy →ₗ[R] Module.Dual R ↥𝔪 :=
  { toFun := fun p ↦
      { toFun := fun a ↦
          ⟨((a : R) : Pxy) * p, by
            sorry⟩
        map_add' := by
          intro a b
          ext
          simp [add_mul]
        map_smul' := by
          intro r a
          sorry }
    map_add' := by
      intro p q
      sorry
    map_smul' := by
      intro r p
      sorry }

private noncomputable def reflexiveCounterexampleIdealDualToAmbient :
    Module.Dual R ↥𝔪 →ₗ[R] Pxy :=
  { toFun := fun φ ↦
      reflexiveCounterexampleDivideByY k
        (((φ (reflexiveCounterexampleYInIdeal k) : R) : Pxy))
    map_add' := by
      intro φ ψ
      sorry
    map_smul' := by
      intro r φ
      sorry }

-- Proof sketch: these are the displayed inverse identifications `Hom_R(𝔪, R) ≃ k[x, y]`.
/-- The displayed `R`-linear identification `Hom_R(𝔪, R) ≃ k[x, y]`. -/
noncomputable def reflexiveCounterexampleIdealDualEquivAmbient :
    Module.Dual R ↥𝔪 ≃ₗ[R] Pxy :=
  { toFun := reflexiveCounterexampleIdealDualToAmbient k
    invFun := reflexiveCounterexampleAmbientToIdealDual k
    left_inv := by
      intro φ
      apply LinearMap.ext
      intro a
      sorry
    right_inv := by
      intro p
      sorry
    map_add' := by
      intro φ ψ
      sorry
    map_smul' := by
      intro r φ
      sorry }

-- Proof sketch: the displayed identifications `Hom_R(k[x, y], R) = 𝔪` and `Hom_R(𝔪, R) = k[x, y]`
-- identify the ambient module with its double dual over `R`.
/-- The ambient polynomial ring `k[x, y]`, viewed as an `R`-module, is reflexive. -/
theorem reflexiveCounterexampleAmbient_isReflexive :
    Module.IsReflexive R Pxy := sorry

-- Proof sketch: the omitted depth computations in the text verify LinearRepresentations_Serre_1977's condition `(S_2)` for
-- `k[x, y]` when it is regarded as an `R`-module.
/-- The ambient polynomial ring satisfies LinearRepresentations_Serre_1977's condition `(S_2)` as an `R`-module. -/
theorem reflexiveCounterexampleAmbient_serreConditionS2 :
    Module.SerreConditionS R Pxy 2 := sorry

-- Proof sketch: this is the depth-theoretic failure exhibited in the text for the explicit
-- ring `R = k[y, x^2, xy, x^3]`.
/-- Example 15.23.17: if `R = k[y, x^2, xy, x^3] ⊂ k[x, y]`, then the ideal
`𝔪 = (y, x^2, xy, x^3)` and the displayed identifications
`Hom_R(k[x, y], R) = 𝔪` and `Hom_R(𝔪, R) = k[x, y]` are recorded by
`reflexiveCounterexampleAmbientDualEquivIdeal k` and
`reflexiveCounterexampleIdealDualEquivAmbient k`; in particular `k[x, y]` is reflexive and
`(S_2)` as an `R`-module, while `R` itself does not satisfy `(S_2)`. -/
theorem reflexiveCounterexampleRing_not_serreConditionS2 :
    ¬ R ⊧ (S₂) := sorry

end
