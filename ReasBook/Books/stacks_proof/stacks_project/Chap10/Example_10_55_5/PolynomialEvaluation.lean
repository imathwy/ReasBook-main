import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap10.EqualEndpointRing
import StacksProject_2024.Chap10.Lemma_10_39_12
import StacksProject_2024.Chap10.Example_10_55_3
import StacksProject_2024.Chap10.Lemma_10_7_2
import Mathlib.Tactic.StacksAttribute

noncomputable section

open scoped TensorProduct

universe u

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Example 10.55.5: a constant polynomial belongs to the equal-endpoint subring. -/
theorem equal_endpoint_constant_mem (a : k) : Polynomial.C a ∈ R := by
  -- Constant polynomials take the same value at both endpoints.
  rw [mem_equal_endpoint_poly_subring_iff]
  simp

/-- Helper for Example 10.55.5: the constant polynomial `C a`, viewed in the equal-endpoint
subring. -/
noncomputable def equal_endpoint_constant (a : k) : R :=
  ⟨Polynomial.C a, equal_endpoint_constant_mem (k := k) a⟩

/-- Helper for Example 10.55.5: subtracting the endpoint difference times `X` puts a polynomial
into the equal-endpoint subring. -/
theorem equal_endpoint_subtract_difference_mul_X_mem (f : Polynomial k) :
    f - Polynomial.C (f.eval 1 - f.eval 0) * Polynomial.X ∈ R := by
  -- The correction term changes the value at `1` by exactly `f(1) - f(0)` and vanishes at `0`.
  rw [mem_equal_endpoint_poly_subring_iff]
  calc
    (f - Polynomial.C (f.eval 1 - f.eval 0) * Polynomial.X).eval 0 = f.eval 0 := by
      simp
    _ = f.eval 1 - (f.eval 1 - f.eval 0) := by ring
    _ = (f - Polynomial.C (f.eval 1 - f.eval 0) * Polynomial.X).eval 1 := by
      simp

/-- Helper for Example 10.55.5: every polynomial splits as an equal-endpoint polynomial plus a
scalar multiple of `X`. -/
theorem equal_endpoint_polynomial_decomposition (f : Polynomial k) :
    ∃ r : R, f = r.1 + Polynomial.C (f.eval 1 - f.eval 0) * Polynomial.X := by
  let r : R :=
    ⟨f - Polynomial.C (f.eval 1 - f.eval 0) * Polynomial.X,
      equal_endpoint_subtract_difference_mul_X_mem (k := k) f⟩
  refine ⟨r, ?_⟩
  -- Re-expanding the chosen equal-endpoint summand recovers the original polynomial.
  dsimp [r]
  ring

/-- Helper for Example 10.55.5: under the `DistribMulAction` scalar path from
`Submodule.smul_mem`, multiplying the generator `1` by `r` recovers the underlying polynomial. -/
theorem equal_endpoint_distrib_smul_one_eq (r : R) :
    letI : SMul R (Polynomial k) := DistribMulAction.toDistribSMul.toSMul
    (r • (1 : Polynomial k) : Polynomial k) = r.1 := by
  -- The exact restricted scalar action still reduces to multiplication in the ambient polynomial
  -- ring, and multiplying by `1` does nothing.
  rw [Subring.smul_def]
  simp [smul_eq_mul]

/-- Helper for Example 10.55.5: under the `DistribMulAction` scalar path from
`Submodule.smul_mem`, the constant witness acts on `X` by ordinary multiplication. -/
theorem equal_endpoint_distrib_smul_X_eq (a : k) :
    letI : SMul R (Polynomial k) := DistribMulAction.toDistribSMul.toSMul
    (equal_endpoint_constant (k := k) a • Polynomial.X : Polynomial k) =
      Polynomial.C a * Polynomial.X := by
  -- Rewriting through the subring action identifies the witness scalar with `C a`.
  rw [Subring.smul_def]
  simp [smul_eq_mul, equal_endpoint_constant]

/-- Helper for Example 10.55.5: under the `DistribMulAction` scalar path used by the generator
map, scalar multiplication on `k[X]` is ordinary multiplication by the corresponding polynomial. -/
theorem equal_endpoint_distrib_smul_eq_mul (r : R) (f : Polynomial k) :
    letI : SMul R (Polynomial k) := DistribMulAction.toDistribSMul.toSMul
    (r • f : Polynomial k) = (r : Polynomial k) * f := by
  -- This is the canonical `DistribMulAction` coming from the ambient polynomial ring.
  rfl

/-- Helper for Example 10.55.5: the `R`-action on `k[X]` is multiplication by the underlying
polynomial. -/
theorem equal_endpoint_polynomial_smul (r : R) (f : Polynomial k) :
    (r • f : Polynomial k) = r.1 * f := by
  -- Restriction of scalars along the subring inclusion acts by ordinary polynomial multiplication.
  rfl

/-- Helper for Example 10.55.5: the algebra map from the equal-endpoint subring to `k[X]` is the
underlying polynomial coercion. -/
theorem equal_endpoint_polynomial_algebraMap_eq_coe (r : R) :
    algebraMap R (Polynomial k) r = (r : Polynomial k) := by
  rfl

/-- Helper for Example 10.55.5: the source decomposition is packaged as a single `R`-linear map
from two copies of `R` onto `k[X]`. -/
noncomputable def equal_endpoint_polynomial_generator_map :
    (R × R) →ₗ[R] Polynomial k :=
  LinearMap.coprod
    (LinearMap.toSpanSingleton R (Polynomial k) (1 : Polynomial k))
    (LinearMap.toSpanSingleton R (Polynomial k) Polynomial.X)

/-- Helper for Example 10.55.5: the source-faithful generator map sends `(r, s)` to `r + sX`. -/
theorem equal_endpoint_polynomial_generator_map_apply (x : R × R) :
    equal_endpoint_polynomial_generator_map (k := k) x =
      (x.1 : Polynomial k) + (x.2 : Polynomial k) * Polynomial.X := by
  -- Expand the coprod map and normalize each coordinate to ambient polynomial multiplication.
  simp [equal_endpoint_polynomial_generator_map, equal_endpoint_polynomial_smul]

/-- Helper for Example 10.55.5: the generator map is surjective by the textbook decomposition
`f = r + C(f(1)-f(0)) X`. -/
theorem equal_endpoint_polynomial_generator_map_surjective :
    Function.Surjective (equal_endpoint_polynomial_generator_map (k := k)) := by
  intro f
  rcases equal_endpoint_polynomial_decomposition (k := k) f with ⟨r, hr⟩
  refine ⟨(r, equal_endpoint_constant (k := k) (f.eval 1 - f.eval 0)), ?_⟩
  -- Evaluate the generator map on the textbook witness from the polynomial decomposition.
  rw [equal_endpoint_polynomial_generator_map_apply]
  simpa [equal_endpoint_constant] using hr.symm

/-- Helper for Example 10.55.5: `k[X]` is generated over `R` by `1` and `X`. -/
theorem equal_endpoint_polynomial_finite : Module.Finite R (Polynomial k) := by
  -- The source decomposition makes `k[X]` a quotient of the finite module `R × R`.
  let _ : Module.Finite R (R × R) := inferInstance
  exact Module.Finite.of_surjective
    (equal_endpoint_polynomial_generator_map (k := k))
    (equal_endpoint_polynomial_generator_map_surjective (k := k))

/-- Helper for Example 10.55.5: register the normalization `k[X]` as a finite `R`-module. -/
noncomputable instance equal_endpoint_polynomial_module_finite :
    Module.Finite R (Polynomial k) :=
  equal_endpoint_polynomial_finite (k := k)

/-- Helper for Example 10.55.5: evaluation at the common endpoint defines a ring map `R → k`. -/
noncomputable def equal_endpoint_eval : R →+* k :=
  (Polynomial.eval₂RingHom (RingHom.id k) (0 : k)).comp (equal_endpoint_poly_subring k).subtype

/-- Helper for Example 10.55.5: the endpoint-evaluation map equips `k` with its natural
`R`-algebra structure. -/
noncomputable instance equal_endpoint_eval_algebra : Algebra R k :=
  (equal_endpoint_eval k).toAlgebra

/-- Helper for Example 10.55.5: the `R`-action on the endpoint field is multiplication by the
endpoint value. -/
theorem equal_endpoint_eval_smul (r : R) (a : k) :
    (r • a : k) = equal_endpoint_eval k r * a := by
  -- The endpoint field module structure comes from the algebra map `R → k`.
  rfl

/-- Helper for Example 10.55.5: the endpoint field is a cyclic `R`-module via evaluation. -/
theorem equal_endpoint_eval_finite : Module.Finite R k := by
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨{(1 : k)}, Set.finite_singleton _, ?_⟩
  rw [Submodule.span_singleton_eq_top_iff]
  intro a
  refine ⟨equal_endpoint_constant (k := k) a, ?_⟩
  -- The constant polynomial `C a` acts on the generator `1` by the scalar `a`.
  rw [equal_endpoint_eval_smul]
  simp [equal_endpoint_eval, equal_endpoint_constant]

/-- Helper for Example 10.55.5: register the endpoint field as a finite `R`-module. -/
noncomputable instance equal_endpoint_eval_module_finite : Module.Finite R k :=
  equal_endpoint_eval_finite (k := k)

/-- Helper for Example 10.55.5: evaluation at `0` makes `k` into a `k[X]`-algebra. -/
noncomputable def polynomial_eval_zero : Polynomial k →+* k :=
  Polynomial.eval₂RingHom (RingHom.id k) (0 : k)

/-- Helper for Example 10.55.5: the evaluation-at-`0` ring map supplies the ambient
`k[X]`-module structure on `k`. -/
noncomputable instance polynomial_eval_zero_algebra : Algebra (Polynomial k) k :=
  (polynomial_eval_zero (k := k)).toAlgebra

/-- Helper for Example 10.55.5: the evaluation-at-`0` module `k` over `k[X]` is cyclic. -/
theorem polynomial_eval_zero_finite : Module.Finite (Polynomial k) k := by
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨{(1 : k)}, Set.finite_singleton _, ?_⟩
  rw [Submodule.span_singleton_eq_top_iff]
  intro a
  refine ⟨Polynomial.C a, ?_⟩
  -- The constant polynomial `C a` sends the generator `1` to the scalar `a`.
  change polynomial_eval_zero (k := k) (Polynomial.C a) * 1 = a
  simp [polynomial_eval_zero]

/-- Helper for Example 10.55.5: register `k` as a finite `k[X]`-module via evaluation at `0`. -/
noncomputable instance polynomial_eval_zero_module_finite :
    Module.Finite (Polynomial k) k :=
  polynomial_eval_zero_finite (k := k)

end
