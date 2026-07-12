import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open PrimeSpectrum Set Topology

section

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [IsDomain B]
variable [Algebra A B]
variable [IsDomain A]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]
variable [Algebra.IsAlgebraic (FractionRing A) (FractionRing B)]

local notation "f" => algebraMap A B

-- Proof sketch: `Frac(B)` is algebraic over `Frac(A)`, hence also algebraic over `A` by
-- `IsFractionRing.comap_isAlgebraic_iff`. Since `B` injects into `Frac(B)`, the `A`-algebra `B`
-- is algebraic as well.
omit [IsDomain B] in
private theorem isAlgebraic_of_fractionRing_isAlgebraic :
    Algebra.IsAlgebraic A B := by
  let _ : Algebra.IsAlgebraic A (FractionRing B) :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic (FractionRing A) (FractionRing B))
  exact
    Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom A B (FractionRing B))
      (IsFractionRing.injective B (FractionRing B))

-- Proof sketch: the closure of the image of `V(J)` under `Spec B → Spec A` is
-- `V(J.comap (algebraMap A B))` by `closure_image_comap_zeroLocus`. The first theorem supplies the
-- contradiction once density forces `J.comap f = ⊥`.
/-
Domain-style triage for Lemma 10.30.8:
* source-facing layer: nonzero ideals of `B` contract nontrivially to `A`, and the corresponding
  closed subsets of `Spec B` have nondense image in `Spec A`.
* sampled canonical owners in this domain:
  `algebraMap_injective_of_field_isFractionRing`,
  `IsFractionRing.comap_isAlgebraic_iff`,
  `Ideal.comap_ne_bot_of_algebraic_mem`,
  `PrimeSpectrum.closure_image_comap_zeroLocus`.
* core owner abstraction: the induced public fraction-field tower
  `[Algebra K L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]`.
* primitive data: the domain map `A → B`, the induced fraction fields `K = Frac(A)` and
  `L = Frac(B)`, and the nonzero ideal `J`.
* bridge/view: the internal bridge `isAlgebraic_of_fractionRing_isAlgebraic`, upgrading the
  algebraic fraction-field extension to algebraicity of `A → B`.
* derived API: injectivity of `A → B` from
  `algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)`, then the
  ideal/topological consequences from `Ideal.comap_ne_bot_of_algebraic_mem` and
  `PrimeSpectrum.closure_image_comap_zeroLocus`.
-/

/-- Lemma 10.30.8: if the induced fraction-field extension `Frac(B) / Frac(A)` is algebraic, then
every nonzero ideal of `B` has nonzero contraction to `A`. Under the tower hypotheses below,
injectivity of `A → B` is automatic from
`algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)`. -/
@[stacks 0H7L]
theorem ideal_comap_ne_bot_of_ne_bot (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap f ≠ ⊥ := by
  let _ : Algebra.IsAlgebraic A B := isAlgebraic_of_fractionRing_isAlgebraic
  obtain ⟨x, hxJ, hx0⟩ := (Submodule.ne_bot_iff _).mp hJ
  exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hxJ (Algebra.IsAlgebraic.isAlgebraic x)

/-- If the induced fraction-field extension `Frac(B) / Frac(A)` is algebraic, then the image of
the proper closed subset `V(J)` is not dense in `Spec A`. Under the tower hypotheses below,
injectivity of `A → B` is automatic from
`algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)`. -/
theorem not_dense_image_zeroLocus_of_ne_bot (J : Ideal B) (hJ : J ≠ ⊥) :
    ¬ Dense (comap f '' zeroLocus J) := by
  intro hDense
  have hclosure :
      closure (comap f '' zeroLocus J) = zeroLocus (J.comap f : Set A) := by
    exact closure_image_comap_zeroLocus f J
  have hzero : zeroLocus (J.comap f : Set A) = univ := by
    rw [← hclosure, dense_iff_closure_eq.mp hDense]
  have hle : J.comap f ≤ nilradical A :=
    zeroLocus_eq_univ_iff _ |>.mp hzero
  have hnil : nilradical A = ⊥ := by
    rw [nilradical_eq_bot_iff]
    infer_instance
  have hbot : J.comap f = ⊥ := by
    apply eq_bot_iff.mpr
    rw [← hnil]
    exact hle
  exact ideal_comap_ne_bot_of_ne_bot J hJ hbot

end
