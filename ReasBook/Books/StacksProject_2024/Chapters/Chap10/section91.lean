import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_10_91_1 (from Chap10) -/
universe u v

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]

/- Domain-style sampling:
- primary domain: the owner predicates `Module.MittagLeffler`, `Module.Projective`, and
  `Module.FinitePresentation` for modules over a commutative ring;
- sampled declarations of the same kind:
  `Module.MittagLeffler` and `Module.instMittagLefflerOfFinitePresentation` from
  `Definition_10_88_7`,
  `Module.mittagLeffler_iff_tensorProduct_piRight_injective` from `Proposition_10_89_5`,
  the direct-sum owner API in `Lemma_10_89_10`,
  and mathlib's instance `Module.Projective.of_free`;
- best owner abstraction: `Module.MittagLeffler R M`;
- primitive data: the module `M` and owner hypotheses such as finite presentation, projectivity,
  or freeness;
- derived API: the finite-generation criterion below, the projective-to-Mittag-Leffler bridge, and
  the free case as a direct inferred consequence of `Module.Projective.of_free`;
- layer: clause (2) is a `bridge/view` from the projective owner to the Mittag-Leffler owner,
  while clause (3) is a recall/consequence item through the canonical owner instances.
-/

/- Example 10.91.1 (1): a finitely presented module is Mittag-Leffler. This is already the
canonical owner instance `Module.instMittagLefflerOfFinitePresentation` from
`Definition_10_88_7`, so this clause is a direct recall rather than a parallel local wrapper. -/
recall Module.instMittagLefflerOfFinitePresentation

-- Proof sketch: apply Proposition `10.89.2` to identify finite generation with surjectivity of the
-- canonical tensor-product-to-product maps, Proposition `10.89.3` to identify finite presentation
-- with bijectivity of the same maps, and Proposition `10.89.5` to rewrite the injectivity part as
-- the Mittag-Leffler condition.
/-- Example 10.91.1: for a finitely generated `R`-module `M`, being Mittag-Leffler is equivalent
to being finitely presented. -/
theorem mittagLeffler_iff_finitePresentation_of_finite [Module.Finite R M] :
    MittagLeffler R M ↔ Module.FinitePresentation R M := by
  have hsurj_iff :
      Module.Finite R M ↔
        ∀ (A : Type (max u v)) (Q : Type u) [AddCommMonoid Q] [Module R Q],
          Function.Surjective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)) :=
    show
      Module.Finite R M ↔
        ∀ (A : Type (max u v)) (Q : Type u) [AddCommMonoid Q] [Module R Q],
          Function.Surjective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q))
    from module_finite_tfae_tensorProduct_pi_surjective.out 0 2
  have hbij_iff :
      Module.FinitePresentation R M ↔
        ∀ (A : Type (max u v)) (Q : Type u) [AddCommGroup Q] [Module R Q],
          Function.Bijective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)) :=
    show
      Module.FinitePresentation R M ↔
        ∀ (A : Type (max u v)) (Q : Type u) [AddCommGroup Q] [Module R Q],
          Function.Bijective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q))
    from module_finitePresentation_tfae_tensorProduct_pi_bijective.out 0 2
  constructor
  · intro hML
    have hsurj_all := hsurj_iff.1 (show Module.Finite R M from inferInstance)
    have hinj_pi :
        ∀ (A : Type (max u v)) (Q : A → Type u) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Injective (TensorProduct.piRightHom R R M Q) :=
      show
        ∀ (A : Type (max u v)) (Q : A → Type u) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Injective (TensorProduct.piRightHom R R M Q)
      from (Module.mittagLeffler_iff_tensorProduct_piRight_injective.1 hML)
    have hinj_all :
        ∀ (A : Type (max u v)) (Q : Type u) [AddCommGroup Q] [Module R Q],
          Function.Injective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)) := by
      intro A Q _ _
      exact hinj_pi A (fun _ : A ↦ Q)
    exact hbij_iff.2 (fun A Q ↦ ⟨hinj_all A Q, hsurj_all A Q⟩)
  · intro hfp
    letI : Module.FinitePresentation R M := hfp
    infer_instance

-- Proof sketch: a projective module is a direct summand of a free module. The previous theorem
-- makes the ambient free module Mittag-Leffler, and Lemma `10.89.10` identifies Mittag-Leffler
-- direct sums with stagewise Mittag-Leffler summands, so the projective summand is
-- Mittag-Leffler.
/-- A projective `R`-module is Mittag-Leffler. -/
instance instMittagLefflerOfProjective [Module.Projective R M] :
    MittagLeffler R M := by
  sorry

section

variable [Module.Free R M]

/- Example 10.91.1 (3): free modules are projective via mathlib's owner instance
`Module.Projective.of_free`, so the Mittag-Leffler conclusion is direct instance inference from
`instMittagLefflerOfProjective`. -/
#check (inferInstance : MittagLeffler R M)

end

end

end Module

/-! ### Lemma_10_91_2 (from Chap10) -/
open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]

-- Proof sketch: for the forward implication, apply Lemma `10.89.6` to obtain the smallest
-- supporting submodule for each tensor in a finite free source. For the converse, use Lazard's
-- theorem to write `M` as a directed colimit of finite free modules, apply Remark `10.88.8` to
-- reduce to the dual inverse system, and identify the eventual images in the duals with the
-- smallest supporting submodules supplied by the hypothesis.
/-- Lemma 10.91.2: for a flat `R`-module `M`, the module `M` is Mittag-Leffler if and only if,
for every finite free `R`-module `F` and every tensor `x : F ⊗[R] M`, there exists a smallest
submodule `F' ≤ F` such that `x` lies in the image of `F' ⊗[R] M → F ⊗[R] M`. -/
theorem flat_mittagLeffler_iff_exists_smallest_supporting_submodule :
    MittagLeffler R M ↔
      ∀ (F : ModuleCat.{w} R) [Module.Free R F] [Module.Finite R F] (x : F ⊗[R] M),
        ∃ F' : Submodule R F,
          IsLeast { F'' : Submodule R F | x ∈ LinearMap.range (F''.subtype.rTensor M) } F' := sorry

namespace MittagLeffler

/-- For a flat Mittag-Leffler module, every tensor over a finite free source has a smallest
supporting submodule. -/
theorem exists_smallest_supporting_submodule [MittagLeffler R M]
    (F : ModuleCat.{w} R) [Module.Free R F] [Module.Finite R F] (x : F ⊗[R] M) :
    ∃ F' : Submodule R F,
      IsLeast { F'' : Submodule R F | x ∈ LinearMap.range (F''.subtype.rTensor M) } F' :=
  flat_mittagLeffler_iff_exists_smallest_supporting_submodule.mp
    (inferInstance : MittagLeffler R M) F x

end MittagLeffler

end

end Module

/-! ### Lemma_10_91_3 (from Chap10) -/
universe u v

namespace Module

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {A : Type v}

/- Domain triage:
- `source-facing`: the Stacks lemma asserting that the product module `R^A` is flat and
  Mittag-Leffler over a Noetherian ring.
- `core/canonical`: the owner predicates `Module.Flat` and `Module.MittagLeffler`.
- `bridge/view`: flatness is derived from the chapter owner theorem
  `coherent_tfae_flat_products` together with the canonical instance
  `noetherianRing_isCoherentRing`; the supporting-submodule criterion from
  `flat_mittagLeffler_iff_exists_smallest_supporting_submodule` supplies the Mittag-Leffler
  clause.
Primitive data are only the ring `R`, the index type `A`, and the product module `A → R`; the
coherence and supporting-submodule criteria are derived API of the owner abstractions. -/

-- Proof sketch: use Lemma `10.90.5` and clause `(3)` of `coherent_tfae_flat_products` to obtain
-- flatness of `A → R` directly from the chapter owner predicate `IsCoherentRing R`. Then apply the
-- criterion of Lemma `10.91.2`. For a finite free module `F` and tensor `x : F ⊗[R] R^A`,
-- identify `F ⊗[R] R^A` with `F^A` via Proposition `10.89.3`. The smallest supporting submodule
-- is generated by the coordinates of the family corresponding to `x`; since `R` is Noetherian and
-- `F` is finite free, this submodule is finite, so Lemma `10.91.2` yields the
-- Mittag-Leffler property.
/-- Lemma 10.91.3: if `R` is Noetherian and `A` is a set, then the product module `A → R` is flat
and Mittag-Leffler over `R`. -/
theorem noetherian_pi_flat_and_mittagLeffler :
    Module.Flat R (A → R) ∧ MittagLeffler R (A → R) := sorry

end

end Module

/-! ### Lemma_10_91_4 (from Chap10) -/
universe u

namespace Module

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-
Domain triage:
- `source-facing`: the Stacks lemma for the formal power series ring `MvPowerSeries (Fin n) R`;
- `core/canonical`: the owner predicates `Module.Flat` and `Module.MittagLeffler`;
- `bridge/view`: `MvPowerSeries σ R` is definitionally the product module `(σ →₀ ℕ) → R`, so the
  whole statement is a direct specialization of `noetherian_pi_flat_and_mittagLeffler`.
Primitive data are only the ring `R` and the monomial index type `(Fin n) →₀ ℕ`; the flat and
Mittag-Leffler clauses are derived API of the owner predicates. -/

/-- Lemma 10.91.4: for a Noetherian ring `R` and an integer `n`, the formal power series ring
`MvPowerSeries (Fin n) R`, viewed as an `R`-module, is flat and Mittag-Leffler. -/
lemma noetherian_mvPowerSeries_flat_and_mittagLeffler (n : ℕ) :
    Module.Flat R (MvPowerSeries (Fin n) R) ∧
      MittagLeffler R (MvPowerSeries (Fin n) R) := by
  simpa [MvPowerSeries] using
    (noetherian_pi_flat_and_mittagLeffler :
      Module.Flat R (((Fin n) →₀ ℕ) → R) ∧ MittagLeffler R (((Fin n) →₀ ℕ) → R))

end

end Module

/-! ### Example_10_91_5 (from Chap10) -/
noncomputable section

universe u v

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: if `M` were Mittag-Leffler, then the countably generated module `M` would be a
-- direct sum of countably generated submodules in the trivial one-summand way. Theorem `10.93.3`
-- would then imply that `M` is projective, contradicting `hproj`.
/-- Example 10.91.5: any flat countably generated non-projective `R`-module is not
Mittag-Leffler. This is the criterion used in the example to manufacture explicit
counterexamples. -/
theorem not_mittagLeffler_of_flat_of_countablyGenerated_of_not_projective
    [Flat R M] (hcg : CountablyGenerated R M) (hproj : ¬ Projective R M) :
    ¬ MittagLeffler R M := sorry

-- Proof sketch: Proposition `10.89.5` identifies the Mittag-Leffler condition with injectivity of
-- all tensor-product-to-product maps, while Example `10.89.1` exhibits a specific family
-- `Q_n = ℤ / nℤ` for which the corresponding map for `ℚ` is not injective.
/-- The `ℤ`-module `ℚ` is not Mittag-Leffler. -/
theorem rat_not_mittagLeffler :
    ¬ MittagLeffler ℤ ℚ := sorry

end

section

variable (k : Type u) [Field k]

/-- The quotient `k[[x]] / (x^n)` viewed as a `k[[x]]`-module. -/
abbrev powerSeriesQuotientByXPow (n : ℕ+) :=
  PowerSeries k ⧸ Ideal.span ({(PowerSeries.X : PowerSeries k) ^ (n : ℕ)} : Set (PowerSeries k))

/-- The product `∏_{n ≥ 1} k[[x]] / (x^n)` from the power-series example. -/
abbrev powerSeriesQuotientProduct :=
  (n : ℕ+) → powerSeriesQuotientByXPow k n

/-- The `x`-adic ideal of `k[[x]]`. -/
abbrev powerSeriesXIdeal : Ideal (PowerSeries k) :=
  Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k))

/-- The direct sum `⨁_{n ≥ 1} k[[x]] / (x^n)` used before taking `x`-adic completion. -/
abbrev powerSeriesQuotientDirectSum :=
  Π₀ n : ℕ+, powerSeriesQuotientByXPow k n

/-- The `x`-adic completion of `⨁_{n ≥ 1} k[[x]] / (x^n)`. -/
abbrev powerSeriesQuotientDirectSumCompletion :=
  AdicCompletion (powerSeriesXIdeal k) (powerSeriesQuotientDirectSum k)

-- Proof sketch: use the element `ξ` supported at powers of two from the textbook. Its
-- annihilator in `(∏ n, R/(x^n)) / x^l` behaves like `x^(l / 2)` along powers of two, which is
-- incompatible with the annihilator growth permitted by Proposition `10.88.6 (1)` for a
-- Mittag-Leffler module.
/-- The product `∏_{n ≥ 1} k[[x]] / (x^n)` is not Mittag-Leffler over `k[[x]]`. -/
theorem powerSeriesQuotientProduct_not_mittagLeffler :
    ¬ MittagLeffler (PowerSeries k) (powerSeriesQuotientProduct k) := sorry

-- Proof sketch: the same annihilator calculation applies because the element `ξ` from the
-- textbook actually lies in the `x`-adic completion of the direct sum, so the previous
-- contradiction with Proposition `10.88.6 (1)` still goes through.
/-- The `x`-adic completion of `⨁_{n ≥ 1} k[[x]] / (x^n)` is not Mittag-Leffler over `k[[x]]`. -/
theorem powerSeriesQuotientDirectSumCompletion_not_mittagLeffler :
    ¬ MittagLeffler (PowerSeries k) (powerSeriesQuotientDirectSumCompletion k) := sorry

/-- The square-zero quotient ring `k[a, b] / (a^2, ab, b^2)` of the final example. -/
abbrev squareZeroPairRing :=
  MvPolynomial (Fin 2) k ⧸
    Ideal.span
      ({(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1,
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ^ 2} : Set (MvPolynomial (Fin 2) k))

/-- The class of `a` in `k[a, b] / (a^2, ab, b^2)`. -/
abbrev squareZeroPairRingA : squareZeroPairRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The class of `b` in `k[a, b] / (a^2, ab, b^2)`. -/
abbrev squareZeroPairRingB : squareZeroPairRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The finitely presented algebra `R[t] / (at - b)` over `R = k[a, b] / (a^2, ab, b^2)`. -/
abbrev squareZeroPairAlgebra :=
  Polynomial (squareZeroPairRing k) ⧸
    Ideal.span
      ({Polynomial.C (squareZeroPairRingA k) * Polynomial.X - Polynomial.C (squareZeroPairRingB k)} :
        Set (Polynomial (squareZeroPairRing k)))

local instance squareZeroPairRingCommRing : CommRing (squareZeroPairRing k) :=
  show CommRing (squareZeroPairRing k) from Ideal.Quotient.commRing _

local instance squareZeroPairAlgebraCommRing : CommRing (squareZeroPairAlgebra k) :=
  show CommRing (squareZeroPairAlgebra k) from Ideal.Quotient.commRing _

local instance squareZeroPairAlgebraAlgebra : Algebra (squareZeroPairRing k) (squareZeroPairAlgebra k) :=
  show Algebra (squareZeroPairRing k) (squareZeroPairAlgebra k) from Ideal.instAlgebraQuotient _ _

local instance squareZeroPairAlgebraModule : Module (squareZeroPairRing k) (squareZeroPairAlgebra k) :=
  (algebraMap (squareZeroPairRing k) (squareZeroPairAlgebra k)).toModule

-- Proof sketch: the quotient `R[t] / (at - b)` is generated by the powers of `t`, so it is
-- countably generated as an `R`-module.
/-- The algebra `R[t] / (at - b)` is countably generated as an `R`-module. -/
theorem squareZeroPairAlgebra_countablyGenerated :
    CountablyGenerated (squareZeroPairRing k) (squareZeroPairAlgebra k) := sorry

-- Proof sketch: the ring `squareZeroPairRing k` is Artinian local and hence henselian. If
-- `squareZeroPairAlgebra k` were Mittag-Leffler, Lemma `10.153.13` would split it as a direct sum
-- of finitely presented modules. The textbook notes that this module is indecomposable, so such a
-- decomposition is impossible.
/-- The algebra `R[t] / (at - b)` is not Mittag-Leffler as an `R`-module for
`R = k[a, b] / (a^2, ab, b^2)`. -/
theorem squareZeroPairAlgebra_not_mittagLeffler :
    ¬ MittagLeffler (squareZeroPairRing k) (squareZeroPairAlgebra k) := sorry

end

end Module
