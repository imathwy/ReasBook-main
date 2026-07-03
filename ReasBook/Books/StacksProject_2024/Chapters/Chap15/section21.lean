import Mathlib
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_21_1 (from Chap15) -/
open Polynomial

universe u

/-
Domain sampling for this item:
* primary domain: polynomial factorization over a commutative ring at a chosen root;
* sampled owner declarations: `mul_divByMonic_eq_iff_isRoot`, `dvd_iff_isRoot`, `monic_X_sub_C`, and
  `Monic.of_mul_monic_left`;
* layer triage:
  - `source-facing`: the textbook existential factorization statement;
  - `core/canonical`: the canonical quotient-factorization owner
    `mul_divByMonic_eq_iff_isRoot`;
  - `bridge/view`: the monicity of the canonical quotient `P /ₘ (X - C α)`, derived from
    `Monic.of_mul_monic_left`.
* owner decision: keep the textbook existential theorem as the public source-facing item and derive
  it directly from the canonical `Polynomial` quotient factorization at a root rather than choosing
  an arbitrary divisibility witness.
-/

/-- Lemma 15.21.1: a monic polynomial `P` over a commutative ring with root `α` factors as
`(X - C α) * Q` for some monic polynomial `Q`. -/
theorem exists_monic_factor_of_isRoot {R : Type u} [CommRing R] (P : R[X]) (hP : P.Monic)
    {α : R} (hα : P.IsRoot α) :
    ∃ Q : R[X], Q.Monic ∧ P = (X - C α) * Q := by
  refine ⟨P /ₘ (X - C α), (monic_X_sub_C α).of_mul_monic_left ?_, ?_⟩
  · simpa [mul_divByMonic_eq_iff_isRoot.mpr hα] using hP
  exact (mul_divByMonic_eq_iff_isRoot.mpr hα).symm

/-! ### Lemma_15_21_2 (from Chap15) -/
open Polynomial

universe u

/- Domain sampling for this item:
* primary domain: commutative algebra of monic polynomials, finite free extensions, and linear
  factorization after adjoining a root;
* sampled owner declarations: `dvd_iff_isRoot`, `AdjoinRoot.isRoot_root`,
  `Polynomial.Monic.free_adjoinRoot`, and `Polynomial.Monic.finite_adjoinRoot`;
* layer triage:
  - `source-facing`: existence of a finite free `R`-algebra in which the base change of `P` has a
    linear factor with monic quotient;
  - `core/canonical`: the canonical witness algebra `AdjoinRoot P` and its distinguished root;
  - `bridge/view`: the specialization of `exists_monic_factor_of_isRoot` to `AdjoinRoot P`.
* owner decision: the numbered lemma should remain source-facing and expose the extension data,
  while `AdjoinRoot` remains only the canonical proof witness.
* primitive data: the extension ring `R'`, its `R`-algebra structure, the finite/free module
  structure, and the root `α`;
* derived API: the monic factorization over `R'[X]`, obtained by applying
  `exists_monic_factor_of_isRoot` to `AdjoinRoot.isRoot_root`. -/

/-- Lemma 15.21.2: for a monic polynomial `P` over a commutative ring `R`, there exists a finite
free `R`-algebra `R'` and an element `α : R'` such that `P` base-changed to `R'` factors as
`(X - C α) * Q` with `Q` monic. -/
-- Proof sketch: take `R' = AdjoinRoot P` and `α = AdjoinRoot.root P`. The extension is finite free
-- by `Polynomial.Monic.free_adjoinRoot` and `Polynomial.Monic.finite_adjoinRoot`, and
-- `AdjoinRoot.isRoot_root P` identifies the canonical quotient by `X - C α`.
theorem exists_finiteFree_extension_with_monic_linear_factor {R : Type u} [CommRing R]
    {P : R[X]} (hP : P.Monic) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Module.Free R R') (α : R') (Q : R'[X]),
      Q.Monic ∧ P.map (algebraMap R R') = (X - C α) * Q := by
  letI : Module.Finite R (AdjoinRoot P) := hP.finite_adjoinRoot
  letI : Module.Free R (AdjoinRoot P) := hP.free_adjoinRoot
  have hroot : (P.map (algebraMap R (AdjoinRoot P))).IsRoot (AdjoinRoot.root P) := by
    simpa [-AdjoinRoot.algebraMap_eq] using AdjoinRoot.isRoot_root P
  obtain ⟨Q, hQ, hfactor⟩ :=
    exists_monic_factor_of_isRoot (P.map (algebraMap R (AdjoinRoot P))) (hP.map _) hroot
  exact ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance,
    AdjoinRoot.root P, Q, hQ, hfactor⟩

/-! ### Lemma_15_21_3 (from Chap15) -/
open scoped TensorProduct
open MvPolynomial

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]

/- Domain sampling for this item:
* primary domain: finite polynomial quotient models for finite algebras after finite free base
  change;
* sampled declarations: `exists_finiteFree_extension_with_monic_linear_factor`,
  `Algebra.FiniteType.iff_quotient_mvPolynomial''`, `MvPolynomial.aeval`, and
  `Algebra.TensorProduct.commRight`;
* layer triage:
  - `source-facing`: the existence of a finite free injective base change after which `S` is a
    quotient of a split polynomial algebra;
  - `core/canonical`: `Algebra.FiniteType.iff_quotient_mvPolynomial''` for quotient presentations
    by polynomial algebras, together with the canonical base-change owner `R' ⊗[R] S`;
  - `source-facing owner`: the quotient ring
    `MvPolynomial (Fin n) R' ⧸ Ideal.span (Set.range fun i ↦ ∏ j, (X i - C (α i j)))`
    together with its canonical `R'`-algebra map to `R' ⊗[R] S`;
  - `bridge/view`: the textbook right-tensor presentation `S ⊗[R] R'`, identified with the chosen
    owner by `Algebra.TensorProduct.commRight`.
* owner decision: keep the source-facing split quotient presentation, but phrase it directly as an
  `R'`-algebra quotient of the canonical base-change owner `R' ⊗[R] S`; the unsplit polynomial
  quotient owner already lives upstream in `Algebra.FiniteType.iff_quotient_mvPolynomial''`, so
  this file should add only the extra split-relations content.
* primitive data: the finite free injective extension `R → R'`, the arities `d`, and the chosen
  roots `α`;
* derived API: the quotient type and its surjective map to `R' ⊗[R] S`, obtained from
  `MvPolynomial.aeval` followed by the canonical ideal quotient lift; the right-tensor textbook
  form is only a bridge via tensor commutativity.
  -/

-- Proof sketch: choose finitely many generators `x₁, …, xₙ` of the finite `R`-algebra `S`. For
-- each generator, pick a monic annihilating polynomial over `R`, then apply Lemma `15.21.2`
-- repeatedly to obtain a finite free `R`-algebra `R'` over which all these polynomials split
-- completely. After base change, send `X i` to `1 ⊗ₜ[R] xᵢ` in the canonical base-change owner
-- `R' ⊗[R] S`; the split relations vanish, so `MvPolynomial.aeval` factors through the quotient
-- and remains surjective.
/-- Lemma 15.21.3: after a finite free injective base change `R → R'`, the canonical base-changed
algebra `R' ⊗[R] S` (equivalently the textbook `S ⊗[R] R'`) is a quotient of a split polynomial
algebra `R'[T₁, …, Tₙ] / (P₁(T₁), …, Pₙ(Tₙ))`, where each `Pᵢ` is a product of linear factors over
`R'`; the equivalence with `S ⊗[R] R'` is the tensor-symmetry bridge
`Algebra.TensorProduct.commRight`. -/
theorem exists_finiteFree_baseChange_surjective_splitPolynomialQuotient
    :
    ∃ (n : ℕ) (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R')
      (_ : Function.Injective (algebraMap R R')) (_ : Module.Finite R R')
      (_ : Module.Free R R') (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R'),
      ∃ φ :
        (MvPolynomial (Fin n) R' ⧸
          Ideal.span (Set.range fun i ↦ ∏ j : Fin (d i), (X i - C (α i j)))) →ₐ[R']
          (R' ⊗[R] S),
        Function.Surjective φ := sorry

end

/-! ### Lemma_15_21_4 (from Chap15) -/
open MvPolynomial PrimeSpectrum
open scoped BigOperators

universe u

section

variable {R : Type u} [CommRing R]
variable {n : ℕ} (d : Fin n → ℕ)

/- Domain sampling for this item:
* primary domain: affine prime-spectrum images for quotients and finite products of commutative
  rings;
* sampled core owners: `PrimeSpectrum.range_comap_of_surjective`, `MvPolynomial.eval`,
  `Pi.ker_ringHom`, `PrimeSpectrum.iUnion_range_comap_comp_evalRingHom`, and `zeroLocus_inf`;
* layer: this lemma is a `source-facing` split-polynomial specialization of those owner
  constructions, not a new owner abstraction. -/
-- Proof sketch: form the product of the evaluation maps indexed by
-- `k : ∀ i : Fin n, Fin (d i)`. The split-polynomial hypothesis ensures that the quotient map to
-- this finite product is surjective, so `range_comap_of_surjective` identifies the spectrum image
-- with the zero locus of the kernel. Then compute that kernel with `Pi.ker_ringHom`, and rewrite
-- the finite-product spectrum image through `iUnion_range_comap_comp_evalRingHom` and
-- `zeroLocus_inf`.
/-- Lemma 15.21.4: if `J ⊆ R[T₁, …, Tₙ]` contains, for each variable `Tᵢ`, the split polynomial
`∏ⱼ (Tᵢ - αᵢⱼ)`, then for `S = R[T₁, …, Tₙ] / J` the image of `Spec(S) → Spec(R)` is the zero
locus `V(⋂ₖ Jₖ)`, where `Jₖ` is the image of `J` under evaluation at the tuple
`Tᵢ ↦ αᵢ,ₖᵢ`. -/
theorem range_comap_polynomial_quotient_eq_zeroLocus_iInf_evaluationImage
    (J : Ideal (MvPolynomial (Fin n) R)) (α : ∀ i : Fin n, Fin (d i) → R)
    (hJ : ∀ i : Fin n, ∏ j : Fin (d i), (X i - C (α i j)) ∈ J) :
    Set.range (comap (algebraMap R (MvPolynomial (Fin n) R ⧸ J))) =
      zeroLocus
        (⨅ k : ∀ i : Fin n, Fin (d i),
          Ideal.map (eval fun i ↦ α i (k i)) J) := sorry

end

/-! ### Lemma_15_21_5 (from Chap15) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Module.Finite R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: flatness descent for modules under finite injective base change over Noetherian
  rings;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange`,
  `flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct`,
  `Module.Flat.of_flat_tensorProduct`;
- best owner abstraction: the canonical flatness predicate `Module.Flat`, with the Chapter 10
  nilpotent-ideal descent criterion as the upstream owner theorem in the minimal dependency
  closure;
- primitive data: the Noetherian base ring `R`, the finite `R`-algebra `S`, the injective algebra
  map `R → S`, and the `R`-module `M`;
- derived API: flatness of the base-changed module `S ⊗[R] M`, expressed in the canonical Lean
  model of base change rather than through a parallel wrapper or renamed tensor-product owner.

Layering:
- this item is `source-facing`: it is the Noetherian finite-extension descent statement from the
  source text;
- `core/canonical`: `Module.Flat` and the Chapter 10 owner theorem
  `flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange`;
- companion source-facing specialization already upstream:
  `flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct`;
- no separate `bridge/view` declaration is warranted here.
-/

-- Proof sketch: after a finite locally free base change reducing to the split polynomial-quotient
-- case of Lemmas `15.21.3` and `15.21.4`, one obtains a nilpotent ideal `I ⊆ R` such that
-- `M / IM` is flat over `R ⧸ I`. Then apply the nilpotent-ideal descent criterion
-- `10.101.5`, using injectivity of `R → S` and the assumed flatness of `S ⊗[R] M`.
/-- Lemma 15.21.5: let `R → S` be a finite injective homomorphism of Noetherian rings, and let
`M` be an `R`-module. If the base change `S ⊗[R] M` is flat over `S`, then `M` is flat over `R`.
This is the canonical Lean form of the textbook statement for `M ⊗_R S`, and it remains a
source-facing Chapter 15 theorem rather than a renamed wrapper around the Chapter 10 owner
criterion. -/
theorem flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := sorry

end

/-! ### Lemma_15_21_6 (from Chap15) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]
variable (n : ℕ)
local notation "P" => MvPolynomial (Fin n) R
variable {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
variable [Module.FinitePresentation (MvPolynomial (Fin n) R) M]

/- Domain triage:
- primary domain: flatness descent for modules finitely presented over a polynomial `R`-algebra
  along an injective integral base change `R → S`;
- sampled owner declarations:
  `Module.Flat`,
  `Module.FinitePresentation`,
  `MvPolynomial (Fin n) R`,
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`;
- best owner abstraction: the canonical flatness predicate `Module.Flat R M`, with the polynomial
  arity `n` kept explicit because it is not inferable from the module arguments;
- primitive data: the injective integral algebra map `R → S`, the polynomial owner ring `P`,
  the `P`-module structure on `M`, and the finite-presentation hypothesis
  `[Module.FinitePresentation P M]`;
- derived API: the base-change flatness hypothesis and flatness conclusion for the canonical
  restricted-scalar `R`-module `RestrictScalars R P M`.

Layering:
- `source-facing`: the polynomial finite-presentation descent statement from the source text;
- `core/canonical`: `Module.Flat` and `Module.FinitePresentation`;
- `bridge/view`: the Chapter 15 finite-base-change descent theorem
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`;
  this file is the source-facing polynomial finite-presentation specialization feeding into that
  bridge, not a second flatness owner.
-/

-- Proof sketch: choose a finite presentation of `M` over `R[x_1, ..., x_n]`, spread the finitely
-- many coefficients to a finitely generated `ℤ`-subalgebra `R₀ ⊆ R` and a finite `R₀`-subalgebra
-- `S₀ ⊆ S`, descend flatness of `S ⊗[R] RestrictScalars R P M` to some stage by finite
-- presentation, apply Lemma `15.21.5` to `R₀ → S₀`, and then recover flatness of
-- `RestrictScalars R P M` over `R` by base change via Lemma `10.39.7`.
/-- Lemma 15.21.6: let `R → S` be an injective integral ring map, and let `M` be a finitely
presented `P`-module, where `P = R[x₁, …, xₙ]` is formalized by `MvPolynomial (Fin n) R`.
If the base change `S ⊗[R] (RestrictScalars R P M)` is flat over `S`, then the restricted
`R`-module `RestrictScalars R P M` is flat over `R`. -/
theorem flat_of_injective_algebraMap_of_isIntegral_of_flat_tensorProduct_of_finitePresentation_mvPolynomial
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] RestrictScalars R P M)) :
    Module.Flat R (RestrictScalars R P M) := sorry

end

/-! ### Lemma_15_21_7 (from Chap15) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Module.Finite R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: descent of projective modules under finite injective base change over
  Noetherian commutative rings;
- sampled owner declarations of the same kind:
  `Module.Projective`,
  `Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated`,
  `Module.Flat.of_projective`,
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`,
  `projective_of_projective_quotient_of_isNilpotent_of_flat`;
- best owner abstraction: the canonical owner predicate `Module.Projective R M`;
- primitive data: the Noetherian base ring `R`, the finite `R`-algebra `S`, the injective
  algebra map `R → S`, and the `R`-module `M`;
- derived API: the descended projectivity of `M`, stated directly in terms of the owner predicate
  rather than via a parallel wrapper for the textbook module `M ⊗_R S`.

Layering:
- this numbered item is `source-facing`: it is the textbook finite-injective descent statement;
- `core/canonical`: `Module.Projective`, together with the flatness owner
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`, the
  projective-to-flat bridge `Module.Flat.of_projective`, and the Chapter 10 nilpotent-thickening
  descent theorem
  `projective_of_projective_quotient_of_isNilpotent_of_flat`;
- no separate `bridge/view` owner is warranted here: the source-facing statement already lands
  directly in the canonical owner predicate `Module.Projective`.
-/

-- Proof sketch: projective modules are flat, so
-- `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`
-- descends flatness of `M` from `hproj`. After the same finite locally free reduction used in
-- Lemmas `15.21.3` and `15.21.4`, one gets a nilpotent ideal `I` such that `M / IM` is
-- projective over `R ⧸ I`; the Chapter 10 projective descent theorem
-- `projective_of_projective_quotient_of_isNilpotent_of_flat` then finishes.
/-- Lemma 15.21.7: let `R → S` be a finite injective homomorphism of Noetherian rings, and let
`M` be an `R`-module. If the base change `S ⊗[R] M` is projective over `S`, then `M` is
projective over `R`. This is the canonical Lean form of the textbook statement for
`M ⊗_R S`, and it remains a source-facing Chapter 15 theorem rather than a renamed wrapper around
an upstream owner theorem with different hypotheses. -/
theorem projective_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_projective_tensorProduct
    (hinj : Function.Injective (algebraMap R S))
    (hproj : Module.Projective S (S ⊗[R] M)) :
    Module.Projective R M := by
  letI : Module.Projective S (S ⊗[R] M) := hproj
  have hflatTensor : Module.Flat S (S ⊗[R] M) := Module.Flat.of_projective
  have hflat : Module.Flat R M :=
    flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct
      hinj hflatTensor
  sorry

end
