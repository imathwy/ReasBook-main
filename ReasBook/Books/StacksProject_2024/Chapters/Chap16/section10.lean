import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_16_10_1_Ogoma (from Chap16) -/
universe u v

section

open Submodule

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable (S : Submonoid A)

local notation "Aₛ" => Localization S
local notation "Mₛ" => LocalizedModule S M

/-
Domain-style sampling:
- primary domain: commutative algebra of finite modules over a Noetherian ring, localized modules,
  and scalar-torsion submodules;
- sampled owner API:
  `Submodule.torsionBy`,
  `Submodule.mem_torsionBy_iff`,
  `isSMulRegular_iff_torsionBy_eq_bot`,
  `LinearMap.lsmul_eq_distribSMultoLinearMap`;
- best owner abstraction: `Submodule.torsionBy`; the current kernel-of-`LinearMap.lsmul` phrasing
  is only the low-level bridge/view;
- primitive data: the ambient ring/module, the localization `Localization S`, and the scalar `π`;
  the kernel of scalar multiplication is derived from the owner `Submodule.torsionBy`, so it
  should not remain the public surface.

Layer triage:
- `source-facing`: Ogoma's stabilization lemma itself;
- `core/canonical`: `Submodule.torsionBy`;
- `bridge/view`: `LinearMap.ker (LinearMap.lsmul ...)`.
-/

-- Proof sketch: Let `K = M[π]` and let `K'` be the preimage in `M` of
-- `(S⁻¹M)[π^2]`. The hypothesis says that `K'/K` localizes to zero. Since
-- `K'/K` is a finite `A`-module over a Noetherian ring, some `s ∈ S` annihilates `K'/K`,
-- and then the same denominator works after replacing `s` by any positive power.
/-- Lemma 16.10.1 (Ogoma): if the `π`-torsion and `π^2`-torsion submodules of `S⁻¹M` agree, then
some `s ∈ S` makes the `s^n * π`-torsion and `(s^n * π)^2`-torsion submodules of `M` agree for
every positive integer `n`. -/
theorem exists_mem_submonoid_torsionBy_eq_of_localized (π : A)
    (htors :
      torsionBy Aₛ Mₛ (algebraMap A Aₛ π) = torsionBy Aₛ Mₛ ((algebraMap A Aₛ π) ^ 2)) :
    ∃ s : S, ∀ n : ℕ+,
      torsionBy A M (((s : A) ^ (n : ℕ)) * π) =
        torsionBy A M ((((s : A) ^ (n : ℕ)) * π) ^ 2) := sorry

end

/-! ### Lemma_16_10_2 (from Chap16) -/
universe u

open IsLocalRing

section

variable {Λ : Type u} [CommRing Λ]
variable (q : PrimeSpectrum Λ)

local notation "Λq" => Localization.AtPrime q.asIdeal

/- Domain-style sampling pass.

Primary domains:
* regular local rings and regular systems of parameters in localizations;
* finite-family prefix ideals and quotient-element annihilator/torsion ideals in commutative
  algebra.

Sampled owner declarations:
* `IsLocalRing.parameterIdeal`;
* `IsLocalRing.IsRegularSystemOfParameters`;
* `isRegularLocalRing_iff_exists_regularSystemOfParameters`;
* `exists_regularSystemOfParameters_with_prefix_span_eq_of_quotient_isRegularLocalRing`;
* `Ideal.torsionOf`;
* `Submodule.annihilator_span_singleton`.

Owner abstractions:
* the regular-system owner `IsRegularSystemOfParameters` in the local ring
  `Λq`;
* the successive quotient ideals are expressed directly by `Ideal.span` of the earlier `e`-th
  powers of the lifted family, rather than by a parallel local owner;
* the element-annihilator owner `Ideal.torsionOf` for quotient elements.

Primitive data: a chosen family in the maximal ideal of the localization.

Derived API: a lift of that family to `Λ`, the `n`-th-power containment in `I`, and the
successive quotient annihilator equalities for the lifted family.

Source/core/bridge triage:
* source-facing: the lifted elements `π₁, …, π_d ∈ Λ` with their power and annihilator
  conditions;
* core/canonical: `IsLocalRing.IsRegularSystemOfParameters` on
  `Λq`, together with direct `Ideal.span` expressions for the successive quotient ideals and
  `Ideal.torsionOf` for the quotient-element annihilator ideals;
* bridge/view: the equality identifying the localized images of the lifted family with the chosen
  regular system of parameters.
-/

-- Proof sketch: choose `d` generators of the maximal ideal of the regular local ring
-- `Λq`, clear denominators so that their `n`-th powers lie in `I`,
-- and then inductively multiply later generators by elements outside `q` using Ogoma's lemma so
-- that the annihilator equality holds in each successive quotient.
/-- Lemma 16.10.2: let `Λ` be a Noetherian ring, let `I ⊆ q` be an ideal contained in a prime
`q`, and let `n`, `e`, `d` be integers with `0 < e`. Assume that `q^n` becomes contained in `I`
after localizing at `q`, and that `Λq` is a regular local ring of dimension `d`. Then there are
elements `π₁, …, π_d` of `Λ` whose localized images form a regular system of parameters of `Λ_q`,
whose `n`-th powers lie in `I`, and whose images in each successive quotient by the earlier
`e`-th powers have the same annihilator as the squares of those images. -/
theorem exists_parameters_generating_localized_prime_pow_mem_ideal_and_annihilator_stable
    (I : Ideal Λ) (n e d : ℕ)
    (he : 0 < e) (hIq : I ≤ q.asIdeal)
    (hqpow : Ideal.map (algebraMap Λ Λq) (q.asIdeal ^ n) ≤ Ideal.map (algebraMap Λ Λq) I)
    [IsNoetherianRing Λ]
    [IsRegularLocalRing Λq]
    (hdim : ringKrullDim Λq = d) :
    ∃ (π : Fin d → Λ) (x : Fin d → maximalIdeal Λq),
      IsRegularSystemOfParameters x ∧
        (∀ i, (x i : Λq) = algebraMap Λ Λq (π i)) ∧
        (∀ i, (π i) ^ n ∈ I) ∧
        ∀ i : Fin d,
          let J : Ideal Λ := Ideal.span (Set.range fun j : Fin i.1 ↦ π (Fin.castLE
            (Nat.le_of_lt i.isLt) j) ^ e)
          Ideal.torsionOf (Λ ⧸ J) (Λ ⧸ J) (Ideal.Quotient.mk J (π i)) =
            Ideal.torsionOf (Λ ⧸ J) (Λ ⧸ J) (Ideal.Quotient.mk J ((π i) ^ 2)) := sorry

end

/-! ### Lemma_16_10_3 (from Chap16) -/
universe u v w

namespace Algebra

open PrimeSpectrum
open scoped Algebra

section

variable {k : Type u} {A : Type v} {Λ : Type w}
variable [Field k] [CommRing A] [CommRing Λ]
variable [Algebra k A] [Algebra k Λ] [Algebra A Λ] [IsScalarTower k A Λ]
variable [FinitePresentation k A] [Algebra.FiniteType k Λ]

/-
Domain-style sampling:
- primary domain: primewise resolution statements for finitely presented algebras over a field,
  organized around the Chapter 16 owner predicate `ResolvableAtPrime`;
- sampled owner declarations:
  `ResolvableAtPrime`,
  `resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero`,
  `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField`,
  `Algebra.FiniteType.isNoetherianRing`;
- best owner abstraction: the public statement should stay source-facing on
  `ResolvableAtPrime k A Λ 𝔮`; the regular-local-ring and separable-residue-field hypotheses are
  primitive source data, and the finite-type hypothesis on `Λ` is primitive bridge-side data
  needed to reuse the chapter's canonical smoothness criterion and to recover the Noetherian
  hypothesis on `Λ` canonically via `Algebra.FiniteType.isNoetherianRing`; primewise smoothness is
  derived API coming from `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField`;
- primitive data: a minimal prime `𝔮` of `h(A⁄k, Λ)`, regularity of `Λ_𝔮`, separability of
  `κ(𝔮) / k` in the Stacks Project sense, and finite type of `Λ` over `k`;
- derived API: the local smoothness input used to build the local resolution and the final passage
  from a local resolution at `𝔮` to `ResolvableAtPrime k A Λ 𝔮`.

Source/core/bridge triage:
- `source-facing`: the theorem that `k → A → Λ ⊃ 𝔮` is resolvable;
- `core/canonical`: `ResolvableAtPrime`;
- `bridge/view`: the primewise smoothness criterion
  `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField` together with the local-to-global
  resolution owner `resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero`.
-/

section Prime

variable (q : PrimeSpectrum Λ)

local notation "𝔮" => q.asIdeal
local notation "Λ_𝔮" => Localization.AtPrime q.asIdeal

-- Proof sketch: choose parameters in `Λ` as in Lemma `16.10.2`, use Lemma `16.9.2` to construct
-- a local resolution after quotienting by the corresponding eighth powers, and then apply the
-- local-to-global owner theorem `resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero`.
-- The finite-type and separable-residue-field hypotheses identify regularity of `Λ_𝔮` with
-- smoothness at `𝔮` via Lemma `10.140.5`, which supplies the smoothness input needed in the local
-- construction; the finite-type hypothesis also supplies the Noetherianity of `Λ` canonically via
-- `Algebra.FiniteType.isNoetherianRing`.
/-- Lemma 16.10.3: in Situation `16.9.1`, if `k` is a field, `A` is finitely presented over `k`,
`Λ` is a finite type `k`-algebra, `q` is a minimal prime of `𝔥_A`, the local ring
`Λ_q` is regular, and the residue field extension `κ(q) / k` is separable, then
`k → A → Λ ⊃ q` is resolvable. -/
theorem resolvableAtPrime_of_minimalPrime_regularLocalRing_and_separable_residueField
    (hq : 𝔮 ∈ (h(A⁄k, Λ)).minimalPrimes)
    [IsRegularLocalRing Λ_𝔮]
    [IsSeparableOver k q.asIdeal.ResidueField] :
    ResolvableAtPrime k A Λ 𝔮 := sorry

end Prime

end

end Algebra
