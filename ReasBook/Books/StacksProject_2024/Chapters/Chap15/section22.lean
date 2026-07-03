import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.List.TFAE
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_22_1 (from Chap15) -/
universe u v

/-
Domain-style sampling:
- primary domain: torsion theory for modules over commutative semirings, with the source-facing
  nonzero-scalar reformulation specialized to domains;
- sampled owner API:
  `Submodule.torsion`,
  `Submodule.mem_torsion_iff`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  `Submodule.isTorsion'_iff_torsion'_eq_top`;
- best owner abstraction: `Submodule.torsion`, with proposition-level owners
  `Module.IsTorsionFree` and `Module.IsTorsion`;
- source-facing layer: textbook restatements describing torsion elements, torsion-free modules, and
  torsion modules in terms of membership in `Submodule.torsion`;
- core/canonical layer: the upstream mathlib owners listed above;
- bridge/view layer: the local textbook reformulations below.

Primitive data are only the ambient ring and module. The torsion submodule itself and the
proposition-level torsion / torsion-free owners are already canonical upstream, so this file should
recall `Submodule.torsion` directly and keep only the source-facing bridge statements that change
the surface wording from `R⁰`-annihilators to nonzero scalars or to membership in the torsion
submodule. In particular, `Submodule.torsion`, `Submodule.mem_torsion_iff`, and the torsion-owner
bridge live at the `CommSemiring` / `AddCommMonoid` level; only the domain-specific restatement in
terms of nonzero scalars needs `IsDomain`, while the torsion-free bridge through
`Submodule.isTorsionFree_iff_torsion_eq_bot` still lives at the `CommRing` / `AddCommGroup` level.
-/

section

open Module

section Domain

variable {R : Type u} [CommSemiring R] [IsDomain R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Definition 15.22.1: over a domain, the canonical torsion submodule `Submodule.torsion R M`
collects exactly the torsion elements of `M`, i.e. those annihilated by some nonzero scalar. -/
recall Submodule.torsion

-- Proof sketch: unfold `Submodule.torsion`; in a domain, non-zero-divisors are exactly the
-- nonzero scalars, so membership is equivalent to the existence of a nonzero annihilator.
/-- An element of a module over a domain is torsion exactly when it lies in the canonical torsion
submodule. -/
theorem mem_torsion_iff_exists_ne_zero_smul_eq_zero (x : M) :
    x ∈ Submodule.torsion R M ↔ ∃ f : R, f ≠ 0 ∧ f • x = 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, mem_nonZeroDivisors_iff_ne_zero.mp f.2, hf⟩
  · rintro ⟨f, hf0, hf⟩
    exact ⟨⟨f, mem_nonZeroDivisors_iff_ne_zero.mpr hf0⟩, hf⟩

end Domain

section DomainRing

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: use the canonical owner theorem
-- `Submodule.isTorsionFree_iff_torsion_eq_bot` and rewrite `Submodule.torsion R M = ⊥` as the
-- statement that every torsion element is zero.
/-- A module over a domain is torsion-free exactly when its only torsion element is `0`. -/
theorem isTorsionFree_iff_forall_mem_torsion_eq_zero :
    IsTorsionFree R M ↔ ∀ x : M, x ∈ Submodule.torsion R M → x = 0 := by
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot, Submodule.eq_bot_iff]

/-- Over a Noetherian domain, a torsion-free module has no nonzero associated primes. -/
theorem Module.not_mem_associatedPrimes_of_ne_bot [IsNoetherianRing R] [IsTorsionFree R M]
    {p : Ideal R} (hp : p ≠ ⊥) : p ∉ associatedPrimes R M := by
  intro hp_assoc
  have hp_not_le : ¬ p ≤ (⊥ : Ideal R) := by
    intro h
    exact hp (le_antisymm h bot_le)
  rw [SetLike.not_le_iff_exists] at hp_not_le
  obtain ⟨r, hrp, hr0⟩ := hp_not_le
  have hr_zeroDiv : r ∈ { a : R | ∃ x : M, x ≠ 0 ∧ a • x = 0 } := by
    rw [← biUnion_associatedPrimes_eq_zero_divisors R M]
    exact Set.mem_iUnion_of_mem p <| Set.mem_iUnion_of_mem hp_assoc hrp
  rcases hr_zeroDiv with ⟨x, hx0, hrx⟩
  exact hr0 ((smul_eq_zero.mp hrx).resolve_right hx0)

end DomainRing

section Semiring

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

-- Proof sketch: `Module.IsTorsion` and membership in `Submodule.torsion` are already equivalent
-- via the canonical owner lemma `Submodule.mem_torsion_iff`, so no domain hypothesis is needed.
/-- An `R`-module is torsion exactly when every element is torsion. -/
theorem isTorsion_iff_forall_mem_torsion :
    IsTorsion R M ↔ ∀ x : M, x ∈ Submodule.torsion R M := by
  simp [Module.IsTorsion]

end Semiring

end

/-! ### Lemma_15_22_2 (from Chap15) -/
universe u v

/-
Domain-style sampling:
- primary domain: torsion theory for modules over commutative rings and its domain specialization;
- sampled owner API:
  `Submodule.torsion`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  `Submodule.QuotientTorsion.torsion_eq_bot`,
  the quotient torsion-free instance on `M ⧸ Submodule.torsion R M`;
- source-facing: the torsion submodule and the torsion-free quotient by it;
- core/canonical: the mathlib owners `Submodule.torsion` and `Module.IsTorsionFree`;
- bridge/view: none.

Primitive data are only the module over the base ring. The torsion-free structure on the quotient by
`Submodule.torsion R M` is derived API already owned upstream, with proposition-level owner
`Module.IsTorsionFree R (M ⧸ Submodule.torsion R M)` and implementation supplied by
`Submodule.QuotientTorsion.instIsTorsionFree`. The public entry here should expose the
proposition-level owner rather than the internal instance name.
-/

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Lemma 15.22.2 (1): the set of torsion elements of an `R`-module `M` is the canonical submodule
`Submodule.torsion R M`; the source's domain hypothesis is redundant for this owner declaration. -/
recall Submodule.torsion

end

section

open Module

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 15.22.2 (2): the quotient of an `R`-module by its torsion submodule is torsion free. -/
#check (inferInstance : IsTorsionFree R (M ⧸ Submodule.torsion R M))

end

/-! ### Lemma_15_22_3 (from Chap15) -/
universe u v

/-
Domain-style sampling:
- primary domain: localization of modules and torsion-freeness over domains;
- sampled owner API:
  `Submodule.torsion`,
  `Submodule.QuotientTorsion.instIsTorsionFree`,
  `IsLocalizedModule.isTorsionFree`,
  the specialized `LocalizedModule` torsion-free instance;
- best owner abstraction: `IsLocalizedModule.isTorsionFree`;
- source-facing layer: the textbook specialization asserting that `LocalizedModule S M` is
  torsion-free over `Localization S`;
- core/canonical layer: `IsLocalizedModule.isTorsionFree`;
- bridge/view layer: specialize that theorem along `LocalizedModule.mkLinearMap S M`.

Primitive data are the base domain `R`, the `R`-module `M`, and the multiplicative set `S`.
Torsion-freeness of the localization is derived API already owned upstream, so this file should
reuse the named owner theorem rather than a parallel local wrapper or anonymous instance search.
-/

section

open Module

variable {R : Type u} [CommRing R] [IsDomain R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M] [IsTorsionFree R M]

/- Lemma 15.22.3: if `M` is a torsion-free module over a domain `R`, then for every
multiplicative set `S ⊆ R` the localized module `LocalizedModule S M` is torsion-free over
`Localization S`. Mathlib owns this through the general localized-module theorem
`IsLocalizedModule.isTorsionFree`, whose specialization to `LocalizedModule` is the source-facing
statement here. -/
#check (IsLocalizedModule.isTorsionFree (LocalizedModule.mkLinearMap S M) S :
  IsTorsionFree (Localization S) (LocalizedModule S M))

end

/-! ### Lemma_15_22_4 (from Chap15) -/
universe u v w

open scoped TensorProduct
open Module

/-
Domain-style sampling:
- primary domain: commutative algebra of torsion-free modules under flat base change;
- sampled owner API:
  `Module.IsTorsionFree`,
  `TensorProduct`,
  `Module.Flat`,
  `LinearEquiv.moduleIsTorsionFree`;
- best owner abstraction: the canonical owner is the tensor-product base change `S ⊗[R] M`,
  with `Module.IsTorsionFree` as the target owner predicate;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma for `R' ⊗[R] M`;
  `core/canonical`: the tensor-product base-change object together with the owner predicate
    `Module.IsTorsionFree`;
  `bridge/view`: no extra bridge owner is needed here, since the source statement already lives on
    the canonical tensor-product base change and no direct downstream file uses an intermediate
    `IsBaseChange` formulation.

Primitive data are the flat algebra `R → S` and the torsion-free `R`-module `M`. The tensor
product `S ⊗[R] M` is already the canonical base-change object, so this file should expose only the
source-facing theorem instead of introducing an additional owner-level wrapper theorem.
-/

section

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
variable [Flat R R'] [AddCommGroup M] [Module R M] [IsTorsionFree R M]

/-- Lemma 15.22.4: if `R → R'` is a flat homomorphism of domains and `M` is a torsion-free
`R`-module, then the base-changed module `R' ⊗[R] M` is a torsion-free `R'`-module. -/
theorem isTorsionFree_baseChange_of_flat :
    IsTorsionFree R' (R' ⊗[R] M) := sorry

end

/-! ### Lemma_15_22_5 (from Chap15) -/
universe u v w x

/-
Domain-style sampling:
- primary domain: torsion-free modules and exact sequences of linear maps;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Function.Exact.linearMap_ker_eq`,
  `isSMulRegular_of_range_eq_ker`,
  `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`;
- best owner abstraction: `isSMulRegular_of_range_eq_ker`;
- source-facing layer: the Stacks lemma that torsion-freeness passes to the middle term of a short
  exact sequence;
- core/canonical layer: scalar-regularity on the middle term of a left exact sequence;
- bridge/view: specialize scalar-regularity to `Module.IsTorsionFree`. The short-complex theorem
  `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact` supplies the
  chapter-level exactness bridge from `ShortExact` to `Function.Exact`, but the owner abstraction
  for this file remains the direct scalar-regularity theorem.

Primitive data for the conclusion are only the injective map `f`, the exactness relation
`Function.Exact f g`, and torsion-freeness on the end terms. The surjectivity part of short
exactness is not used by the canonical owner theorem and should not remain primitive input here.
-/

section

variable {R : Type u} [Ring R]
variable {M : Type v} {M' : Type w} {M'' : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M']
variable [AddCommGroup M''] [Module R M'']

open Module

/-- Lemma 15.22.5: if `M ⟶ M' ⟶ M''` is exact at `M'`, the first map is injective, and the end
terms are torsion free, then `M'` is torsion free. For the source short exact sequence statement,
the surjectivity of the second map is redundant for this conclusion. -/
theorem isTorsionFree_of_exact_of_injective
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    [IsTorsionFree R M] [IsTorsionFree R M''] :
    IsTorsionFree R M' where
  isSMulRegular _r hr :=
    isSMulRegular_of_range_eq_ker hf hfg.linearMap_ker_eq.symm
      hr.isSMulRegular hr.isSMulRegular

end

/-! ### Lemma_15_22_6 (from Chap15) -/
universe u v

/-
Domain-style sampling:
- primary domain: torsion-free modules and localization at maximal ideals;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Module.IsTorsionFree.of_smul_eq_zero`,
  `IsLocalizedModule.isTorsionFree`,
  `Module.eq_zero_of_localization_maximal`,
  `smul_eq_zero_iff_right`;
- best owner abstraction: `Module.IsTorsionFree`;
- source-facing layer: the Stacks lemma detecting torsion-freeness from maximal localizations;
- core/canonical layer: scalar-regularity packaged by `Module.IsTorsionFree`;
- bridge/view layer: the canonical localization maps `LocalizedModule.mkLinearMap`.

Primitive data are only the domain `R`, the module `M`, and the canonical family of localizations
at maximal ideals. Local torsion-freeness is already owner-level derived data, so this file should
reuse the canonical localization and local-detection API directly.
-/

section

open Module
open LocalizedModule (AtPrime mkLinearMap)

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: the forward implication is the canonical localized-module torsion-free instance.
-- Conversely, use the owner constructor `Module.IsTorsionFree.of_smul_eq_zero`. If `r ≠ 0` and
-- `r • x = 0`, then in every maximal localization the image of `x` is killed by the nonzero
-- scalar `algebraMap R (Localization.AtPrime m) r`, hence is zero by local torsion-freeness. The
-- mathlib local-to-global theorem `Module.eq_zero_of_localization_maximal` then gives `x = 0`.
/-- Lemma 15.22.6: an `R`-module over a domain is torsion free if and only if its localization at
every maximal ideal is torsion free. -/
theorem isTorsionFree_iff_localizedModule_atPrime_maximal :
    IsTorsionFree R M ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        IsTorsionFree (Localization.AtPrime m) (AtPrime m M) := by
  constructor
  · intro hM m _
    letI := hM
    simpa using
      (IsLocalizedModule.isTorsionFree (mkLinearMap m.primeCompl M) m.primeCompl :
        IsTorsionFree (Localization.AtPrime m) (AtPrime m M))
  · intro hlocal
    have hzero : ∀ (r : R) (x : M), r • x = 0 → r = 0 ∨ x = 0 := fun r x hx ↦ by
      by_cases hr : r = 0
      · exact Or.inl hr
      · let Mₘ : ∀ (m : Ideal R) [m.IsMaximal], Type (max u v) := fun m _ ↦ AtPrime m M
        let fₘ : ∀ (m : Ideal R) [m.IsMaximal], M →ₗ[R] Mₘ m :=
          fun m _ ↦ mkLinearMap m.primeCompl M
        have hx_zero : x = 0 := eq_zero_of_localization_maximal Mₘ fₘ x fun m _ ↦ by
          letI := hlocal m
          have hmap :
              (algebraMap R (Localization.AtPrime m)) r • mkLinearMap m.primeCompl M x = 0 := by
            simpa using congrArg (mkLinearMap m.primeCompl M) hx
          have hmap_ne_zero : (algebraMap R (Localization.AtPrime m)) r ≠ 0 :=
            IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors
              (Localization.AtPrime m)
              (Ideal.primeCompl_le_nonZeroDivisors m)
              (mem_nonZeroDivisors_iff_ne_zero.mpr hr)
          exact (smul_eq_zero_iff_right hmap_ne_zero).mp hmap
        exact Or.inr hx_zero
    exact Module.IsTorsionFree.of_smul_eq_zero hzero

end

/-! ### Lemma_15_22_7 (from Chap15) -/
universe u v

/-
Domain-style sampling:
- primary domain: finite modules over domains, torsion-freeness, and embeddings into finite free
  modules;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Basis.isTorsionFree`,
  `Function.Injective.moduleIsTorsionFree`,
  `Module.Finite.exists_fin'`,
  `LinearIndependent.iff_fractionRing`;
- best owner abstraction: `Module.IsTorsionFree`, with `Fin n → R` as the canonical finite free
  model used by `Module.Finite.exists_fin'`;
- source-facing layer: the Stacks equivalence between torsion-freeness and embeddability into a
  finite free module;
- core/canonical layer: the torsion-free owner `Module.IsTorsionFree`;
- bridge/view layer: the canonical finite free model `Fin n → R` and injective linear maps
  `M →ₗ[R] (Fin n → R)`.

Primitive data are only the finite `R`-module `M` and the owner predicate
`Module.IsTorsionFree R M`. Mathlib provides the owner abstractions used in the proof, but not this
exact equivalence as a canonical theorem, so the source-facing statement should remain here instead
of being replaced by a less usable existential package around `Module.Free`.
-/

section

open Module

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsDomain R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: if `M` embeds into `Fin n → R`, then it is torsion free because submodules of a
-- torsion-free module are torsion free. Conversely, tensor `M` with the fraction field of `R`,
-- choose a basis of the resulting finite-dimensional vector space, clear denominators on a finite
-- generating set of `M`, and obtain an injective map from `M` into `R^n`.
/-- Lemma 15.22.7: a finite module over a domain is torsion free if and only if it admits an
injective linear map into a finite free module, expressed here in the canonical model
`Fin n → R`. -/
theorem isTorsionFree_iff_exists_injective_to_fin_fun :
    Module.IsTorsionFree R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R), Function.Injective f := sorry

end

/-! ### Lemma_15_22_8 (from Chap15) -/
universe u v

/-
Domain-style sampling:
- primary domain: commutative algebra of finite modules over Noetherian domains, with owner-level
  notions `Module.IsTorsionFree R M`, `associatedPrimes R M`,
  `Module.SerreConditionS R M 1`, and `embeddedAssociatedPrimes R M`;
- sampled owner declarations:
  `isTorsionFree_iff_exists_injective_to_fin_fun`,
  `Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one`,
  `embeddedAssociatedPrimes_eq_empty_iff`,
  `Module.associatedPrimes_subset_support`,
  `minimal_support_iff_minimal_associatedPrimes`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`;
- best owner abstraction: `Module.SerreConditionS R M 1` for the `(S₁)` clause and
  `embeddedAssociatedPrimes R M` for the no-embedded-associated-primes clause;
- primitive data vs derived API: the owner predicates above are primitive/canonical, while the two
  deleted public pairwise equivalence theorems were bridge-level API that added no new owner data.

Source/core/bridge triage:
- `source-facing`: the five-way TFAE from Stacks, whose fourth and fifth clauses still need the
  extra generic-point-in-support conjunct from the source;
- `core/canonical`: `Module.IsTorsionFree`, `associatedPrimes`, `Module.SerreConditionS`,
  `embeddedAssociatedPrimes`;
- `bridge/view`: the source-facing conjunctions pairing the generic-point support clause with the
  canonical owner predicates.
-/

section

open Module

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: combine Lemma `15.22.7` for the equivalence of torsion-freeness with embeddability
-- into a finite free module, Lemma `10.157.2` for `(S_1)` versus absence of embedded associated
-- primes, and the standard implications relating associated primes and support over a domain.
variable [Nontrivial M]

/-- Lemma 15.22.8: for a nonzero finite module over a Noetherian domain, the following are
equivalent: `M` is torsion free, `M` embeds into a finite free module, `(0)` is the only
associated prime of `M`, `(0)` lies in the support of `M` and `M` satisfies LinearRepresentations_Serre_1977's condition
`(S_1)`, and `(0)` lies in the support of `M` and `M` has no embedded associated prime. -/
theorem torsionFree_tfae_associatedPrimes_support_serreS1 :
    List.TFAE
      [ IsTorsionFree R M,
        ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R), Function.Injective f,
        associatedPrimes R M = {⊥},
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ SerreConditionS R M 1,
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ ] := by
  have htors :
      IsTorsionFree R M ↔ associatedPrimes R M = {⊥} := by
    constructor
    · intro htors
      letI := htors
      have hprime_eq_bot : ∀ ⦃p : Ideal R⦄, p ∈ associatedPrimes R M → p = ⊥ := by
        intro p hp
        by_contra hpbot
        exact not_mem_associatedPrimes_of_ne_bot hpbot hp
      have hbot_assoc : (⊥ : Ideal R) ∈ associatedPrimes R M := by
        obtain ⟨p, hp⟩ := associatedPrimes.nonempty R M
        simpa [hprime_eq_bot hp] using hp
      ext p
      constructor
      · intro hp
        simpa [hprime_eq_bot hp]
      · intro hp
        simpa [Set.mem_singleton_iff.mp hp] using hbot_assoc
    · intro hassoc
      rw [Submodule.isTorsionFree_iff_torsion_eq_bot]
      refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
      by_contra hx0
      rw [Submodule.mem_torsion_iff] at hx
      rcases hx with ⟨⟨r, hr0⟩, hrx⟩
      have hr0' : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr0
      have hr_mem : r ∈ ⋃ p ∈ associatedPrimes R M, p := by
        rw [biUnion_associatedPrimes_eq_zero_divisors R M]
        exact ⟨x, hx0, hrx⟩
      rw [Set.mem_iUnion] at hr_mem
      obtain ⟨p, hp_mem⟩ := hr_mem
      rw [Set.mem_iUnion] at hp_mem
      obtain ⟨hp, hrp⟩ := hp_mem
      have hpbot : p = ⊥ := by
        simpa [hassoc] using hp
      exact hr0' (by simpa [hpbot] using hrp)
  have hassoc :
      associatedPrimes R M = {⊥} ↔
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ := by
    constructor
    · intro hassoc
      refine ⟨?_, ?_⟩
      · exact associatedPrimes_subset_support <| by
          simpa [hassoc]
      · exact (embeddedAssociatedPrimes_eq_empty_iff R M).2 <|
          fun p hp ↦ by
            refine ⟨hp, ?_⟩
            intro q hq hqp
            have hpbot : p = ⊥ := by
              simpa [hassoc] using hp
            have hqbot : q = ⊥ := by
              simpa [hassoc] using hq
            simpa [hpbot, hqbot]
    · rintro ⟨hbot_support, hembedded⟩
      have hminimal_assoc := (embeddedAssociatedPrimes_eq_empty_iff R M).mp hembedded
      have hbot_assoc : Minimal (· ∈ associatedPrimes R M) (⊥ : Ideal R) := by
        have hminimal_support_bot : Minimal (· ∈ support R M) (⊥ : PrimeSpectrum R) := by
          refine ⟨hbot_support, ?_⟩
          intro q hq hqbot
          exact bot_le
        exact (minimal_support_iff_minimal_associatedPrimes (⊥ : PrimeSpectrum R)).1
          hminimal_support_bot
      ext p
      constructor
      · intro hp
        have hp_min := hminimal_assoc p hp
        have hpbot : p = ⊥ := by
          exact le_antisymm (hp_min.2 hbot_assoc.1 bot_le) bot_le
        simpa [hpbot]
      · intro hp
        simpa [Set.mem_singleton_iff.mp hp] using hbot_assoc.1
  have hserre :
      (⊥ : PrimeSpectrum R) ∈ support R M ∧ SerreConditionS R M 1 ↔
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ := by
    constructor
    · rintro ⟨hsupport, hserre⟩
      exact ⟨hsupport, embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one.2 hserre⟩
    · rintro ⟨hsupport, hembedded⟩
      exact ⟨hsupport, embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one.1 hembedded⟩
  refine List.tfae_of_forall (IsTorsionFree R M) _ ?_
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | ha
  · rfl
  rcases ha with rfl | ha
  · exact (isTorsionFree_iff_exists_injective_to_fin_fun).symm
  rcases ha with rfl | ha
  · exact htors.symm
  rcases ha with rfl | ha
  · calc
      (⊥ : PrimeSpectrum R) ∈ support R M ∧ SerreConditionS R M 1 ↔
          (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ :=
        hserre
      _ ↔ associatedPrimes R M = {⊥} :=
        hassoc.symm
      _ ↔ IsTorsionFree R M :=
        htors.symm
  rcases ha with rfl | ha
  · calc
      (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ ↔
          associatedPrimes R M = {⊥} :=
        hassoc.symm
      _ ↔ IsTorsionFree R M :=
        htors.symm
  · simpa using ha

end

/-! ### Lemma_15_22_9 (from Chap15) -/
universe u v

/-
Domain-style sampling:
- primary domain: flatness and torsion theory for modules over commutative domains;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Submodule.torsion`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  `Module.Flat.torsion_eq_bot`;
- best owner abstraction: the proposition-level owner is `Module.IsTorsionFree R M`; the torsion
  submodule `Submodule.torsion R M` is the primitive data owner, and flatness supplies the derived
  vanishing statement `Module.Flat.torsion_eq_bot`;
- source/core/bridge triage:
  `source-facing`: the textbook implication that flat modules over a domain are torsion free;
  `core/canonical`: `Submodule.torsion` together with the owner property `Module.IsTorsionFree`;
  `bridge/view`: the present lemma, converting the canonical flatness hypothesis into the
  canonical torsion-free conclusion.

Primitive data here are only the ambient ring/module and the flatness hypothesis. The torsion
submodule and torsion-free predicate are already owned upstream, so this file should not introduce a
parallel wrapper or entrywise reformulation: it should expose the source-facing implication through
the canonical bridge from `Module.Flat.torsion_eq_bot` to
`Submodule.isTorsionFree_iff_torsion_eq_bot`.
-/

section

open Module

variable {R : Type u} {M : Type v} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

/-- Lemma 15.22.9: over a domain, every flat `R`-module is torsion free. -/
-- Proof sketch: use `Submodule.isTorsionFree_iff_torsion_eq_bot` to reduce torsion-freeness to the
-- vanishing of the torsion submodule, then apply `Module.Flat.torsion_eq_bot`.
theorem flat_isTorsionFree [Flat R M] : IsTorsionFree R M :=
  Submodule.isTorsionFree_iff_torsion_eq_bot.2 Module.Flat.torsion_eq_bot

end

/-! ### Lemma_15_22_10 (from Chap15) -/
universe u v

/-
Domain-style sampling:
- primary domain: flatness and torsion theory for modules over valuation rings;
- sampled owner API:
  `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  the instance `ValuationRing A → IsBezout A`;
- best owner abstraction: the canonical owners are `Module.Flat` and `Module.IsTorsionFree`;
- primitive data: the ring `A`, the module `M`, and the valuation-ring structure on `A`;
- derived API: the induced `IsBezout A` instance and the torsion-vanishing bridge
  `Submodule.isTorsionFree_iff_torsion_eq_bot`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma specialized to valuation rings;
  `core/canonical`: the Bezout-domain flatness criterion and the torsion-free owner predicate;
  `bridge/view`: this theorem, which specializes the canonical Bezout criterion to valuation
  rings.

No extra primitive data should be introduced here: valuation rings already carry the needed
`IsBezout` instance upstream, so the file should reuse the owner theorem directly rather than keep
any parallel local flatness-versus-torsion wrapper.
-/

section

open Module

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]

-- Proof sketch: specialize the canonical Bezout-domain criterion
-- `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` along the valuation-ring instance
-- `IsBezout A`, then rewrite the source-facing torsion-free owner with
-- `Submodule.isTorsionFree_iff_torsion_eq_bot`.
/-- Lemma 15.22.10: for a valuation ring `A`, an `A`-module `M` is flat if and only if `M` is torsion free. -/
theorem flat_iff_isTorsionFree_of_valuationRing :
    Flat A M ↔ IsTorsionFree A M := by
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot, Flat.flat_iff_torsion_eq_bot_of_isBezout]

end

/-! ### Lemma_15_22_11 (from Chap15) -/
universe u v

open Module

/-
Domain-style sampling:
- primary domain: torsion-free, flat, finite locally free, and free modules over Dedekind domains
  and principal ideal domains;
- sampled owner declarations:
  `IsDedekindDomain.flat_iff_torsion_eq_bot`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  `Module.finiteLocallyFree_of_finitePresentation_of_flat`,
  `Module.free_of_finite_type_torsion_free'`;
- best owner abstraction: the public statements should be organized around the owner predicates
  `IsTorsionFree`, `FiniteLocallyFree`, and `Module.Free`, with vanishing torsion and finite
  presentation used only as bridge data;
- primitive data: the ring, the module, and for parts `(2)` and `(3)` the finiteness hypothesis;
- derived API: flatness over a Dedekind domain, finite local freeness via
  `Module.finiteLocallyFree_of_finitePresentation_of_flat`, and freeness over a PID via the canonical owner
  `Module.free_of_finite_type_torsion_free'`.

Source/core/bridge triage:
- part `(1)` is `bridge/view`, translating the canonical Dedekind-domain flatness criterion into
  the source-facing torsion-free owner;
- part `(2)` is `bridge/view`, translating the finite torsion-free hypothesis into the chapter
  owner `FiniteLocallyFree`;
- part `(3)` is `core/canonical`, since the textbook statement already coincides with an existing
  mathlib owner and should be recalled directly.
-/

section

variable {A : Type u} [CommRing A] [IsDedekindDomain A]
variable {M : Type v} [AddCommGroup M] [Module A M]

-- Proof sketch: rewrite flatness over a Dedekind domain using the canonical mathlib theorem
-- `IsDedekindDomain.flat_iff_torsion_eq_bot`, then identify vanishing torsion with
-- `IsTorsionFree A M` via `Submodule.isTorsionFree_iff_torsion_eq_bot`.
/-- Lemma 15.22.11 (1): over a Dedekind domain `A` (hence in particular over a discrete valuation
ring or a PID), an `A`-module is flat if and only if it is torsion free. -/
theorem flat_iff_isTorsionFree_of_isDedekindDomain :
    Flat A M ↔ IsTorsionFree A M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]

-- Proof sketch: a finite module over a Dedekind domain is finitely presented because Dedekind
-- domains are Noetherian, and a torsion-free module is flat by the canonical Dedekind-domain
-- owner theorem. The chapter owner bridge
-- `Module.finiteLocallyFree_of_finitePresentation_of_flat` then upgrades the finitely presented
-- flat module directly to `FiniteLocallyFree`.
/-- Lemma 15.22.11 (2): a finite torsion-free module over a Dedekind domain is finite locally
free. -/
theorem finiteLocallyFree_of_finite_of_isTorsionFree_of_isDedekindDomain
    [Module.Finite A M] [IsTorsionFree A M] :
    FiniteLocallyFree A M := by
  letI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  exact finiteLocallyFree_of_finitePresentation_of_flat

end

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable [IsTorsionFree A M]

/- Lemma 15.22.11 (3): a finite torsion-free module over a principal ideal domain is free.
This is exactly the canonical mathlib owner `Module.free_of_finite_type_torsion_free'`. -/
recall free_of_finite_type_torsion_free'

end

/-! ### Lemma_15_22_12 (from Chap15) -/
universe u v w

/-
Domain-style sampling:
- primary domain: torsion-free semimodules and semilinear-map modules;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Function.Injective.moduleIsTorsionFree`,
  `LinearMap.instIsTorsionFree`,
  `Module.IsTorsionFree.of_smul_eq_zero`;
- best owner abstraction: the proposition-level owner `Module.IsTorsionFree`, with the linear-map
  module instance `LinearMap.instIsTorsionFree` as the canonical owner declaration for this item;
- source/core/bridge triage:
  `source-facing`: the textbook assertion that `Hom_R(M, N)` is torsion free when `N` is;
  `core/canonical`: `LinearMap.instIsTorsionFree`;
  `bridge/view`: none needed, since the source statement already coincides with the canonical owner
  instance.

Primitive data are the semiring `R`, the source and target `R`-semimodules, and the
torsion-freeness instance on `N`. The torsion-free structure on `M →ₗ[R] N` is derived API owned
upstream by `LinearMap.instIsTorsionFree`, so this file should recall that instance directly at the
weaker canonical semiring/additive-monoid level instead of using an anonymous `inferInstance`
check.
-/

section

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N] [Module.IsTorsionFree R N]

/- Lemma 15.22.12: if `N` is a torsion-free `R`-module over a domain `R`, then the `R`-module
of homomorphisms `M →ₗ[R] N` is torsion free. Mathlib's owner instance is stronger: it already
holds for `R` a semiring and `M`, `N` additive commutative monoids. -/
recall LinearMap.instIsTorsionFree

end
