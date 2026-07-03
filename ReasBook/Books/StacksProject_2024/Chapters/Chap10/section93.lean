import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_93_1 (from Chap10) -/
universe u v

namespace Module

/-
Source/core/bridge triage:
* source-facing: Lemma `10.93.1`, the projectivity criterion for countably generated flat
  Mittag-Leffler modules.
* core/canonical owners: `Module.CountablyGenerated` from `Definition_10_84_1` and
  `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: the local finite-to-countably-generated theorem below.
-/
section

variable (R : Type u) (M : Type v)
variable [Ring R] [AddCommGroup M] [Module R M]

/-- A finite module is countably generated. -/
theorem countablyGenerated_of_finite [Module.Finite R M] :
    CountablyGenerated R M := sorry

end

section

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [Flat R M] [MittagLeffler R M]

-- Proof sketch: apply Lazard's theorem to write `M` as a filtered colimit of finite free modules,
-- use the countable-generation hypothesis and the Mittag-Leffler condition to replace this by a
-- countable directed subsystem, and then apply the exactness of inverse limits for countable
-- Mittag-Leffler systems to show that `Hom_R(M, -)` preserves short exact sequences.
/-- Lemma 10.93.1: if an `R`-module `M` is flat, Mittag-Leffler, and countably generated, then
`M` is projective. -/
theorem projective_of_flat_of_mittagLeffler_of_countablyGenerated
    (hcg : CountablyGenerated R M) :
    Projective R M := sorry

end

end Module

/-! ### Remark_10_93_2 (from Chap10) -/
namespace Module

open scoped PowerSeries

/-
Domain triage:
- `source-facing`: the coefficientwise `p`-adic divisibility-tail condition on `ℤ⟦X⟧` and
  the resulting submodule singled out in the remark;
- `core/canonical`: the chapter owner predicates `Module.Flat`, `Module.MittagLeffler`, and
  `Module.Projective`;
- `bridge/view`: the nonfree divisible-tail submodule obstructing projectivity of `ℤ⟦X⟧`.
Sampled owner-level declarations in this domain:
- `Module.MittagLeffler` from `Definition_10_88_7`;
- `Module.noetherian_pi_flat_and_mittagLeffler` from `Lemma_10_91_3`;
- `Module.noetherian_mvPowerSeries_flat_and_mittagLeffler` from `Lemma_10_91_4`;
- `Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated` from
  `Theorem_10_93_3`.
Primitive data are exactly `HasPAdicallyDivisibleTail` and the induced `Submodule`; the flat,
Mittag-Leffler, and projective clauses are derived API and should reuse the chapter owners rather
than a parallel local class. -/

/-- A formal power series over `ℤ` has an eventually `p`-adically divisible tail if, for every
integer `m`, only finitely many coefficients fail to be divisible by `p^(m + 1)`. This is the
same positive-exponent condition from the remark, reindexed to avoid a redundant positivity
guard. -/
def HasPAdicallyDivisibleTail (p : ℕ) (f : ℤ⟦X⟧) : Prop :=
  ∀ m : ℕ, Set.Finite {i : ℕ | ¬ ((p : ℤ) ^ (m + 1) ∣ PowerSeries.coeff i f)}

/-- Unfolding `HasPAdicallyDivisibleTail` gives the coefficientwise eventual divisibility condition
used in the remark, with the positive exponent written as `m + 1`. -/
theorem hasPAdicallyDivisibleTail_iff (p : ℕ) (f : ℤ⟦X⟧) :
    HasPAdicallyDivisibleTail p f ↔
      ∀ m : ℕ, Set.Finite {i : ℕ | ¬ ((p : ℤ) ^ (m + 1) ∣ PowerSeries.coeff i f)} :=
  Iff.rfl

-- Proof sketch: every coefficient of the zero series is `0`, so it is divisible by every power of
-- `p`; hence the exceptional set is empty for each exponent `m + 1`.
/-- The zero power series has an eventually `p`-adically divisible tail. -/
theorem hasPAdicallyDivisibleTail_zero (p : ℕ) :
    HasPAdicallyDivisibleTail p (0 : ℤ⟦X⟧) := sorry

-- Proof sketch: for each fixed `m`, the coefficients of `f + g` can fail to be divisible by
-- `p^(m + 1)`
-- only where the corresponding coefficient of `f` or of `g` already fails, so the exceptional set
-- is contained in the union of two finite sets.
/-- The eventually `p`-adically divisible-tail condition is closed under addition. -/
theorem hasPAdicallyDivisibleTail_add (p : ℕ) {f g : ℤ⟦X⟧}
    (hf : HasPAdicallyDivisibleTail p f) (hg : HasPAdicallyDivisibleTail p g) :
    HasPAdicallyDivisibleTail p (f + g) := sorry

-- Proof sketch: multiplying all coefficients by an integer scalar preserves divisibility by each
-- fixed power `p^(m + 1)`, so no new infinite exceptional set can appear.
/-- The eventually `p`-adically divisible-tail condition is closed under scalar multiplication. -/
theorem hasPAdicallyDivisibleTail_smul (p : ℕ) (n : ℤ) {f : ℤ⟦X⟧}
    (hf : HasPAdicallyDivisibleTail p f) :
    HasPAdicallyDivisibleTail p (n • f) := sorry

/-- The submodule of `ℤ[[x]]` whose coefficients are eventually divisible by every power of `p`. -/
def pAdicallyDivisibleTailSubmodule (p : ℕ) : Submodule ℤ ℤ⟦X⟧ where
  carrier := {f | HasPAdicallyDivisibleTail p f}
  zero_mem' := hasPAdicallyDivisibleTail_zero p
  add_mem' := fun hf hg ↦ hasPAdicallyDivisibleTail_add p hf hg
  smul_mem' := fun n _ hf ↦ hasPAdicallyDivisibleTail_smul p n hf

/-- Membership in `pAdicallyDivisibleTailSubmodule p` is exactly the eventual divisibility
condition on coefficients. -/
theorem mem_pAdicallyDivisibleTailSubmodule_iff (p : ℕ) (f : ℤ⟦X⟧) :
    f ∈ pAdicallyDivisibleTailSubmodule p ↔ HasPAdicallyDivisibleTail p f :=
  Iff.rfl

-- Proof sketch: the remark shows that `pAdicallyDivisibleTailSubmodule p` is uncountable, while
-- the residue classes of the monomials `x^i` span its quotient modulo `p`. A free abelian group of
-- uncountable rank would have uncountable dimension after reduction mod `p`, giving a
-- contradiction.
/-- For a prime `p`, the divisible-tail submodule from the remark is not free as an abelian
group. -/
theorem pAdicallyDivisibleTailSubmodule_not_free {p : ℕ} (hp : Nat.Prime p) :
    ¬ Module.Free ℤ ↥(pAdicallyDivisibleTailSubmodule p) := sorry

-- Proof sketch: identify `ℤ[[x]]` with the one-variable case of the formal power-series module
-- covered by the owner theorem `noetherian_pi_flat_and_mittagLeffler`.
/-- The `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is flat. -/
instance integerPowerSeries_flat : Module.Flat ℤ ℤ⟦X⟧ := by
  simpa [PowerSeries] using
    (noetherian_pi_flat_and_mittagLeffler :
      Module.Flat ℤ ((Unit →₀ ℕ) → ℤ) ∧ MittagLeffler ℤ ((Unit →₀ ℕ) → ℤ)).1

-- Proof sketch: apply the same owner theorem `noetherian_pi_flat_and_mittagLeffler` to the
-- coefficient module presentation of `ℤ⟦X⟧`.
/-- The `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is Mittag-Leffler. -/
instance integerPowerSeries_mittagLeffler : MittagLeffler ℤ ℤ⟦X⟧ := by
  simpa [PowerSeries] using
    (noetherian_pi_flat_and_mittagLeffler :
      Module.Flat ℤ ((Unit →₀ ℕ) → ℤ) ∧ MittagLeffler ℤ ((Unit →₀ ℕ) → ℤ)).2

-- Proof sketch: if `ℤ⟦X⟧` were projective, then as an abelian group it would be free, and
-- every submodule would also be free. For any prime `p`, the submodule
-- `pAdicallyDivisibleTailSubmodule p` is not free by the preceding theorem, contradiction.
/-- Remark 10.93.2: the `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is flat and Mittag-Leffler but
not projective. This is the source-facing counterexample showing that Lemma 10.93.1 fails without
the countable-generation assumption. -/
theorem integerPowerSeries_flat_mittagLeffler_and_not_projective :
    Module.Flat ℤ ℤ⟦X⟧ ∧ MittagLeffler ℤ ℤ⟦X⟧ ∧ ¬ Module.Projective ℤ ℤ⟦X⟧ := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  sorry

/-- The `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is not projective. -/
theorem integerPowerSeries_not_projective :
    ¬ Module.Projective ℤ ℤ⟦X⟧ :=
  integerPowerSeries_flat_mittagLeffler_and_not_projective.2.2

end Module

/-! ### Theorem_10_93_3 (from Chap10) -/
universe u v

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: for the forward implication, projective modules are flat, Theorem `10.84.5`
-- gives a direct-sum decomposition by countably generated submodules, and both flatness and the
-- Mittag-Leffler property pass to direct summands of free modules. For the converse, combine the
-- direct-sum decomposition with stability of flatness and Mittag-Leffler under direct summands,
-- then apply Lemma `10.93.1` to each countably generated summand and conclude that a direct sum of
-- projective modules is projective.
/-- Theorem 10.93.3: an `R`-module `M` is projective if and only if it is flat, Mittag-Leffler,
and a direct sum of countably generated `R`-submodules. -/
theorem projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated :
    Projective R M ↔
      Flat R M ∧ MittagLeffler R M ∧ IsDirectSumOfCountablyGenerated R M := sorry

end

end Module

/-! ### Lemma_10_93_4 (from Chap10) -/
universe u v

namespace LinearMap

open CategoryTheory
open CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {M N : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

-- Proof sketch: attach to `f` the short exact sequence `0 → M → N → N ⧸ range f → 0`. Universal
-- injectivity makes this short complex universally exact, so Lemma `10.82.7` gives flatness of
-- `M` from flatness of `N`, and Lemma `10.89.7` gives the Mittag-Leffler property of `M` from that
-- of `N`. Then apply Theorem `10.93.3` using the assumed decomposition of `M` as a direct sum of
-- countably generated submodules.
/-- Lemma 10.93.4: if `f : M →ₗ[R] N` is universally injective, `M` is a direct sum of countably
generated `R`-modules, and `N` is flat and Mittag-Leffler, then `M` is projective. -/
theorem projective_of_universallyInjective_of_flat_of_mittagLeffler_of_isDirectSumOfCountablyGenerated
    (f : M →ₗ[R] N) (hf : UniversallyInjective.{u, v, v, v} f)
    [Module.Flat R N] [Module.MittagLeffler R N]
    (hM : Module.IsDirectSumOfCountablyGenerated R M) :
    Module.Projective R M := by
  have hf_inj : Function.Injective f := by
    have hquot : Function.Injective (f.quotientMapByIdeal (⊥ : Ideal R)) :=
      (universallyInjective_iff_injective_mod_finite_ideal f).1 hf ⊥
        (by simpa using (Submodule.fg_bot : (⊥ : Ideal R).FG))
    intro x y hxy
    have hxyQ :
        (((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ x) =
          (((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ y) := by
      apply hquot
      simp [LinearMap.quotientMapByIdeal, hxy]
    have hmem : x - y ∈ ((⊥ : Ideal R) • (⊤ : Submodule R M) : Submodule R M) :=
      (Submodule.Quotient.eq (((⊥ : Ideal R) • (⊤ : Submodule R M) : Submodule R M))).mp hxyQ
    simpa [sub_eq_zero] using hmem
  let S : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom (LinearMap.range f).mkQ)
      (by
        ext x
        simp)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (by simpa [S] using LinearMap.exact_map_mkQ_range f)
    hf_inj (Submodule.mkQ_surjective _)
  have hU : UniversallyExact S := ⟨hS, by simpa [S] using hf⟩
  letI : Module.Flat R M := UniversallyExact.flat_X₁ hU
  letI : Module.MittagLeffler R M := UniversallyExact.mittagLeffler_X₁ hU
  exact
    Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated.2
      ⟨inferInstance, inferInstance, hM⟩

end

end LinearMap

/-! ### Lemma_10_93_5 (from Chap10) -/
universe u v

namespace LinearMap

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
- `source-facing`: this Stacks lemma specializes the projectivity criterion to maps into
  `MvPowerSeries (Fin n) R`;
- `core/canonical`: `LinearMap
  .projective_of_universallyInjective_of_flat_of_mittagLeffler_of_isDirectSumOfCountablyGenerated`
  is the owner theorem, with `Module.Projective` as the ambient owner predicate;
- `bridge/view`: `Module.noetherian_mvPowerSeries_flat_and_mittagLeffler` provides the derived flat
  and Mittag-Leffler structure on the target module.
Primitive data are the universally injective map `f` and the direct-sum hypothesis on `M`; the
flat and Mittag-Leffler facts for the codomain are derived API and should not be repackaged
locally. -/

-- Proof sketch: install the canonical flat and Mittag-Leffler instances for
-- `MvPowerSeries (Fin n) R` from Lemma `10.91.4`, then apply the owner theorem `10.93.4`.
/-- Lemma 10.93.5: if `M` is a direct sum of countably generated `R`-modules and admits a
universally injective `R`-linear map into the formal power series ring
`MvPowerSeries (Fin n) R`, then `M` is projective. -/
theorem projective_of_universallyInjective_to_mvPowerSeries_of_isDirectSumOfCountablyGenerated
    (n : ℕ) (f : M →ₗ[R] MvPowerSeries (Fin n) R) (hf : UniversallyInjective f)
    (hM : Module.IsDirectSumOfCountablyGenerated R M) :
    Module.Projective R M := by
  sorry

end

end LinearMap
