import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u v

/- Domain triage:
- primary domain: separable polynomials over a field of characteristic `p`, viewed through the
  Frobenius / purely inseparable interface;
- sampled owner declarations:
  `Polynomial.map`,
  `frobenius`,
  `X_pow_sub_C_irreducible_of_prime`,
  `minpoly.natSepDegree_eq_one_iff_pow_mem`,
  `Irreducible.hasSeparableContraction`,
  `Polynomial.map_frobenius_expand`;
- owner abstraction in this file: the canonical Frobenius-image condition
  `P ∈ Set.range (Polynomial.map (frobenius K p))`, whose primitive data are a separable polynomial
  `P` and a root `α`;
- derived API: the source-facing coefficientwise `p`th-power hypothesis, together with any chosen
  preimage polynomial `Q`, the resulting carrier-level Frobenius-image conclusion
  `α ∈ Set.range (fun β : L ↦ β ^ p)`, and the minimal-polynomial specialization for `minpoly K α`.

Layer triage:
- `source-facing`: `exists_pth_root_of_aeval_zero_of_separable_of_coeff_pth_powers`;
- `bridge/view`: `Polynomial.mem_map_frobenius_range_iff_coeff_eq_pow`, translating the source
  coefficient condition into the owner-level Frobenius-image condition;
- `core/canonical`: `mem_range_pow_of_aeval_zero_of_separable_of_mem_map_frobenius_range`;
- `bridge/view`: `exists_pth_root_of_aeval_zero_of_separable_of_mem_map_frobenius_range`,
  unpacking the canonical Frobenius-image conclusion into the source existential conclusion;
- `bridge/view`: `exists_pth_root_of_minpoly_coeff_pth_powers`, obtained by specializing the
  owner theorem to `P := minpoly K α`.
-/

namespace Polynomial

section Coefficients

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p] {P : R[X]}

/-- A polynomial has coefficientwise `p`th-power coefficients iff it lies in the image of
`Polynomial.map (frobenius R p)`. This packages the coordinatewise source condition into the
canonical owner-level Frobenius map on coefficients. -/
theorem mem_map_frobenius_range_iff_coeff_eq_pow :
    P ∈ Set.range (Polynomial.map (frobenius R p)) ↔ ∀ n : ℕ, ∃ b : R, P.coeff n = b ^ p := by
  rw [Set.mem_range]
  constructor
  · rintro ⟨Q, rfl⟩ n
    refine ⟨Q.coeff n, ?_⟩
    simp [frobenius_def]
  · intro hcoeff
    classical
    let Q : R[X] := ∑ n ∈ P.support, monomial n (Classical.choose (hcoeff n))
    refine ⟨Q, ?_⟩
    ext n
    rw [coeff_map]
    by_cases hn : n ∈ P.support
    · have hchosen : P.coeff n = Classical.choose (hcoeff n) ^ p :=
        Classical.choose_spec (hcoeff n)
      have hQn : Q.coeff n = Classical.choose (hcoeff n) := by
        unfold Q
        rw [finset_sum_coeff, Finset.sum_eq_single_of_mem n hn]
        · simp
        · intro b hb hbn
          simp [coeff_monomial, hbn]
      rw [hQn]
      simpa [frobenius_def] using hchosen.symm
    · have hPn : P.coeff n = 0 := by
        by_contra hPn
        exact hn (mem_support_iff.2 hPn)
      have hQn : Q.coeff n = 0 := by
        unfold Q
        rw [finset_sum_coeff]
        refine Finset.sum_eq_zero ?_
        intro b hb
        by_cases hbn : b = n
        · exact (hn (hbn ▸ hb)).elim
        · simp [coeff_monomial, hbn]
      rw [hQn, map_zero, hPn]

end Coefficients

end Polynomial

section

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

-- Proof sketch: choose `Q` with `Q.map (frobenius K p) = P`. Then any `p`th root `β` of `α` in
-- an algebraic closure is a root of `Q`. If `α` were not a `p`th power in `L`, Lemma `9.14.2`
-- would make `X ^ p - C α` irreducible over `L`; since it shares the root `β` with `Q`, it would
-- divide `Q`, contradicting separability after transporting along `Polynomial.separable_map`.
/-- Canonical owner form of Lemma 9.28.2: if `α` is a root of a separable polynomial `P` over a
field `K` of characteristic `p`, and `P` lies in the Frobenius image of `Polynomial.map`, then
`α` lies in the carrier-level Frobenius image on `L`. -/
theorem mem_range_pow_of_aeval_zero_of_separable_of_mem_map_frobenius_range
    {α : L} {P : K[X]} (hPsep : P.Separable) (hPα : aeval α P = 0)
    (hP : P ∈ Set.range (Polynomial.map (frobenius K p))) :
    α ∈ Set.range (fun β : L ↦ β ^ p) := by
  obtain ⟨Q, hmap⟩ := hP
  have hQsep : Q.Separable := (Polynomial.separable_map (frobenius K p)).1 (hmap ▸ hPsep)
  by_contra hα
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  let g : L[X] := X ^ p - C α
  have hgirr : Irreducible g := by
    refine X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) ?_
    simpa [Set.mem_range, frobenius_def, g] using hα
  letI : Fact (Irreducible g) := ⟨hgirr⟩
  let M := AdjoinRoot g
  letI : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  haveI : ExpChar M p := expChar_of_injective_algebraMap (algebraMap K M).injective p
  let β : M := AdjoinRoot.root g
  have hβg_eval : g.eval₂ (AdjoinRoot.of g) β = 0 := by
    dsimp [β]
    exact AdjoinRoot.eval₂_root g
  have hβg : aeval β g = 0 := by
    simpa [Polynomial.aeval_def, M] using hβg_eval
  have hβpow : β ^ p = algebraMap L M α := by
    simpa [g, M, β] using root_X_pow_sub_C_pow p α
  have hPαM : aeval (algebraMap L M α) P = 0 := by
    have hcomp :
        (algebraMap K M).comp (RingHom.id K) = (algebraMap L M).comp (algebraMap K L) := by
      ext x
      rfl
    have hmapP : algebraMap L M (aeval α P) = aeval (algebraMap L M α) P := by
      simpa using P.map_aeval_eq_aeval_map hcomp α
    rw [← hmapP]
    simpa using congrArg (algebraMap L M) hPα
  have hβQfrobenius : frobenius M p (aeval β Q) = 0 := by
    have hcomp :
        (algebraMap K M).comp (frobenius K p) = (frobenius M p).comp (algebraMap K M) := by
      ext x
      simp [frobenius_def]
    calc
      frobenius M p (aeval β Q) = aeval (frobenius M p β) (Q.map (frobenius K p)) := by
        simpa [M] using Q.map_aeval_eq_aeval_map hcomp β
      _ = aeval (algebraMap L M α) P := by simp [frobenius_def, hβpow, hmap]
      _ = 0 := hPαM
  have hβQ : aeval β Q = 0 := by
    exact (pow_eq_zero_iff (Nat.Prime.ne_zero (Fact.out : p.Prime))).1 <|
      by simpa [frobenius_def] using hβQfrobenius
  have hβQ' : aeval β (Q.map (algebraMap K L)) = 0 := by
    have hcomp : (algebraMap L M).comp (algebraMap K L) = algebraMap K M := by
      ext x
      rfl
    rw [← Q.aeval_eq_aeval_map hcomp β]
    exact hβQ
  have hgdvd : g ∣ Q.map (algebraMap K L) := by
    rw [minpoly.eq_of_irreducible_of_monic hgirr hβg
      (monic_X_pow_sub_C α (Nat.Prime.ne_zero (Fact.out : p.Prime)))]
    exact minpoly.dvd L β hβQ'
  have hgsep : g.Separable := by
    exact Polynomial.Separable.of_dvd ((Polynomial.separable_map (algebraMap K L)).2 hQsep) hgdvd
  exact ((Polynomial.separable_iff_derivative_ne_zero hgirr).1 hgsep) <| by
    simp [g, Polynomial.derivative_pow]

/-- Source-facing unpacking of the canonical Frobenius-image conclusion: under the hypotheses of
Lemma 9.28.2, the root `α` admits a `p`th root in `L`. -/
theorem exists_pth_root_of_aeval_zero_of_separable_of_mem_map_frobenius_range
    {α : L} {P : K[X]} (hPsep : P.Separable) (hPα : aeval α P = 0)
    (hP : P ∈ Set.range (Polynomial.map (frobenius K p))) :
    ∃ β : L, β ^ p = α := by
  simpa [Set.mem_range] using
    mem_range_pow_of_aeval_zero_of_separable_of_mem_map_frobenius_range hPsep hPα hP

-- Proof sketch: convert the coefficientwise source hypothesis into the canonical Frobenius-image
-- hypothesis using `Polynomial.mem_map_frobenius_range_iff_coeff_eq_pow`, then apply the
-- owner-level theorem above.
/-- Lemma 9.28.2: if `α` is a root of a separable polynomial `P` over a field `K` of
characteristic `p`, and every coefficient of `P` is a `p`th power in `K`, then `α` is a `p`th
power in `L`. This source-facing form is derived from the canonical Frobenius-image owner theorem
`mem_range_pow_of_aeval_zero_of_separable_of_mem_map_frobenius_range`. -/
theorem exists_pth_root_of_aeval_zero_of_separable_of_coeff_pth_powers
    {α : L} {P : K[X]} (hPsep : P.Separable) (hPα : aeval α P = 0)
    (hcoeff : ∀ n : ℕ, ∃ b : K, P.coeff n = b ^ p) :
    ∃ β : L, β ^ p = α := by
  have hmap : P ∈ Set.range (Polynomial.map (frobenius K p)) :=
    (Polynomial.mem_map_frobenius_range_iff_coeff_eq_pow).2 hcoeff
  exact exists_pth_root_of_aeval_zero_of_separable_of_mem_map_frobenius_range hPsep hPα hmap

-- Proof sketch: specialize the source-facing polynomial theorem to `P := minpoly K α`. The
-- hypotheses `hα` and `minpoly.aeval K α` supply the separability and root conditions.
/-- Companion specialization: if every coefficient of the minimal polynomial of `α` over `K` is a
`p`th power in `K`, then `α` is a `p`th power in `L`. -/
theorem exists_pth_root_of_minpoly_coeff_pth_powers {α : L} (hα : IsSeparable K α)
    (hcoeff : ∀ n : ℕ, ∃ b : K, (minpoly K α).coeff n = b ^ p) :
    ∃ β : L, β ^ p = α := by
  exact exists_pth_root_of_aeval_zero_of_separable_of_coeff_pth_powers hα (minpoly.aeval K α)
    hcoeff

end
