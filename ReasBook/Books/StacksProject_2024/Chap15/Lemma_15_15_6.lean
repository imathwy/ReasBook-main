import Mathlib
import StacksProject_2024.Chap10.Lemma_10_72_2
import StacksProject_2024.Chap10.Proposition_10_102_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise
open RingTheory.Sequence

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

namespace Ideal

/-- In a Noetherian local ring, the length-`1` source-style condition for `I` is equivalent to the
owner depth inequality `1 ≤ I.depth R`. -/
theorem eq_top_or_exists_isRegular_iff_one_le_depth (I : Ideal R) :
    (I = ⊤ ∨ ∃ x ∈ I, IsRegular x) ↔ (1 : WithTop ℕ) ≤ I.depth R := by
  constructor
  · rintro (hI | ⟨x, hxI, hxreg⟩)
    · exact (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mp <| Or.inl hI
    · by_cases hxunit : IsUnit x
      · exact
          (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mp <|
            Or.inl (I.eq_top_of_isUnit_mem hxI hxunit)
      · refine (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mp ?_
        refine Or.inr ⟨[x], ?_, ?_, by simp⟩
        · have hxsmul : IsSMulRegular R x := hxreg.left.isSMulRegular
          have hxsmul_ne_top : x • (⊤ : Ideal R) ≠ ⊤ := by
            intro htop
            apply hxunit
            have hspanTop : Ideal.span ({x} : Set R) = ⊤ := by
              calc
                Ideal.span ({x} : Set R) = Ideal.span ({x} : Set R) • (⊤ : Ideal R) := by simp
                _ = x • (⊤ : Ideal R) := by rw [Submodule.ideal_span_singleton_smul]
                _ = ⊤ := htop
            exact Ideal.span_singleton_eq_top.mp hspanTop
          let _ : Nontrivial (QuotSMulTop x R) := Submodule.Quotient.nontrivial_iff.2 <| by
            simpa [QuotSMulTop] using hxsmul_ne_top
          refine IsRegular.cons hxsmul ?_
          simpa using IsRegular.nil R (QuotSMulTop x R)
        · simpa using (Ideal.span_singleton_le_iff_mem I).2 hxI
  · rintro hdepth
    rcases (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mpr hdepth with
      hI | ⟨rs, hrs, hrs_le, hrs_len⟩
    · exact .inl hI
    · rcases List.length_eq_one_iff.mp hrs_len with ⟨x, rfl⟩
      have hxsmul : IsSMulRegular R x := by
        exact ((isRegular_cons_iff R x []).mp (by simpa using hrs)).1
      refine .inr ⟨x, ?_, ?_⟩
      · exact hrs_le (Ideal.subset_span (by simp : x ∈ {r | r ∈ ([x] : List R)}))
      · refine ⟨hxsmul.isLeftRegular, ?_⟩
        simpa [IsRightRegular, IsSMulRegular, smul_eq_mul, mul_comm] using hxsmul

end Ideal

end

namespace LinearMap

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {m n : ℕ}

/- Domain triage:
* primary domain: injectivity criteria for maps of finite free modules over a local ring, governed
  upstream by the Buchsbaum--Eisenbud exactness criterion for finite free complexes;
* sampled owner declarations of the same kind:
  `LinearMap.exteriorRank`,
  `LinearMap.rankMinorIdeal`,
  `Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth`,
  `FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud_depth_criterion`;
* core/canonical owner: the Chapter 10 Buchsbaum--Eisenbud criterion, specialized here to a
  two-term complex, with the Noetherian ideal-theoretic clause canonically expressed via
  `Ideal.depth`;
* source-facing layer: the injectivity criterion with annihilator zero and its regular-element
  reformulation below;
* bridge/view layer: the depth reformulation and the local length-`1` regular-sequence bridge
  between `Ideal.depth` and `I(φ) = ⊤ ∨ ∃ x ∈ I(φ), IsRegular x`.

Primitive data are only the map `φ`, its owner invariants `exteriorRank φ` and `I(φ)`, and the
ambient local-ring hypotheses. The annihilator and nonzerodivisor conditions are derived API, so
this file should reuse the chapter owner abstraction instead of introducing a parallel determinantal
package.
-/

-- Proof sketch: for the forward implication, reduce to weakly associated primes of the local
-- ring and use the auto-associated criteria from the preceding lemmas to show that the rank-minor
-- ideal survives in every weakly associated residue field, forcing full exterior rank and trivial
-- annihilator. For the converse, use the full-rank condition to write the identity on `R^m`
-- locally through finitely many maximal minors, and then the trivial annihilator of the rank-minor
-- ideal kills every kernel element.
/-- Lemma 15.15.6: for a map `φ : R^m → R^n` of finite free modules over a local ring, `φ` is
injective if and only if it has exterior rank `m` and the annihilator of its rank-minor ideal
`I(φ)` is zero. -/
theorem injective_iff_exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      exteriorRank φ = m ∧
        (I(φ)).annihilator = (⊥ : Ideal R) := sorry

section Noetherian

variable [IsNoetherianRing R]

-- Proof sketch: this is the `i = 0` depth form of the Chapter 10 Buchsbaum--Eisenbud owner
-- specialized to the two-term complex attached to `φ`, where `1 ≤ depth I(φ)` is the canonical
-- owner-side replacement for the length-`1` regular-sequence clause.
/-- Companion owner-style reformulation: over a Noetherian local ring, injectivity is equivalently
detected by full exterior rank together with positive depth of the rank-minor ideal. -/
theorem injective_iff_exteriorRank_eq_and_one_le_depth_rankMinorIdeal
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      exteriorRank φ = m ∧
        (1 : WithTop ℕ) ≤ (I(φ)).depth R := sorry

-- Proof sketch: combine the owner-style depth criterion above with the Noetherian local bridge
-- identifying positive depth with either `I(φ) = ⊤` or the presence of a regular element in
-- `I(φ)`.
/-- In a Noetherian local ring, injectivity is equivalently detected by full exterior rank together
with the rank-minor ideal being the unit ideal or containing a nonzerodivisor. -/
theorem injective_iff_exteriorRank_eq_and_rankMinorIdeal_eq_top_or_exists_isRegular
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      exteriorRank φ = m ∧
        (I(φ) = ⊤ ∨ ∃ x ∈ I(φ), IsRegular x) := by
  rw [injective_iff_exteriorRank_eq_and_one_le_depth_rankMinorIdeal]
  rw [Ideal.eq_top_or_exists_isRegular_iff_one_le_depth]

end Noetherian

end

end LinearMap
