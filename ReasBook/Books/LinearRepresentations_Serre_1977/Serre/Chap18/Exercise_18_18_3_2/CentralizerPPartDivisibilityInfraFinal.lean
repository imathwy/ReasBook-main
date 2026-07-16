import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularClasses

noncomputable section

open scoped MonoidAlgebra Representation

universe u

namespace Representation

/-!
Final DVR/divisibility audit for the centralizer-`p`-part residual branch.

Useful existing API:
* `dvd_def` / `exists_eq_mul_right_of_dvd` turns `z ∣ x` into `∃ a, x = z * a`.
* `ConjClasses.centralizerPPart_eq_prime_pow` gives
  `ConjClasses.centralizerPPart p c = p ^ n`.
* `Nat.cast_pow` rewrites the cast of that prime power in any semiring.
* `IsLocalRing.residue_eq_zero_iff` identifies residue-zero with membership in
  `IsLocalRing.maximalIdeal A`.
* `Irreducible.maximalIdeal_eq` identifies the maximal ideal of a DVR with the span of any
  irreducible uniformizer.
* `IsDiscreteValuationRing.addVal_le_iff_dvd` is the actual DVR criterion for arbitrary
  higher-power divisibility.

The key negative point is formalized by the residue lemmas below: a single residue congruence
only gives divisibility by a uniformizer, hence one valuation step.  It does not by itself give
divisibility by `(p : A) ^ n`, or by
`(ConjClasses.centralizerPPart p c : A)`, unless an additional valuation/divisibility input is
supplied.
-/

section CentralizerPPartCast

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [Finite G]
variable {A : Type u} [Semiring A]

/-- Cast a known centralizer-`p`-part prime-power identity into any semiring. -/
theorem centralizerPPart_natCast_eq_pow_of_eq_primePow
    (c : ConjClasses G) {n : ℕ}
    (hc : ConjClasses.centralizerPPart p c = p ^ n) :
    (ConjClasses.centralizerPPart p c : A) = (p : A) ^ n := by
  rw [hc, Nat.cast_pow]

/-- Every cast centralizer-`p`-part is visibly a cast power of `p`. -/
theorem exists_centralizerPPart_natCast_eq_pow
    (c : ConjClasses G) :
    ∃ n : ℕ, (ConjClasses.centralizerPPart p c : A) = (p : A) ^ n := by
  rcases ConjClasses.centralizerPPart_eq_prime_pow (p := p) c with ⟨n, hn⟩
  exact ⟨n, centralizerPPart_natCast_eq_pow_of_eq_primePow (A := A) (p := p) c hn⟩

/-- The existential multiplier form for divisibility by a cast centralizer-`p`-part. -/
theorem exists_eq_centralizerPPart_mul_iff
    (c : ConjClasses G) {x : A} :
    (∃ a : A, x = (ConjClasses.centralizerPPart p c : A) * a) ↔
      (ConjClasses.centralizerPPart p c : A) ∣ x :=
  Iff.rfl

/-- If the corresponding cast power of `p` divides `x`, then the cast centralizer-`p`-part
divides `x`. -/
theorem centralizerPPart_natCast_dvd_of_primePow_dvd
    (c : ConjClasses G) {n : ℕ} {x : A}
    (hc : ConjClasses.centralizerPPart p c = p ^ n)
    (hx : (p : A) ^ n ∣ x) :
    (ConjClasses.centralizerPPart p c : A) ∣ x := by
  simpa [centralizerPPart_natCast_eq_pow_of_eq_primePow (A := A) (p := p) c hc] using hx

/-- Multiplier form of `centralizerPPart_natCast_dvd_of_primePow_dvd`. -/
theorem exists_eq_centralizerPPart_mul_of_primePow_dvd
    (c : ConjClasses G) {n : ℕ} {x : A}
    (hc : ConjClasses.centralizerPPart p c = p ^ n)
    (hx : (p : A) ^ n ∣ x) :
    ∃ a : A, x = (ConjClasses.centralizerPPart p c : A) * a :=
  (centralizerPPart_natCast_dvd_of_primePow_dvd
    (A := A) (p := p) c hc hx)

end CentralizerPPartCast

section DVRResidue

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
variable [IsDiscreteValuationRing A]
variable {G : Type u} [Group G] [Finite G]

/-- In a DVR, residue-zero is exactly divisibility by any irreducible uniformizer. -/
theorem residue_eq_zero_iff_irreducible_dvd
    {ϖ x : A} (hϖ : Irreducible ϖ) :
    IsLocalRing.residue A x = 0 ↔ ϖ ∣ x := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]

omit [Fact p.Prime] in
/-- If the residue field has characteristic `p`, then a uniformizer divides `(p : A)`.

This is only a one-step valuation statement.  It does not say that `(p : A)` is a uniformizer,
nor that `(p : A) ^ n` divides an arbitrary residue-zero element. -/
theorem irreducible_dvd_natCast_of_residue_char
    [CharP (IsLocalRing.ResidueField A) p]
    {ϖ : A} (hϖ : Irreducible ϖ) :
    ϖ ∣ (p : A) := by
  rw [← residue_eq_zero_iff_irreducible_dvd (A := A) hϖ]
  simp

omit [IsLocalRing A] in
/-- DVR valuation criterion for divisibility by a cast centralizer-`p`-part. -/
theorem centralizerPPart_natCast_dvd_iff_addVal_le
    (c : ConjClasses G) {x : A} :
    (ConjClasses.centralizerPPart p c : A) ∣ x ↔
      IsDiscreteValuationRing.addVal A (ConjClasses.centralizerPPart p c : A) ≤
        IsDiscreteValuationRing.addVal A x := by
  exact
    (IsDiscreteValuationRing.addVal_le_iff_dvd
      (R := A) (a := (ConjClasses.centralizerPPart p c : A)) (b := x)).symm

omit [IsLocalRing A] in
/-- Valuation inequality form of centralizer-`p`-part divisibility. -/
theorem centralizerPPart_natCast_dvd_of_addVal_le
    (c : ConjClasses G) {x : A}
    (hval :
      IsDiscreteValuationRing.addVal A (ConjClasses.centralizerPPart p c : A) ≤
        IsDiscreteValuationRing.addVal A x) :
    (ConjClasses.centralizerPPart p c : A) ∣ x :=
  (centralizerPPart_natCast_dvd_iff_addVal_le
    (A := A) (p := p) c).2 hval

omit [IsLocalRing A] in
/-- Multiplier form of the DVR valuation criterion. -/
theorem exists_eq_centralizerPPart_mul_of_addVal_le
    (c : ConjClasses G) {x : A}
    (hval :
      IsDiscreteValuationRing.addVal A (ConjClasses.centralizerPPart p c : A) ≤
        IsDiscreteValuationRing.addVal A x) :
    ∃ a : A, x = (ConjClasses.centralizerPPart p c : A) * a :=
  centralizerPPart_natCast_dvd_of_addVal_le
    (A := A) (p := p) c hval

/-- What a residue-zero input can prove about centralizer-`p`-part divisibility: after choosing a
uniformizer, one still needs the extra bridge that the cast centralizer-`p`-part divides that
uniformizer.  Without such a bridge, residue-zero only gives the right-hand uniformizer
divisibility in `residue_eq_zero_iff_irreducible_dvd`. -/
theorem centralizerPPart_natCast_dvd_of_residue_eq_zero_of_dvd_uniformizer
    (c : ConjClasses G) {ϖ x : A}
    (hϖ : Irreducible ϖ)
    (hres : IsLocalRing.residue A x = 0)
    (hcentralizer_dvd_uniformizer :
      (ConjClasses.centralizerPPart p c : A) ∣ ϖ) :
    (ConjClasses.centralizerPPart p c : A) ∣ x :=
  hcentralizer_dvd_uniformizer.trans
    ((residue_eq_zero_iff_irreducible_dvd (A := A) hϖ).1 hres)

end DVRResidue

end Representation
