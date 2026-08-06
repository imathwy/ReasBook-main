import Mathlib.Data.Int.ModEq
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Definition_21_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_1_3

open scoped Manifold

noncomputable section

section

variable {K : Type} [Field K]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace H M] [CompactSpace M] [IsManifold I ⊤ M]

section

omit [IsManifold I ⊤ M]

/-- Bridge form of Proposition 21.2.3 in the `4 * m`-dimensional case: Definition 21.2.2
identifies `I(M)` with the signature owner `manifoldIndexFourMul o`. -/
theorem manifoldEulerCharacteristic_modEq_manifoldIndexFourMul_of_oriented_dim_eq_four_mul (m : ℕ)
    [Fact (Module.finrank ℝ E = 4 * m)] [o : ROrientedManifold ℤ I (4 * m) M] :
    manifoldEulerCharacteristic K M ≡ manifoldIndexFourMul o [ZMOD 2] := by
  sorry

/-- Proposition 21.2.3 in the `4 * m`-dimensional case: the Euler characteristic of a compact
oriented manifold agrees modulo `2` with the index `I(M)` from Definition 21.2.2. -/
theorem manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_four_mul (m : ℕ)
    [Fact (Module.finrank ℝ E = 4 * m)] [o : ROrientedManifold ℤ I (4 * m) M] :
    manifoldEulerCharacteristic K M ≡ manifoldIndex o [ZMOD 2] := by
  simpa [manifoldIndex_eq_manifoldIndexFourMul o] using
    manifoldEulerCharacteristic_modEq_manifoldIndexFourMul_of_oriented_dim_eq_four_mul m

end

include I

/-- Companion form of Proposition 21.2.3 in the odd-dimensional case, using the vanishing of
`χ(M)` from Proposition 21.1.2. -/
theorem manifoldEulerCharacteristic_modEq_zero_of_dim_eq_two_mul_add_one (m : ℕ)
    [Fact (Module.finrank ℝ E = 2 * m + 1)] :
    manifoldEulerCharacteristic K M ≡ 0 [ZMOD 2] := by
  have hχ : manifoldEulerCharacteristic K M = 0 :=
    manifoldEulerCharacteristic_eq_zero_of_oddDimension
      (K := K) (E := E) (I := I) (M := M) m
  simp [hχ]

section

omit [IsManifold I ⊤ M]

/-- Proposition 21.2.3 in the odd-dimensional case: Proposition 21.1.2 gives `χ(M) = 0`, and
Definition 21.2.2 sets `I(M) = 0` away from the `4 * k`-dimensional case. -/
theorem manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_two_mul_add_one
    (m : ℕ) [Fact (Module.finrank ℝ E = 2 * m + 1)] [o : ROrientedManifold ℤ I (2 * m + 1) M] :
    manifoldEulerCharacteristic K M ≡ manifoldIndex o [ZMOD 2] := by
  have hI : manifoldIndex o = 0 := by
    exact manifoldIndex_eq_zero_of_mod_ne_zero o (by omega)
  have hχ : manifoldEulerCharacteristic K M ≡ 0 [ZMOD 2] :=
    manifoldEulerCharacteristic_modEq_zero_of_dim_eq_two_mul_add_one
      (K := K) (E := E) (I := I) (M := M) m
  simpa [hI] using hχ

/-- Bridge form of Proposition 21.2.3 for dimensions congruent to `2 [MOD 4]`: Proposition 21.1.3
gives `χ(M) ≡ 0 [ZMOD 2]`, and Definition 21.2.2 sets `I(M) = 0`. -/
theorem manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_modEq_two {n : ℕ}
    [Fact (Module.finrank ℝ E = n)] [o : ROrientedManifold ℤ I n M] (h_dim : n ≡ 2 [MOD 4]) :
    manifoldEulerCharacteristic K M ≡ manifoldIndex o [ZMOD 2] := by
  have hχ : manifoldEulerCharacteristic K M ≡ 0 [ZMOD 2] :=
    (even_manifoldEulerCharacteristic_of_oriented_dim_modEq_two h_dim).two_dvd.modEq_zero_int
  have hmod : n % 4 = 2 := by
    simpa [Nat.ModEq] using h_dim
  have hI : manifoldIndex o = 0 := by
    exact manifoldIndex_eq_zero_of_mod_ne_zero o (by omega)
  simpa [hI] using hχ

/-- Proposition 21.2.3 in the `4 * m + 2`-dimensional case: Definition 21.2.2 sets `I(M) = 0`,
so Proposition 21.1.3 identifies `χ(M)` with `I(M)` modulo `2`. -/
theorem manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_four_mul_add_two (m : ℕ)
    [Fact (Module.finrank ℝ E = 4 * m + 2)]
    [o : ROrientedManifold ℤ I (4 * m + 2) M] :
    manifoldEulerCharacteristic K M ≡ manifoldIndex o [ZMOD 2] := by
  have h_dim : (4 * m + 2) % 4 = 2 := by
    omega
  exact manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_modEq_two
    (by simp [Nat.ModEq, h_dim])

/-- Companion form of Proposition 21.2.3 in the `4 * m + 2`-dimensional case, using the
vanishing of `I(M)` from Definition 21.2.2. -/
theorem manifoldEulerCharacteristic_modEq_zero_of_oriented_dim_eq_four_mul_add_two (m : ℕ)
    [Fact (Module.finrank ℝ E = 4 * m + 2)]
    [o : ROrientedManifold ℤ I (4 * m + 2) M] :
    manifoldEulerCharacteristic K M ≡ 0 [ZMOD 2] := by
  exact
    (manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_four_mul_add_two m).trans
      (by simp [manifoldIndex_eq_zero_of_mod_ne_zero o (by omega)])

/-- Proposition 21.2.3. For a compact oriented manifold, the Euler characteristic agrees modulo
`2` with the index `I(M)` from Definition 21.2.2. The proof reuses the `4 * m`,
`2 * m + 1`, and `n ≡ 2 [MOD 4]` branches, with
`manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_four_mul_add_two`
as the source-facing specialization of the last branch. -/
theorem manifoldEulerCharacteristic_modEq_manifoldIndex {n : ℕ}
    [Fact (Module.finrank ℝ E = n)] [o : ROrientedManifold ℤ I n M] :
    manifoldEulerCharacteristic K M ≡ manifoldIndex o [ZMOD 2] := by
  have hmod_lt : n % 4 < 4 := Nat.mod_lt n (by decide)
  interval_cases hmod : n % 4
  · have hm : n = 4 * (n / 4) := by
      simpa [hmod] using (Nat.mod_add_div n 4).symm
    obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m := ⟨n / 4, hm⟩
    simpa using manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_four_mul m
  · have hm : n = 2 * (n / 2) + 1 := by
      have hdiv := (Nat.mod_add_div n 2).symm
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, hm⟩
    simpa using
      manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_two_mul_add_one m
  · exact manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_modEq_two
      (by simpa [Nat.ModEq] using hmod)
  · have hm : n = 2 * (n / 2) + 1 := by
      have hdiv := (Nat.mod_add_div n 2).symm
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, hm⟩
    simpa using
      manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_two_mul_add_one m

end

/- Proposition 21.2.3. For compact oriented manifolds, `χ(M) ≡ I(M) mod 2`.

In the current repository, the main source-facing entry is
`manifoldEulerCharacteristic_modEq_manifoldIndex`. The odd-dimensional branch is exposed by
`manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_two_mul_add_one` together
with the zero-valued companion `manifoldEulerCharacteristic_modEq_zero_of_dim_eq_two_mul_add_one`.
The `4 * m` branch
is exposed both in the source-facing form
`manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_four_mul` and in the bridge
form `manifoldEulerCharacteristic_modEq_manifoldIndexFourMul_of_oriented_dim_eq_four_mul`, while
the `n ≡ 2 [MOD 4]` bridge is exposed by
`manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_modEq_two`, and its source-facing
`4 * m + 2` specialization is formalized by
`manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_four_mul_add_two` together
with the zero-valued companion
`manifoldEulerCharacteristic_modEq_zero_of_oriented_dim_eq_four_mul_add_two`. -/
#check manifoldEulerCharacteristic_modEq_manifoldIndex
#check manifoldEulerCharacteristic_modEq_manifoldIndexFourMul_of_oriented_dim_eq_four_mul
#check manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_four_mul
#check manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_two_mul_add_one
#check manifoldEulerCharacteristic_modEq_zero_of_dim_eq_two_mul_add_one
#check manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_modEq_two
#check manifoldEulerCharacteristic_modEq_manifoldIndex_of_oriented_dim_eq_four_mul_add_two
#check manifoldEulerCharacteristic_modEq_zero_of_oriented_dim_eq_four_mul_add_two
#check ROrientedManifold
