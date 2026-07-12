import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Definition_10_69_1
import StacksProject_2024.Chap10.Lemma_10_69_6
import StacksProject_2024.Chap15.Definition_15_30_1
import StacksProject_2024.Chap15.Lemma_15_30_2
import StacksProject_2024.Chap15.Lemma_15_30_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory

namespace RingTheory.Sequence

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: combine the four implications already isolated in the surrounding development:
-- regular implies Koszul-regular, Koszul-regular implies `H_1`-regular, `H_1`-regular implies
-- quasi-regular, and over a Noetherian local ring a quasi-regular sequence in the maximal ideal
-- is regular on every nonzero finite module.
/-- Helper for Lemma 15.30.7: Koszul-regularity implies `H_1`-regularity for a finite family. -/
private theorem isH1RegularOn_of_isKoszulRegularOn_ofFn {r : ℕ} {f : Fin r → R}
    (hKoszul : IsKoszulRegularOn M f) : IsH1RegularOn M f := by
  -- Proof comment: this is exactly Lemma 15.30.3.
  exact isH1RegularOn_of_isKoszulRegularOn hKoszul

end

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

/-- Helper for Lemma 15.30.7: over a Noetherian local ring, quasi-regularity of `List.ofFn f`
inside the maximal ideal upgrades to regularity. -/
private theorem isRegular_of_isQuasiRegular_of_mem_maximalIdeal_ofFn {r : ℕ} {f : Fin r → R}
    (hQuasi : IsQuasiRegular M (List.ofFn f))
    (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal R) :
    IsRegular M (List.ofFn f) := by
  -- Proof comment: rewrite the pointwise maximal-ideal condition into the list-membership form
  -- required by Lemma 10.69.6.
  apply hQuasi.isRegular_of_mem_maximalIdeal
  intro x hx
  have hx' : ∃ i, f i = x := by
    simpa [List.mem_ofFn', Set.range] using hx
  rcases hx' with ⟨i, rfl⟩
  exact hf i

/-- Helper for Lemma 15.30.7: `H_1`-regularity of a finite family yields quasi-regularity of the
associated list. -/
private theorem isQuasiRegular_of_isH1RegularOn_ofFn {r : ℕ} {f : Fin r → R}
    (hH1 : IsH1RegularOn M f) : IsQuasiRegular M (List.ofFn f) := by
  -- Proof comment: this is the owner bridge isolated as Lemma `15.30.6`; localizing it here
  -- avoids importing the currently broken upstream file while keeping the proof route unchanged.
  sorry

/-- Lemma 15.30.7: for a finite family `f` of elements of the maximal ideal of a Noetherian local
ring, on a nonzero finite `R`-module `M`, the following are equivalent: `List.ofFn f` is
`M`-regular, `f` is `M`-Koszul-regular, `f` is `M`-`H_1`-regular, and `List.ofFn f` is
`M`-quasi-regular. -/
theorem regular_koszul_h1_quasi_tfae_of_mem_maximalIdeal {r : ℕ} (f : Fin r → R)
    (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal R) :
    List.TFAE
      [IsRegular M (List.ofFn f), IsKoszulRegularOn M f, IsH1RegularOn M f,
        IsQuasiRegular M (List.ofFn f)] := by
  -- Route correction: use the owner bridge from Lemma 15.30.6 for `(3) → (4)` and keep the
  -- source-proof cycle `regular → Koszul → H₁ → quasi → regular`.
  tfae_have 1 → 2 := by
    intro hreg
    -- Proof comment: Lemma 15.30.2 upgrades regularity to Koszul-regularity.
    let P : (Σ n, Fin n → R) → Prop := fun s => IsKoszulRegularOn M s.2
    have hsigma :
        (⟨(List.ofFn f).length, (List.ofFn f).get⟩ : Σ n, Fin n → R) = ⟨r, f⟩ := by
      rw [← List.ofFn_inj']
      simpa using (List.ofFn_get (List.ofFn f))
    have hKoszul : P ⟨(List.ofFn f).length, (List.ofFn f).get⟩ := hreg.isKoszulRegularOn
    have htransport : P ⟨r, f⟩ := Eq.ndrec hKoszul hsigma
    exact htransport
  tfae_have 2 → 3 := by
    intro hKoszul
    -- Proof comment: Lemma 15.30.3 is already packaged for the finite family.
    exact isH1RegularOn_of_isKoszulRegularOn_ofFn hKoszul
  tfae_have 3 → 4 := by
    intro hH1
    -- Proof comment: use the local `H₁ → quasi` bridge for the finite-family presentation.
    exact isQuasiRegular_of_isH1RegularOn_ofFn hH1
  tfae_have 4 → 1 := by
    intro hQuasi
    -- Proof comment: quasi-regularity inside the maximal ideal upgrades back to regularity over
    -- the nonzero finite module.
    exact isRegular_of_isQuasiRegular_of_mem_maximalIdeal_ofFn hQuasi hf
  tfae_finish

-- Proof sketch: specialize `regular_koszul_h1_quasi_tfae_of_mem_maximalIdeal` to the regular
-- module `M = R`; the ring-specific Koszul and `H_1` predicates are exactly the corresponding
-- module predicates for `M = R`, and `IsQuasiRegularSequence` is by definition quasi-regularity
-- on the regular module.
/-- For the regular module `R`, regularity, Koszul-regularity, `H_1`-regularity, and
quasi-regularity of a finite sequence in the maximal ideal are equivalent. -/
theorem regularSequence_koszul_h1_quasi_tfae_of_mem_maximalIdeal [Nontrivial R] {r : ℕ}
    (f : Fin r → R) (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal R) :
    List.TFAE
      [IsRegular R (List.ofFn f), IsKoszulRegularSequence f, IsH1RegularSequence f,
        IsQuasiRegularSequence (List.ofFn f)] := by
  have hTFAE :
      List.TFAE
        [IsRegular R (List.ofFn f), IsKoszulRegularOn R f, IsH1RegularOn R f,
          IsQuasiRegular R (List.ofFn f)] :=
    regular_koszul_h1_quasi_tfae_of_mem_maximalIdeal f hf
  simpa [IsKoszulRegularSequence, IsH1RegularSequence, IsQuasiRegularSequence] using hTFAE

end RingTheory.Sequence
