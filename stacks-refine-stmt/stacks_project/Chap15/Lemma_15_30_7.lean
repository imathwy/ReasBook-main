import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Definition_10_69_1
import stacks_project.Chap15.Definition_15_30_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

-- Proof sketch: combine the four implications already isolated in the surrounding development:
-- regular implies Koszul-regular, Koszul-regular implies `H_1`-regular, `H_1`-regular implies
-- quasi-regular, and over a Noetherian local ring a quasi-regular sequence in the maximal ideal
-- is regular on every nonzero finite module.
/-- Lemma 15.30.7: for a finite family `f` of elements of the maximal ideal of a Noetherian local
ring, on a nonzero finite `R`-module `M`, the following are equivalent: `List.ofFn f` is
`M`-regular, `f` is `M`-Koszul-regular, `f` is `M`-`H_1`-regular, and `List.ofFn f` is
`M`-quasi-regular. -/
theorem regular_koszul_h1_quasi_tfae_of_mem_maximalIdeal {r : ℕ} (f : Fin r → R)
    (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal R) :
    List.TFAE
      [IsRegular M (List.ofFn f), IsKoszulRegularOn M f, IsH1RegularOn M f,
        IsQuasiRegular M (List.ofFn f)] := sorry

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
