import Mathlib
import stacks_project.Chap10.Lemma_10_119_2_Koll_r

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-
Domain-style sampling:
- primary domain: local Noetherian commutative algebra around Kollár's exceptional finite
  extension alternative;
- sampled owner declarations:
  `HasKollarExceptionalFiniteExtension`,
  `hasKollarExceptionalFiniteExtension_iff`,
  `kollar_exactly_one_of_artinian_regular_dim_one_depth_ge_two_or_exceptional_finite_extension`;
- owner abstraction: the chapter already packages the finite-extension conclusion canonically as
  `HasKollarExceptionalFiniteExtension R`.

This lemma is therefore a `source-facing` criterion for that existing owner, not a place to keep a
parallel local wrapper around the same finite `R`-algebra data.
-/

-- Proof sketch: apply Lemma `10.119.2 (Kollár)` and rule out the other three alternatives.
-- The cotangent-space hypothesis excludes regularity in dimension `1`, and Lemma `10.72.3`
-- bounds the depth of `R` by `ringKrullDim R = 1`, so the depth-`≥ 2` alternative cannot occur.
-- In dimension `1`, the hypothesis `dim (𝔪 / 𝔪²) > 1` also rules out the Artinian/field case.
/-- Lemma 10.119.3: if `R` is a Noetherian local ring of Krull dimension `1` and the cotangent
space `𝔪/𝔪²` of its maximal ideal has dimension greater than `1`, then there exists a finite
ring map `R → R'` that is not an isomorphism, whose kernel and cokernel are annihilated by a
power of `𝔪`, such that `𝔪` is not an associated prime of `R'`; equivalently, Kollár's canonical
exceptional-extension alternative `HasKollarExceptionalFiniteExtension R` holds. -/
theorem hasKollarExceptionalFiniteExtension_of_ringKrullDim_eq_one_of_one_lt_finrank_cotangentSpace
    (hdim : ringKrullDim R = 1)
    (hcot : 1 < Module.finrank (ResidueField R) (CotangentSpace R)) :
    HasKollarExceptionalFiniteExtension R := sorry

end
