import Mathlib
import StacksProject_2024.Chap10.Lemma_10_119_2_Koll_r

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
/-- Helper for Lemma 10.119.3: a local Noetherian ring of Krull dimension `1` cannot be
Artinian. -/
lemma not_isArtinianRing_of_ringKrullDim_eq_one
    (hdim : ringKrullDim R = 1) :
    ¬ IsArtinianRing R := by
  -- Proof comment: an Artinian local ring has Krull dimension `0`, contradicting `hdim`.
  intro hArt
  have hzero : ringKrullDim R = 0 := by
    exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
      ((isArtinianRing_iff_krullDimLE_zero).mp hArt)
  have : (0 : WithBot ℕ∞) = 1 := by
    simpa [hzero] using hdim
  norm_num at this

/-- Helper for Lemma 10.119.3: a one-dimensional regular local ring has one-dimensional
cotangent space. -/
lemma finrank_cotangentSpace_eq_one_of_regular_dim_one
    [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) :
    Module.finrank (ResidueField R) (CotangentSpace R) = 1 := by
  -- Proof comment: regularity identifies the Krull dimension with the minimal number of
  -- generators of the maximal ideal, and the cotangent-space dimension is that same span rank.
  have hspan :
      ringKrullDim R = (maximalIdeal R).spanFinrank := by
    simpa using
      ((isRegularLocalRing_iff (R := R)).1 (inferInstance : IsRegularLocalRing R)).symm
  have hcot :
      (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) = 1 := by
    calc
      (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) =
          (maximalIdeal R).spanFinrank := by
            rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)]
      _ = 1 := by
        simpa [hdim] using hspan.symm
  exact_mod_cast hcot

/-- Helper for Lemma 10.119.3: in Krull dimension `1`, the depth of the self-module is at most
`1`. -/
lemma moduleDepth_self_le_one_of_ringKrullDim_eq_one
    (hdim : ringKrullDim R = 1) :
    moduleDepth R R ≤ 1 := by
  -- Proof comment: Lemma `10.72.3` gives `depth ≤ supportDim`, and the support dimension of the
  -- self-module is the Krull dimension.
  have hle :
      ((moduleDepth R R : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
    calc
      ((moduleDepth R R : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim R R := depth_le_supportDim
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim (R := R) (M := R)
      _ = 1 := hdim
  exact_mod_cast hle

/-- Lemma 10.119.3: if `R` is a Noetherian local ring of Krull dimension `1` and the cotangent
space `𝔪/𝔪²` of its maximal ideal has dimension greater than `1`, then there exists a finite
ring map `R → R'` that is not an isomorphism, whose kernel and cokernel are annihilated by a
power of `𝔪`, such that `𝔪` is not an associated prime of `R'`; equivalently, Kollár's canonical
exceptional-extension alternative `HasKollarExceptionalFiniteExtension R` holds. -/
@[stacks 00P9]
theorem hasKollarExceptionalFiniteExtension_of_ringKrullDim_eq_one_of_one_lt_finrank_cotangentSpace
    (hdim : ringKrullDim R = 1)
    (hcot : 1 < Module.finrank (ResidueField R) (CotangentSpace R)) :
    HasKollarExceptionalFiniteExtension R := by
  -- Proof comment: Lemma `10.119.2 (Kollár)` gives four mutually exclusive cases, so it remains
  -- to exclude the Artinian, regular one-dimensional, and depth-`≥ 2` branches.
  have hxor :=
    kollar_exactly_one_of_artinian_regular_dim_one_depth_ge_two_or_exceptional_finite_extension
      (R := R)
  have hnotArt : ¬ IsArtinianRing R :=
    not_isArtinianRing_of_ringKrullDim_eq_one (R := R) hdim
  have hnotReg : ¬ (IsRegularLocalRing R ∧ ringKrullDim R = 1) := by
    -- Proof comment: in the regular one-dimensional branch, the cotangent space would have
    -- dimension exactly `1`, contradicting `hcot`.
    rintro ⟨hreg, hdim'⟩
    letI : IsRegularLocalRing R := hreg
    have hcot_eq :
        Module.finrank (ResidueField R) (CotangentSpace R) = 1 :=
      finrank_cotangentSpace_eq_one_of_regular_dim_one (R := R) hdim'
    omega
  have hnotDepth : ¬ ((2 : WithTop ℕ) ≤ moduleDepth R R) := by
    -- Proof comment: the depth branch is impossible because `depth R ≤ dim R = 1`.
    intro hdepth
    have hdepth' : (2 : ℕ∞) ≤ moduleDepth R R := by
      simpa using hdepth
    have hdepth_le : moduleDepth R R ≤ 1 :=
      moduleDepth_self_le_one_of_ringKrullDim_eq_one (R := R) hdim
    have : (2 : ℕ∞) ≤ 1 := le_trans hdepth' hdepth_le
    norm_num at this
  -- Proof comment: once the first three branches are eliminated, Kollár's fourth alternative is
  -- the only surviving case.
  simpa [Xor', hnotArt, hnotReg, hnotDepth] using hxor

end
