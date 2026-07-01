import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v w

section

variable {R : Type u} [Ring R]
variable {ι : Type w} [LinearOrder ι] [IsWellOrder ι (· < ·)]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain-style sampling:
* primary domain: projective dimension in `ModuleCat R` together with well-ordered filtrations by
  submodules;
* sampled owner declarations:
  `HasProjectiveDimensionLE`,
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁`,
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₂`,
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃`;
* best owner abstraction: the ambient owner notion is `HasProjectiveDimensionLE` on
  `ModuleCat.of R M`, while the short-exact `LT` lemmas are the canonical core step used on each
  successor quotient;
* layer triage: this item is `bridge/view`, translating the source-facing well-ordered submodule
  filtration into the canonical projective-dimension owner API;
* primitive data: the filtration `M_ : ι → Submodule R M` together with monotonicity and
  exhaustiveness;
* derived API: the bound on `M`, obtained from the owner short-exact machinery applied to the
  successive quotient hypotheses.
-/

-- Proof sketch: argue by induction on the projective-dimension bound. For `n = 0`, split each
-- successor quotient, identify `M` with the direct sum of these projective factors, and apply the
-- canonical projectivity of arbitrary direct sums. For `n + 1`, choose compatible free covers of
-- the stages, pass to the well-ordered union of the kernels, use the short exact sequence bound on
-- successive quotients from Lemma 10.109.9, and apply the induction hypothesis to the kernel
-- filtration.
/-- Lemma 10.109.11: if `M` is the union of a well-ordered increasing family of submodules `Mₑ`,
and each successive quotient `Mₑ / ⋃_{e' < e} M_{e'}` has projective dimension at most `n`, then
`M` itself has projective dimension at most `n`. -/
theorem hasProjectiveDimensionLE_of_wellOrdered_submodule_union
    (M_ : ι → Submodule R M) (hmono : Monotone M_) (hcover : iSup M_ = ⊤) (n : ℕ)
    (hquot :
      ∀ e : ι,
        HasProjectiveDimensionLE
          (ModuleCat.of R (M_ e ⧸ (⨆ e' : Set.Iio e, M_ e').comap (M_ e).subtype)) n) :
    HasProjectiveDimensionLE (ModuleCat.of R M) n := sorry

end
