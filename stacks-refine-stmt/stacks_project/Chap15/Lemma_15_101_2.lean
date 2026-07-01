import Mathlib
import stacks_project.Chap15.Lemma_15_65_17
import stacks_project.Chap15.Lemma_15_98_6_Koll_r_Kov_cs

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Domain-style sampling for Lemma 15.101.2:
- primary domain: pseudo-coherent derived `A`-complexes, the ideal-power quotient-tensor homology
  tower, and its completion comparison;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `isPseudoCoherent_iff_boundedAbove_and_homology_finite`,
  `idealPowerQuotientTensorHomologyInverseSystem`,
  `homology_idealPowerQuotient_limit_iso_tensorQuotient_homology_limit`;
- best owner abstraction:
  `source-facing`: the Mittag-Leffler property of the tower `(H^i(K_n))_n`;
  `core/canonical`: the tower owner
    `idealPowerQuotientTensorHomologyInverseSystem I K i` and the completion-limit comparison from
    Lemma `15.98.6`;
  `bridge/view`: the finite-cohomology consequence of pseudo-coherence from Lemma `15.65.17`,
    used only to specialize the canonical comparison theorem.
- primitive vs. derived:
  primitive data are the ideal `I`, the pseudo-coherent derived object `K`, and the degree `i`;
  derived API is the Mittag-Leffler assertion for the canonical tower and the resulting canonical
  comparison from the `I`-adic completion of `H^i(K)` to the inverse limit of that tower. -/

-- Proof sketch: by Lemma `15.65.17`, pseudo-coherence over the Noetherian ring `A` implies that
-- each cohomology module `H^j(K)` is finite. Represent `K` by a bounded-above complex of finite
-- free modules; then the tower `K_n = K ⊗_A^L A / I^(n+1)` is represented degreewise by quotient
-- complexes modulo `I^(n+1)`, so Lemma `15.101.1` gives the Mittag-Leffler property for both
-- `H^{i-1}(K_n)` and `H^i(K_n)`. Finally apply Lemma `15.98.6` using the degree-`i - 1`
-- hypothesis to identify the inverse limit of
-- `H^i(K) / I^(n+1) H^i(K)` with the inverse limit of `H^i(K_n)`.
theorem idealPowerQuotientTensorHomology_isMittagLeffler_of_isPseudoCoherent
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ) :
    (idealPowerQuotientTensorHomologyInverseSystem I K i).IsMittagLeffler := by
  sorry

/-- Lemma 15.101.2: let `I` be an ideal of the Noetherian ring `A`, let `K ∈ D(A)` be
pseudo-coherent, and for each `n` set `K_n = K \otimes_A^{\mathbf L} A / I^(n+1)`. Then for every
`i : ℤ` the inverse system `(H^i(K_n))_n` is Mittag-Leffler, and the inverse limit of the
quotients `H^i(K) / I^(n+1) H^i(K)` is canonically isomorphic to the inverse limit of
`(H^i(K_n))_n`; equivalently, the `I`-adic completion of `H^i(K)` is canonically isomorphic to
that inverse limit. Lean starts the tower at `n = 0`, corresponding to the textbook power `I^1`.
-/
theorem idealPowerQuotientTensorHomology_isMittagLeffler_and_limit_iso_of_isPseudoCoherent
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ) :
    (idealPowerQuotientTensorHomologyInverseSystem I K i).IsMittagLeffler ∧
      IsIsomorphic
        (ModuleCat.of A (AdicCompletion I ((H i).obj K)))
        (limit (idealPowerQuotientTensorHomologyInverseSystem I K i)) := by
  have hKfinite : ∀ j : ℤ, Module.Finite A ((H j).obj K) :=
    (isPseudoCoherent_iff_boundedAbove_and_homology_finite K).1 hK |>.2
  refine ⟨idealPowerQuotientTensorHomology_isMittagLeffler_of_isPseudoCoherent I K hK i, ?_⟩
  exact homology_idealPowerQuotient_limit_iso_tensorQuotient_homology_limit I K i hKfinite
    (idealPowerQuotientTensorHomology_isMittagLeffler_of_isPseudoCoherent I K hK (i - 1))

end
