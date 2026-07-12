import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_21_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

section

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {I : Type*} [Nonempty I]

namespace Finsupp

/-- A nonnegative nontrivial multiplier family whose weighted sum is pointwise nonnegative on
`C` with zero lower bound. -/
abbrev IsNonnegativeZeroBoundCertificateOn
    [Finite I]
    (weights : I →₀ 𝕜) (C : Set E) (f : I → E → WithBotTop 𝕜) : Prop :=
  by
    classical
    letI : Fintype I := Fintype.ofFinite I
    exact (weights : I → 𝕜).IsNonnegativeZeroBoundCertificateOn C f

end Finsupp

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 21.6.2 sharpens the source-facing alternatives of Theorems 21.1 and
  21.2 by sharpening their chapter-owner feasible-set alternatives: either the original owner
  feasible-set branch holds, or the multiplier branch can already be stated with at most
  `Module.finrank 𝕜 E + 1` nonzero multipliers on the strict side. Specializing to
  `𝕜 = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the textbook bound `n + 1`.
- `core/canonical`: the owner APIs are the source-facing `Xor'` alternatives from Theorems 21.1
  and 21.2 together with the canonical finitely supported owner `Finsupp` for support-bounded
  certificate data and its intrinsic weighted sum `w.sum`. On the mixed side the convex and affine
  multipliers are still best packaged as a single sum-indexed `Finsupp` on `ι ⊕ κ`.
  The strict branch now stays on the same scalar-generic owner layer as Theorem 21.1; the mixed
  branch remains on the finite-dimensional real layer inherited from Theorem 21.2. The stronger
  Chapter 21.3 predicate
  `Finsupp.IsNonnegativeMultiplierCertificateOn` is not the right owner here: it packages a
  uniform positive lower bound `ε > 0`, while Corollary 21.6.2 preserves the weaker Theorems 21.1
  and 21.2 certificate semantics with lower bound `0`.
- `bridge/view`: the source-pointwise and certificate-only extraction lemmas are companions. They
  are obtained by expanding the owner feasible-set side or by combining the sharpened `Xor'`
  alternatives with the original Theorems 21.1 and 21.2 to rule out the owner feasible-set branch
  once an old-style certificate is already given.

Domain-style sampling used here:
- `xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate`;
- `xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate`;
- `strict_convexInequalitySolutionSet_nonempty_iff`;
- `mixed_convexInequalitySolutionSet_nonempty_iff_affine`;
- `convexInequalitySolutionSet_nonempty_of_small_subsystems_feasible`;
- `Finsupp.sum`;
- `mixedSystem`.

Primitive data vs derived API:
- primitive source-facing data: the existing owner feasible-set branches and multiplier hypotheses from
  Theorems 21.1 and 21.2; for the strict-family branch this includes the nonempty finite index
  family required already by Theorem 21.1;
- primitive owner-side bounded-certificate data in this corollary: a single finitely supported
  multiplier family `w` together with its intrinsic sum `w.sum`;
- derived API: the source-pointwise bridge companions obtained by expanding the owner feasible-set
  side, and the certificate-only extraction companions obtained from the sharpened `Xor'`
  statements.

Layer target: `source-facing` for the two sharpened owner alternatives, with `bridge/view`
companions that expand the owner feasible-set side to the textbook pointwise wording and that
extract only the bounded certificate branch when an old-style certificate is already known.
-/

/-- Corollary 21.6.2 (1), owner form: under the hypotheses of Theorem 21.1, exactly one of the
following holds: either the strict Chapter 21 feasible set on `C` is nonempty, or there is a
nontrivial nonnegative finitely supported multiplier family `w` with
`w.support.card ≤ Module.finrank 𝕜 E + 1` whose weighted sum is nonnegative on `C`. Specializing
to `𝕜 = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the textbook bound `n + 1`. -/
theorem
    xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
    [Finite I]
    {C : Set E} (f : I → E → WithBotTop 𝕜) (hC : Convex 𝕜 C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i)) :
    Xor'
      ((C ∩ strictConvexInequalitySolutionSet f).Nonempty)
      (∃ w : I →₀ 𝕜,
        w.support.card ≤ Module.finrank 𝕜 E + 1 ∧
          w.IsNonnegativeZeroBoundCertificateOn C f) := sorry

/-- Corollary 21.6.2 (1), source-facing bridge: the owner feasible-set branch above is exactly the
existence of a point `x ∈ C` with `f i x < 0` for every `i`. -/
theorem xor_exists_strict_feasible_point_or_nonnegative_multiplier_certificate_with_support_card_le
    [Finite I]
    {C : Set E} (f : I → E → WithBotTop 𝕜) (hC : Convex 𝕜 C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i)) :
    Xor'
      (∃ x : E, x ∈ C ∧ ∀ i, f i x < 0)
      (∃ w : I →₀ 𝕜,
        w.support.card ≤ Module.finrank 𝕜 E + 1 ∧
          w.IsNonnegativeZeroBoundCertificateOn C f) := by
  simpa [strict_convexInequalitySolutionSet_nonempty_iff f] using
    xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
      f hC hf_convex hf_bot hdom

/-- Companion to Corollary 21.6.2 (1): once the old multiplier branch of Theorem 21.1 is known,
the sharpened alternative above forces a support-bounded certificate. -/
theorem exists_strict_convex_system_multiplier_certificate_with_support_card_le
    [Fintype I]
    {C : Set E} (f : I → E → WithBotTop 𝕜) (hC : Convex 𝕜 C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i))
    (hcert : ∃ w : I → 𝕜, w.IsNonnegativeZeroBoundCertificateOn C f) :
    ∃ w : I →₀ 𝕜,
      w.support.card ≤ Module.finrank 𝕜 E + 1 ∧
        w.IsNonnegativeZeroBoundCertificateOn C f := by
  classical
  have hxor :=
    xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
      f hC hf_convex hf_bot hdom
  rcases hxor.or with hfeasible | hsmall
    · have horig :=
      xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate
        f hC hf_convex hf_bot hdom
    rcases horig with ⟨_, hnotcert⟩ | ⟨_, hnotfeasible⟩
    · exact False.elim (hnotcert hcert)
    · exact False.elim (hnotfeasible hfeasible)
  · exact hsmall

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

namespace Finsupp

/-- Mixed strict/weak multiplier certificate owner used in Corollary 21.6.2 (2). -/
abbrev IsNonnegativeZeroBoundMixedCertificateOn
    (weights : (ι ⊕ κ) →₀ ℝ) (C : Set E)
    (f : ι → E → WithBotTop ℝ) (g : κ → AffineMap ℝ E ℝ) : Prop :=
  (weights : ι ⊕ κ → ℝ).IsNonnegativeZeroBoundCertificateOn C (mixedSystem f g) ∧
    ∃ i : ι, weights (.inl i) ≠ 0

end Finsupp

/-- Corollary 21.6.2 (2), owner form: under the hypotheses of Theorem 21.2, exactly one of the
following holds: either the mixed Chapter 21 feasible set on `C` is nonempty, or there is a
nonnegative sum-indexed finitely supported multiplier family
`w : (ι ⊕ κ) →₀ ℝ` with `w.support.card ≤ Module.finrank ℝ E + 1` whose weighted mixed
sum is nonnegative on `C`, and whose convex-side coefficients are not all zero. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook bound `n + 1`. -/
theorem
    xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
    {C : Set E} (hC : Convex ℝ C)
    (f : ι → E → WithBotTop ℝ) (g : κ → AffineMap ℝ E ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[ℝ](C) ⊆ dom(f i))
    (hfeas_affine : ∃ x, x ∈ ri[ℝ](C) ∧ ∀ j, g j x ≤ 0) :
    Xor'
      ((C ∩ mixedConvexInequalitySolutionSet f g).Nonempty)
      (∃ w : (ι ⊕ κ) →₀ ℝ,
        w.support.card ≤ Module.finrank ℝ E + 1 ∧
          w.IsNonnegativeZeroBoundMixedCertificateOn C f g) :=
  sorry

/-- Corollary 21.6.2 (2), source-facing bridge: the owner feasible-set branch above is exactly the
existence of a point `x ∈ C` satisfying the strict convex block and the weak affine block. -/
theorem xor_strict_feasible_or_nonnegative_multiplier_certificate_with_support_card_le
    {C : Set E} (hC : Convex ℝ C)
    (f : ι → E → WithBotTop ℝ) (g : κ → AffineMap ℝ E ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[ℝ](C) ⊆ dom(f i))
    (hfeas_affine : ∃ x, x ∈ ri[ℝ](C) ∧ ∀ j, g j x ≤ 0) :
    Xor'
      (∃ x : E, x ∈ C ∧ (∀ i : ι, f i x < 0) ∧ ∀ j : κ, g j x ≤ 0)
      (∃ w : (ι ⊕ κ) →₀ ℝ,
        w.support.card ≤ Module.finrank ℝ E + 1 ∧
          w.IsNonnegativeZeroBoundMixedCertificateOn C f g) := by
  have hiff :
      (C ∩ mixedConvexInequalitySolutionSet f g).Nonempty ↔
        ∃ x : E, x ∈ C ∧ (∀ i : ι, f i x < 0) ∧ ∀ j : κ, g j x ≤ 0 :=
    mixed_convexInequalitySolutionSet_nonempty_iff_affine f g
  rcases
      xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
        hC f g hf_convex hf_bot hdom hfeas_affine with
    hxor | hxor
  · exact Or.inl ⟨hiff.mp hxor.1, hxor.2⟩
  · exact Or.inr ⟨hxor.1, fun hfeasible ↦ hxor.2 (hiff.mpr hfeasible)⟩

/-- Companion to Corollary 21.6.2 (2): once the old multiplier branch of Theorem 21.2 is known,
the sharpened alternative above forces a support-bounded mixed certificate. -/
theorem exists_convex_affine_system_multiplier_certificate_with_support_card_le
    {C : Set E} (hC : Convex ℝ C)
    (f : ι → E → WithBotTop ℝ) (g : κ → AffineMap ℝ E ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[ℝ](C) ⊆ dom(f i))
    (hfeas_affine : ∃ x, x ∈ ri[ℝ](C) ∧ ∀ j, g j x ≤ 0)
    (hcert : ∃ wf : ι → ℝ, ∃ wg : κ → ℝ,
      (∀ i : ι, 0 ≤ wf i) ∧
      (∀ j : κ, 0 ≤ wg j) ∧
      (∃ i : ι, wf i ≠ 0) ∧
      ∀ x : C,
        (0 : WithBotTop ℝ) ≤
          (∑ i, (wf i : WithBotTop ℝ) * f i x) +
            ∑ j, (wg j : WithBotTop ℝ) * Function.toWithBotTop (g j) x) :
    ∃ w : (ι ⊕ κ) →₀ ℝ,
      w.support.card ≤ Module.finrank ℝ E + 1 ∧
        w.IsNonnegativeZeroBoundMixedCertificateOn C f g := by
  have hxor :=
    xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
      hC f g hf_convex hf_bot hdom hfeas_affine
  rcases hxor.or with hfeasible | hsmall
  · have horig :=
      xor_strict_feasible_or_nonnegative_multiplier_certificate
        hC f g hf_convex hf_bot hdom hfeas_affine
    have hfeasible' :
        ∃ x : E, x ∈ C ∧ (∀ i : ι, f i x < 0) ∧ ∀ j : κ, g j x ≤ 0 :=
      (mixed_convexInequalitySolutionSet_nonempty_iff_affine f g).mp hfeasible
    rcases horig with horig | horig
    · exact False.elim (horig.2 hcert)
    · exact False.elim (horig.2 hfeasible')
  · exact hsmall

end
