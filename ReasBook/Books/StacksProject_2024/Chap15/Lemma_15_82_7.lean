import Mathlib
import StacksProject_2024.Chap15.Definition_15_81_2
import StacksProject_2024.Chap15.Definition_15_82_4
import StacksProject_2024.Chap15.Lemma_15_65_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]
variable [Algebra.FiniteType R A]

/- Domain-style sampling:
- primary domain: relative pseudo-coherence for modules over a finite type algebra;
- sampled owner declarations:
  `Module.IsMPseudoCoherentRelativeTo`,
  `Module.IsPseudoCoherentRelativeTo`,
  `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `Module.FinitePresentationRelativeTo`,
  `Module.HasLengthFiniteFreeResolution`;
- best owner abstraction: the thin unbundled module bridge owners
  `Module.IsMPseudoCoherentRelativeTo R A M` and
  `Module.IsPseudoCoherentRelativeTo R A M`, which reuse the chapter owners on `ModuleCat`;
- primitive data: the bundled module object `ModuleCat.of A M` together with the existing relative
  pseudo-coherence owner from `Definition_15_82_4`;
- derived API: finite / finitely presented / finite-free-resolution criteria obtained by testing
  the restricted module over every surjective polynomial presentation of `A`.

Source/core/bridge triage:
- `source-facing`: the four equivalences of Lemma `15.82.7`;
- `core/canonical`: `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `Module.FinitePresentationRelativeTo`,
  `Module.HasLengthFiniteFreeResolution`,
  and Lemma `15.65.4`;
- `bridge/view`: the presentationwise finite-free-resolution criteria on the right-hand sides of
  parts `(3)` and `(4)`.

The canonical owner remains the chapter predicate on `ModuleCat`, but the ordinary theorem surface
for unbundled modules should use the thin bridge `Module.IsMPseudoCoherentRelativeTo` /
`Module.IsPseudoCoherentRelativeTo` rather than repeating `ModuleCat.of A M`. -/

-- Proof sketch: for each surjective polynomial presentation `α`, apply Lemma `15.65.4 (1)` over
-- `MvPolynomial (Fin n) R` to identify `0`-pseudo-coherence with finite generation. Finite
-- generation descends and ascends along the surjection `α`, so the pointwise condition is
-- equivalent to finite generation over `A`.
/-- Lemma 15.82.7 (1): an `A`-module is `0`-pseudo-coherent relative to `R` exactly when it is a
finite `A`-module. -/
theorem Module.isZeroPseudoCoherentRelativeTo_iff_finite :
    Module.IsMPseudoCoherentRelativeTo R A M 0 ↔ Module.Finite A M := sorry

-- Proof sketch: apply Lemma `15.65.4 (2)` to each surjective polynomial presentation of `A` over
-- `R`. Then use Lemma `15.81.1` to pass between finite presentation over one presentation and over
-- every presentation.
/-- Lemma 15.82.7 (2): an `A`-module is `(-1)`-pseudo-coherent relative to `R` exactly when it is
finitely presented relative to `R`. -/
theorem Module.isMinusOnePseudoCoherentRelativeTo_iff_finitePresentationRelativeTo :
    Module.IsMPseudoCoherentRelativeTo R A M (-1) ↔
      Module.FinitePresentationRelativeTo R A M := sorry

-- Proof sketch: for each surjective polynomial presentation `α`, apply Lemma `15.65.4 (3)` over
-- the polynomial ring `MvPolynomial (Fin n) R`; this identifies `(-(d : ℤ))`-pseudo-coherence
-- with the existence of a length-`d` finite free resolution over that presentation ring.
/-- Lemma 15.82.7 (3): for `d : ℕ`, an `A`-module is `(-d)`-pseudo-coherent relative to `R`
exactly when for every surjective polynomial presentation of `A` over `R`, the induced module
admits a length-`d` finite free resolution. -/
theorem Module.isNegPseudoCoherentRelativeTo_iff_hasLengthFiniteFreeResolutionRelativeTo
    (d : ℕ) :
    Module.IsMPseudoCoherentRelativeTo R A M (-(d : ℤ)) ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          Module.HasLengthFiniteFreeResolution P M d := sorry

-- Proof sketch: apply Lemma `15.65.4 (4)` over each surjective polynomial presentation of `A`
-- over `R`; the pointwise pseudo-coherence condition is equivalent to the existence of an infinite
-- finite free resolution over every such presentation ring.
/-- Lemma 15.82.7 (4): an `A`-module is pseudo-coherent relative to `R` exactly when for every
surjective polynomial presentation of `A` over `R`, the induced module admits an infinite
resolution by finite free modules. -/
theorem Module.isPseudoCoherentRelativeTo_iff_hasInfiniteFiniteFreeResolutionRelativeTo :
    Module.IsPseudoCoherentRelativeTo R A M ↔
      ∀ n : ℕ,
        let P := MvPolynomial (Fin n) R
        ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
          let _ : Module P M := Module.compHom M α.toRingHom
          ∃ (F : ChainComplex (ModuleCat P) ℕ)
            (π : F ⟶ (ChainComplex.single₀ (ModuleCat P)).obj (ModuleCat.of P M)),
            ChainComplex.IsFiniteFreeResolution π := sorry

end
