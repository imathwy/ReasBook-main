import Mathlib
import StacksProject_2024.Chap10.Definition_10_125_1
import StacksProject_2024.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]
variable {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)

/-
Domain-style sampling:
- primary domain: explicit polynomial presentations under localization away from one element;
- sampled owner declarations:
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.localizationAway`,
  `Algebra.Presentation.localizationAway`,
  `Algebra.Presentation.relation_comp_localizationAway_inl`;
- best owner abstraction:
  `Algebra.IsRelativeGlobalCompleteIntersection` remains the owner of the property, while the
  explicit quotient obtained by adjoining an inverse is the source-facing bridge/view for this
  lemma;
- primitive vs. derived:
  the primitive source-facing data are `h`, `g`, the explicit quotient presentation, and the
  comparison `Localization.Away g ≃ₐ[R] ...`; the relative-global-complete-intersection property
  should then be stated on that displayed quotient ring itself.
-/

local notation "PresentedIdeal" =>
  Ideal.span (Set.range f)

local notation "PresentedAlgebra" =>
  MvPolynomial (Fin n) R ⧸ PresentedIdeal

local notation "LocalizedPresentedAlgebra" =>
  fun h : MvPolynomial (Fin n) R ↦
    MvPolynomial (Fin (n + 1)) R ⧸
      Ideal.span
        (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
          {rename Fin.castSuccEmb h * X (Fin.last n) - 1})

-- Proof sketch: apply Lemma `10.125.6` to the quotient map `(R / I) → (S / IS)` to find a basic
-- open neighbourhood of `V (IS)` on which all fibers have dimension at most `n - c`; choose
-- `g` cutting out the complementary closed set so that `g = 1` in `S / IS`, lift `g` to some
-- `h` in the polynomial ring, and use the standard presentation of `S_g` by adjoining an inverse
-- for `h` together with Definition `10.136.5`.
/-- Lemma 10.136.10 (1): if all fibers of `Spec (S / IS) → Spec (R / I)` have dimension `n - c`
for `S = R[x_1, \ldots, x_n] / (f_1, \ldots, f_c)`, then there exist `h` in the polynomial ring
and its image `g` in `S` such that `g = 1` in `S / IS`, the localization `S_g` is identified with
the explicit quotient obtained by adjoining an inverse for `h`, and that displayed quotient is a
relative global complete intersection over `R`. -/
theorem exists_relativeGlobalCompleteIntersection_localizationAway_of_fiberDimension_on_closedSet
    (I : Ideal R)
    (hdim : ∀ p : PrimeSpectrum R,
      I ≤ p.asIdeal →
        Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
          ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (_ : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        Ideal.Quotient.mk (Ideal.map (algebraMap R PresentedAlgebra) I) g = 1 ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := sorry

-- Proof sketch: apply Lemma `10.125.6` to the fiber over `p` to obtain a basic open
-- neighbourhood of `Spec (S ⊗[R] κ(p))` on which all fibers have dimension at most `n - c`;
-- choose `g` whose image in the fiber ring is a unit, lift it to some `h`, and identify `S_g`
-- with the quotient obtained by adjoining an inverse for `h`, which is then a relative global
-- complete intersection by Definition `10.136.5`.
/-- Lemma 10.136.10 (2): if `dim (S ⊗[R] κ(p)) = n - c` for
`S = R[x_1, \ldots, x_n] / (f_1, \ldots, f_c)`, then there exist `h` in the polynomial ring and
its image `g` in `S` such that `g` becomes a unit in the fiber over `p`, the localization `S_g`
is identified with the explicit quotient obtained by adjoining an inverse for `h`, and that
displayed quotient is a relative global complete intersection over `R`. -/
theorem exists_relativeGlobalCompleteIntersection_localizationAway_of_fiberDimension_atPrime
    (p : PrimeSpectrum R)
    (hdim : ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (_ : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        IsUnit (1 ⊗ₜ[R] g : p.asIdeal.Fiber PresentedAlgebra) ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := sorry

-- Proof sketch: use Lemma `10.125.6` at the prime `q` to find a principal open neighbourhood on
-- which the relative dimension is at most `n - c`; choose a generator `g` of that neighbourhood
-- with `g ∉ q`, lift it to some `h` in the polynomial ring, and then use the standard
-- localization presentation together with Definition `10.136.5`.
/-- Lemma 10.136.10 (3): if `dim_q (S / R) = n - c` for
`S = R[x_1, \ldots, x_n] / (f_1, \ldots, f_c)`, then there exist `h` in the polynomial ring and
its image `g` in `S` with `g ∉ q` such that the localization `S_g` is identified with the
explicit quotient obtained by adjoining an inverse for `h`, and that displayed quotient
presentation is a relative global complete intersection over `R`. -/
theorem exists_relativeGlobalCompleteIntersection_localizationAway_of_relativeDimensionAt
    (q : PrimeSpectrum PresentedAlgebra)
    (hdim : relativeDimensionAt R PresentedAlgebra q = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (_ : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        g ∉ q.asIdeal ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := sorry

end
