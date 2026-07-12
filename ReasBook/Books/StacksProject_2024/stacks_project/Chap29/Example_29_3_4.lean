import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme owners
-- `AlgebraicGeometry.IsImmersion`, `AlgebraicGeometry.IsOpenImmersion`, and
-- `AlgebraicGeometry.IsClosedImmersion`, together with the factorization criterion
-- `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact`. The source example is
-- therefore formalized as an explicit open subscheme of an affine scheme together with a theorem
-- asserting that a closed subscheme of that open does not admit an open-then-closed factorization
-- over the ambient affine scheme.

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/-- A morphism of schemes factors as an open immersion followed by a closed immersion. -/
def HasOpenThenClosedFactorization
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ (middle : Scheme.{u}) (openMap : X ⟶ middle) (closedMap : middle ⟶ Y),
    IsOpenImmersion openMap ∧
      IsClosedImmersion closedMap ∧
      openMap ≫ closedMap = f

/-- Unfolding form of `Scheme.Hom.HasOpenThenClosedFactorization`. -/
theorem hasOpenThenClosedFactorization_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.HasOpenThenClosedFactorization ↔
      ∃ (middle : Scheme.{u}) (openMap : X ⟶ middle) (closedMap : middle ⟶ Y),
        IsOpenImmersion openMap ∧
          IsClosedImmersion closedMap ∧
          openMap ≫ closedMap = f :=
  Iff.rfl

end Scheme.Hom
end AlgebraicGeometry

section

variable (k : Type u) [Field k]

/-- The infinite polynomial ring `k[x_1, x_2, x_3, ...]` from Example 29.3.4. -/
abbrev example2934Ring (k : Type u) [Field k] :=
  MvPolynomial ℕ k

/-- The affine scheme `Spec(k[x_1, x_2, x_3, ...])` from Example 29.3.4. -/
def example2934X : Scheme :=
  Spec <| CommRingCat.of (example2934Ring k)

/-- The variable `x_n` in the infinite polynomial ring of Example 29.3.4. -/
def example2934Variable (n : ℕ) : example2934Ring k :=
  MvPolynomial.X n

/-- The open subset `U = ⋃_{n ≥ 0} D(x_n)` of `Spec(k[x_1, x_2, x_3, ...])` from Example 29.3.4.

Here the indexing is shifted to natural numbers `n : ℕ`, so `x_n` in Lean corresponds to the
textbook variable `x_{n + 1}`. -/
def example2934Open : (example2934X k).Opens :=
  ⨆ n : ℕ,
    (PrimeSpectrum.basicOpen (example2934Variable k n) :
      TopologicalSpace.Opens (PrimeSpectrum (example2934Ring k)))

/-- The open subscheme `U = ⋃_{n ≥ 0} D(x_n)` of `Spec(k[x_1, x_2, x_3, ...])` from
Example 29.3.4. -/
abbrev example2934U : Scheme :=
  (example2934Open k).toScheme

/-- The canonical open immersion `U ⟶ Spec(k[x_1, x_2, x_3, ...])` from Example 29.3.4. -/
abbrev example2934ι : example2934U k ⟶ example2934X k :=
  (example2934Open k).ι

/-- The localization `k[x_1, x_2, x_3, ...][1 / x_n]` used on the chart `D(x_n)` in
Example 29.3.4. -/
abbrev example2934LocalizedRing (n : ℕ) :=
  Localization.Away (example2934Variable k n)

/-- The canonical localization map
`k[x_1, x_2, x_3, ...] → k[x_1, x_2, x_3, ...][1 / x_n]` used in Example 29.3.4. -/
def example2934LocalizationMap (n : ℕ) :
    example2934Ring k →+* example2934LocalizedRing k n :=
  algebraMap (example2934Ring k) (example2934LocalizedRing k n)

/-- The generators defining the localized ideal of Example 29.3.4. -/
def example2934LocalizedIdealGeneratorSet (n : ℕ) : Set (example2934LocalizedRing k n) :=
  {f |
    (∃ i : ℕ,
        i < n ∧
          f =
            example2934LocalizationMap k n ((example2934Variable k i) ^ n)) ∨
      f =
        example2934LocalizationMap k n
          (example2934Variable k n - (1 : example2934Ring k)) ∨
      ∃ m : ℕ,
        n < m ∧
          f =
            example2934LocalizationMap k n (example2934Variable k m)}

/-- The ideal
`(x_0^n, x_1^n, ..., x_{n-1}^n, x_n - 1, x_{n+1}, x_{n+2}, ...)`
inside `k[x_0, x_1, x_2, ...][1 / x_n]` from Example 29.3.4.

As above, the Lean indexing `x_n` is shifted by one from the textbook notation. -/
def example2934LocalizedIdeal (n : ℕ) :
    Ideal (example2934LocalizedRing k n) :=
  Ideal.span (example2934LocalizedIdealGeneratorSet k n)

end

/-- The ring-theoretic obstruction used in Example 29.3.4: the only polynomial whose image lies in
every localized ideal `I_n` is `0`. -/
theorem example2934OnlyZeroMemAllLocalizedIdeals
    (k : Type u) [Field k] (f : example2934Ring k)
    (hf : ∀ n : ℕ,
      example2934LocalizationMap k n f ∈
        example2934LocalizedIdeal k n) :
    f = 0 := sorry

/-- A closed immersion into `U` whose composite into `Spec(k[x_1, x_2, x_3, ...])` is an
immersion but admits no open-then-closed factorization over the ambient affine scheme. -/
structure ImmersionNotOpenThenClosed
    (k : Type u) [Field k] (Z : Scheme) (i : Z ⟶ example2934U k) : Prop where
  /-- The map `i : Z ⟶ U` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion i
  /-- No open-then-closed factorization over `X` exists. -/
  not_hasOpenThenClosedFactorization :
    ¬ (i ≫ example2934ι k).HasOpenThenClosedFactorization

instance {k : Type u} [Field k] {Z : Scheme} {i : Z ⟶ example2934U k}
    (h : ImmersionNotOpenThenClosed k Z i) : IsClosedImmersion i :=
  h.isClosedImmersion

/-- A closed immersion into the open subscheme `U` composes with `U ⟶ X` to an immersion. -/
theorem ImmersionNotOpenThenClosed.isImmersion_comp
    {k : Type u} [Field k] {Z : Scheme} {i : Z ⟶ example2934U k}
    (h : ImmersionNotOpenThenClosed k Z i) :
    IsImmersion (i ≫ example2934ι k) := by
  letI : IsClosedImmersion i := h.isClosedImmersion
  infer_instance

/-- Source-facing companion API for `ImmersionNotOpenThenClosed`: the composite
`Z ⟶ U ⟶ Spec(k[x_1, x_2, x_3, ...])` admits no factorization as an open immersion followed by a
closed immersion. -/
theorem ImmersionNotOpenThenClosed.not_exists_openThenClosedFactorization
    {k : Type u} [Field k] {Z : Scheme} {i : Z ⟶ example2934U k}
    (h : ImmersionNotOpenThenClosed k Z i) :
    ¬ ∃ (middle : Scheme) (openMap : Z ⟶ middle) (closedMap : middle ⟶ example2934X k),
        IsOpenImmersion openMap ∧
          IsClosedImmersion closedMap ∧
          openMap ≫ closedMap = i ≫ example2934ι k := by
  simpa [Scheme.Hom.HasOpenThenClosedFactorization] using
    h.not_hasOpenThenClosedFactorization

section

variable (k : Type u) [Field k]

/-- Example 29.3.4: for the explicit open subscheme
`U = ⋃_{n ≥ 0} D(x_n) ⊆ Spec(k[x_1, x_2, x_3, ...])`, there exists a closed subscheme
`Z ⊆ U` whose composite `Z → U → Spec(k[x_1, x_2, x_3, ...])` is an immersion but cannot be
factored as an open immersion followed by a closed immersion. -/
theorem example2934ExistsImmersionNotOpenThenClosed
    (k : Type u) [Field k] :
    ∃ (Z : Scheme) (i : Z ⟶ example2934U k),
      ImmersionNotOpenThenClosed k Z i := by
  sorry

end
