import Mathlib
import stacks_project.Chap10.Lemma_10_55_6
import stacks_project.Chap15.Lemma_15_79_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "K₀" => projectiveGrothendieckGroup R

/- Domain-style sampling for Lemma 15.120.1:
- primary domain: Euler characteristics of perfect objects in the derived category, valued in the
  Grothendieck group of finite projective modules;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.DPerf`,
  `projectiveGrothendieckGroup`,
  `CategoryTheory.TriangulatedK0`;
- best owner abstraction:
  the source-facing notion here is an Euler-characteristic value attached to an object of the
  perfect derived category `DPerf R`, while the canonical later owner for the comparison theorem is
  the additive `K₀`-equivalence in Lemma `15.120.2`;
- primitive vs. derived:
  primitive data are a bounded finite-projective representative together with its canonical
  complex-level alternating sum in `K₀(R)`;
  interval formulas, the perfect-complex value predicate, and the canonical Euler characteristic
  with its shift/additivity lemmas are derived API built from that owner and the uniqueness
  statement;
- source/core/bridge triage:
  `source-facing`: the value predicate and its uniqueness statement for a perfect complex;
  `core/canonical`: `DPerf`, `projectiveGrothendieckGroup`, and later `TriangulatedK0`;
  `bridge/view`: the bounded finite-projective representative witnessing a source-facing value,
    together with its complex-level Euler characteristic.

The public source-facing predicate should therefore live on the chapter owner `DPerf` rather than
as a parallel global "perfect complex" wrapper name. -/

namespace CochainComplex

/-- The alternating-sum Euler-characteristic class of a bounded finite-projective cochain complex,
written canonically as a `finsum` in `K₀(R)`. -/
noncomputable def eulerCharacteristic
    (L : Cpx) [hL : IsBoundedFiniteProjective L] : projectiveGrothendieckGroup R :=
  ∑ᶠ i : ℤ,
    i.negOnePow •
      projectiveGrothendieckGroupOf R
        ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩

/-- If an interval `[a, b]` contains all nonzero terms of a bounded finite-projective complex,
its canonical Euler-characteristic class is the corresponding finite alternating sum. -/
theorem eulerCharacteristic_eq_sum_Icc
    (L : Cpx) [hL : IsBoundedFiniteProjective L] {a b : ℤ}
    (hge : L.IsStrictlyGE a) (hle : L.IsStrictlyLE b) :
    L.eulerCharacteristic =
      Finset.sum (Finset.Icc a b) fun i ↦
        i.negOnePow •
          projectiveGrothendieckGroupOf R
            ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩ := sorry

end CochainComplex

namespace CategoryTheory.DPerf

open CochainComplex DerivedCategory

/-- A class `c ∈ K₀(R)` is an Euler-characteristic value of a perfect derived `R`-complex `K`
if `K` is represented by a bounded finite-projective complex and `c` is the canonical
Euler-characteristic class of that representative. Equivalently, by
`CochainComplex.eulerCharacteristic_eq_sum_Icc`, `c` is the finite alternating sum over any
interval containing all nonzero terms of the representative. -/
def IsEulerCharacteristicValue
    (K : DPerf R) (c : K₀) : Prop :=
  ∃ (L : Cpx) (_ : K.obj ≅ DerivedCategory.Q.obj L) (_ : IsBoundedFiniteProjective L),
    c = L.eulerCharacteristic

-- Proof sketch: existence comes from choosing any bounded finite-projective representative of the
-- perfect complex and taking the alternating sum of its terms in `K₀(R)`. Uniqueness is the
-- well-definedness argument from the textbook: quasi-isomorphic bounded finite-projective
-- representatives have acyclic cone, and acyclic bounded finite-projective complexes contribute
-- zero in `K₀(R)`.
/-- Lemma 15.120.1: every perfect complex over `R` has a unique Euler-characteristic class in
`K₀(R)`, namely the alternating sum of the terms of any bounded finite-projective representative. -/
theorem existsUnique_isEulerCharacteristicValue
    (K : DPerf R) :
    ∃! c : K₀, K.IsEulerCharacteristicValue c := sorry

/-- The canonical Euler-characteristic class in `K₀(R)` attached to a perfect derived
`R`-complex. -/
noncomputable def eulerCharacteristic
    (K : DPerf R) : K₀ :=
  (K.existsUnique_isEulerCharacteristicValue).choose

/-- The canonical Euler-characteristic class satisfies the defining alternating-sum formula. -/
theorem eulerCharacteristic_spec
    (K : DPerf R) :
    K.IsEulerCharacteristicValue K.eulerCharacteristic := by
  exact (K.existsUnique_isEulerCharacteristicValue).choose_spec.1

/-- Any Euler-characteristic value of a perfect complex agrees with its canonical
Euler-characteristic class. -/
theorem eq_eulerCharacteristic
    {K : DPerf R} {c : K₀}
    (hc : K.IsEulerCharacteristicValue c) :
    c = K.eulerCharacteristic := by
  exact (K.existsUnique_isEulerCharacteristicValue).choose_spec.2 c hc

-- Proof sketch: shift a bounded finite-projective representative by `n`; its terms are the same
-- modules with all degrees translated by `n`, so the alternating sum is multiplied by the
-- canonical sign `(-1)^n`.
/-- Shifting a perfect complex multiplies its Euler-characteristic class by the canonical sign
`(-1)^n`. -/
theorem isEulerCharacteristicValue_shift
    {K : DPerf R} {c : K₀}
    (hc : K.IsEulerCharacteristicValue c) (n : ℤ) :
    (K⟦n⟧).IsEulerCharacteristicValue (n.negOnePow • c) := sorry

-- Proof sketch: the source-facing shift statement applied to the canonical value of `K` produces
-- a value for `K⟦n⟧`; uniqueness for `K⟦n⟧` then identifies that value with the canonical Euler
-- characteristic of the shift.
/-- Shifting a perfect complex multiplies its canonical Euler-characteristic class by the canonical
sign `(-1)^n`. -/
theorem eulerCharacteristic_shift
    (K : DPerf R) (n : ℤ) :
    (K⟦n⟧).eulerCharacteristic = n.negOnePow • K.eulerCharacteristic := sorry

-- Proof sketch: represent a distinguished triangle of perfect complexes by a short exact sequence
-- of bounded finite-projective complexes up to quasi-isomorphism. The termwise short exact
-- sequences split because the terms are projective, so the alternating sums satisfy the desired
-- additivity in `K₀(R)`.
/-- In a distinguished triangle of perfect complexes, the middle Euler-characteristic class is the
sum of the outer two classes. -/
theorem isEulerCharacteristicValue_add_of_distinguishedTriangle
    {T : Triangle (DPerf R)} (hT : T ∈ distTriang (DPerf R))
    {c₁ c₂ c₃ : K₀}
    (hc₁ : T.obj₁.IsEulerCharacteristicValue c₁)
    (hc₂ : T.obj₂.IsEulerCharacteristicValue c₂)
    (hc₃ : T.obj₃.IsEulerCharacteristicValue c₃) :
    c₂ = c₁ + c₃ := sorry

-- Proof sketch: apply the source-facing additivity statement to the canonical values of the
-- three vertices and use uniqueness on each object to identify those values with the owner-level
-- Euler characteristics.
/-- In a distinguished triangle of perfect complexes, the canonical Euler-characteristic classes
are additive. -/
theorem eulerCharacteristic_add_of_distinguishedTriangle
    {T : Triangle (DPerf R)} (hT : T ∈ distTriang (DPerf R)) :
    T.obj₂.eulerCharacteristic = T.obj₁.eulerCharacteristic + T.obj₃.eulerCharacteristic := sorry

end CategoryTheory.DPerf

end
