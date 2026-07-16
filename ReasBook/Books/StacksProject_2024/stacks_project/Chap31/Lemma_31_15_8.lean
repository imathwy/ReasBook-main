import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_13_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Set TopologicalSpace
open scoped BigOperators

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.IdealSheafData

-- Semantic recall: `lean_leansearch` surfaced only ambient ideal-sheaf/subscheme API and no
-- existing weighted-sum owner for effective Cartier divisors in this workspace. Following the
-- local Chapter 31 `X.IdealSheafData` owner, the source sum `\sum a_i D_i` is therefore recorded
-- by the finite-support ideal-sheaf product below, while the codimension-`≥ 2` clause is exposed
-- through the local irreducible-closed-subset owner `irreducibleComponentsCodimAtLeast`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable {ι : Type v}

/-- A subset of the underlying topological space of `X` has irreducible components of codimension
at least `k` if every maximal irreducible closed subset contained in it has `coheight` at least
`k`. This is the local source-facing codimension owner needed for the codimension-`≥ 2` clause of
Lemma `31.15.8`. -/
def irreducibleComponentsCodimAtLeast (k : ℕ) (F : Set X) : Prop :=
  ∀ Z : IrreducibleCloseds X,
    Maximal (fun Y : IrreducibleCloseds X ↦ (Y : Set X) ⊆ F) Z →
      (k : ℕ∞) ≤ Order.coheight Z

/-- Companion expansion for `irreducibleComponentsCodimAtLeast`. -/
theorem irreducibleComponentsCodimAtLeast_iff (k : ℕ) (F : Set X) :
    irreducibleComponentsCodimAtLeast k F ↔
      ∀ Z : IrreducibleCloseds X,
        Maximal (fun Y : IrreducibleCloseds X ↦ (Y : Set X) ⊆ F) Z →
          (k : ℕ∞) ≤ Order.coheight Z := sorry

/-- The finite weighted sum of a family of effective Cartier divisors, expressed in the local
`IdealSheafData` owner by the product of the ideal-sheaf powers indexed by the finite support of
the coefficient function. -/
def effectiveCartierDivisorWeightedSum [DecidableEq ι] (a : ι →₀ ℕ)
    (D : ι → X.IdealSheafData) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals (fun U ↦ a.support.prod fun i ↦ (D i).ideal U ^ a i)

/-- Companion expansion for `effectiveCartierDivisorWeightedSum`. -/
theorem effectiveCartierDivisorWeightedSum_def [DecidableEq ι] (a : ι →₀ ℕ)
    (D : ι → X.IdealSheafData) :
    effectiveCartierDivisorWeightedSum a D =
      Scheme.IdealSheafData.ofIdeals
        (fun U ↦ a.support.prod fun i ↦ (D i).ideal U ^ a i) := sorry

/-- Two closed subschemes of `X` agree away from codimension `2` if they coincide after
restriction to some open subscheme of `X` whose complement in the support of the second subscheme
has irreducible components of codimension at least `2`. -/
def agreesAwayFromCodimensionTwo (D Z : X.IdealSheafData) : Prop :=
  ∃ U : X.Opens,
    D.comap U.ι = Z.comap U.ι ∧
      irreducibleComponentsCodimAtLeast 2 (((Z.support : Set X) \ (U : Set X)) : Set X)

/-- Companion expansion for `agreesAwayFromCodimensionTwo`. -/
theorem agreesAwayFromCodimensionTwo_iff (D Z : X.IdealSheafData) :
    D.agreesAwayFromCodimensionTwo Z ↔
      ∃ U : X.Opens,
        D.comap U.ι = Z.comap U.ι ∧
          irreducibleComponentsCodimAtLeast 2 (((Z.support : Set X) \ (U : Set X)) : Set X) :=
  sorry

/-- `D` is an effective Cartier divisor approximation to `Z` if it is an effective Cartier
divisor containing `Z` and agreeing with `Z` away from codimension `2`. -/
class EffectiveCartierDivisorApproximation (D : X.IdealSheafData)
    (Z : outParam X.IdealSheafData) : Prop extends IsEffectiveCartierDivisor D where
  /-- The original closed subscheme is contained in the approximating divisor. -/
  le : Z ≤ D
  /-- The approximating divisor and the original subscheme agree away from codimension `2`. -/
  agreesAwayFromCodimensionTwo : D.agreesAwayFromCodimensionTwo Z

/-- An effective Cartier divisor approximation is, in particular, an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisorOfEffectiveCartierDivisorApproximation
    (D Z : X.IdealSheafData) [h : EffectiveCartierDivisorApproximation D Z] :
    IsEffectiveCartierDivisor D :=
  h.toIsEffectiveCartierDivisor

/-- Lemma 31.15.8 (1): let `X` be a Noetherian scheme, let `Z ⊆ X` be a closed subscheme, and
assume that set-theoretically the support of `Z` is contained in the union of a closed subset
whose irreducible components all have codimension at least `2` and a family of integral effective
Cartier divisors `D i`. Then there exists a finitely supported coefficient function `a` such that
the weighted sum `\sum a_i D_i` is an effective Cartier divisor contained in `Z` and agreeing with
`Z` away from codimension `2`. -/
@[stacks 0AGB]
theorem exists_effectiveCartierDivisorWeightedSum_le_and_agreesAwayFromCodimensionTwo
    [DecidableEq ι] (Z : X.IdealSheafData) (D : ι → X.IdealSheafData)
    (hCartier : ∀ i, IsEffectiveCartierDivisor (D i))
    (hIntegral : ∀ i, IsIntegral (D i).subscheme)
    (Z' : Set X) (hZ'closed : IsClosed Z')
    (hZ'codim : irreducibleComponentsCodimAtLeast 2 Z')
    (hcover : (Z.support : Set X) ⊆ Z' ∪ ⋃ i, ((D i).support : Set X)) :
    ∃ a : ι →₀ ℕ,
      EffectiveCartierDivisorApproximation (effectiveCartierDivisorWeightedSum a D) Z := sorry

/-- Lemma 31.15.8 (2): if `Z ⊆ X` is nowhere dense and every stalk `\mathcal O_{X,x}` with
`x ∈ Z` is a unique factorization domain, then there exists an effective Cartier divisor contained
in `Z` and agreeing with `Z` away from codimension `2`. This is the direct source-facing corollary
of the divisor-family existence statement in the textbook lemma. -/
@[stacks 0AGB]
theorem exists_effectiveCartierDivisor_le_and_agreesAwayFromCodimensionTwo_of_nowhereDense_of_stalks_uniqueFactorizationMonoid
    (Z : X.IdealSheafData) (hnowhere : IsNowhereDense (Z.support : Set X))
    (hUFD : ∀ x : X, x ∈ Z.support → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ D : X.IdealSheafData, EffectiveCartierDivisorApproximation D Z := sorry

/-- Lemma 31.15.8 (3): if `Z ⊆ X` is nowhere dense and every stalk `\mathcal O_{X,x}` is a
regular local ring, then there exists an effective Cartier divisor contained in `Z` and agreeing
with `Z` away from codimension `2`. This is the regular-case corollary of the source lemma. -/
@[stacks 0AGB]
theorem exists_effectiveCartierDivisor_le_and_agreesAwayFromCodimensionTwo_of_nowhereDense_of_regular
    (Z : X.IdealSheafData) (hnowhere : IsNowhereDense (Z.support : Set X))
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ D : X.IdealSheafData, EffectiveCartierDivisorApproximation D Z := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
