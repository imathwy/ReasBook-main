import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_116_1 (from Chap15) -/
/-
Domain-style sampling for Definition 15.116.1:
- primary domain: weakly unramified and formally smooth localized branches arising from reduced
  tensor-product base change for extensions of discrete valuation rings;
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings.WeaklyUnramified`,
  `IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal`,
  `RingHom.formally_smooth_for_adic`,
  `isExtensionOfDiscreteValuationRings_localizationBranch`;
- best owner abstraction: the source-facing predicates `IsWeakSolutionFor` and `IsSolutionFor`
  should quantify over maximal branches with the canonical localized branch algebra from Remark
  `15.115.1`; the weak-solution predicate uses `WeaklyUnramified` directly, the solution
  predicate uses `RingHom.formally_smooth_for_adic`, and the maximal-ideal equality remains a
  companion bridge theorem rather than primitive public data;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, the fraction
  fields `K ⊂ L`, and the finite extension `K₁ / K`; the localized branch extension structure and
  its ramification/smoothness properties are derived API.

Source/core/bridge triage:
- `source-facing`: `IsWeakSolutionFor`, `IsSolutionFor`, `IsSeparableSolutionFor`;
- `core/canonical`: `WeaklyUnramified`, `RingHom.formally_smooth_for_adic`,
  `Localization.localRingHom`;
- `bridge/view`: `IsWeakSolutionFor.map_maximalIdeal`.
-/

open scoped TensorProduct
open IsExtensionOfDiscreteValuationRings
open IsLocalRing

universe u v w x y

noncomputable section

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra K K1] [Algebra A K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance : CommRing A1 :=
  inferInstance

local instance : CommRing L1 :=
  Ideal.Quotient.commRing _

local instance : CommRing B1 :=
  inferInstance

private noncomputable instance localizedBranchAlgebra
    (p : Ideal A1) [p.IsPrime] (q : Ideal B1) [q.IsPrime] [q.LiesOver p] :
    Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
  (Localization.localRingHom p q (algebraMap A1 B1) (q.over_def p)).toAlgebra

private def IsWeakSolutionBranch
    (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p] :
    Prop :=
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    localizedBranchAlgebra p q
  let _ : IsExtensionOfDiscreteValuationRings
      (Localization.AtPrime p) (Localization.AtPrime q) :=
    isExtensionOfDiscreteValuationRings_localizationBranch p q
  WeaklyUnramified (Localization.AtPrime p) (Localization.AtPrime q)

private def IsSolutionBranch
    (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p] :
    Prop :=
  (Localization.localRingHom p q (algebraMap A1 B1) (q.over_def p)).formally_smooth_for_adic
    (maximalIdeal (Localization.AtPrime q))

variable (A) (B) (K) (L) (K1) in
/-- Definition 15.116.1: a finite field extension `K₁ / K` is a weak solution for `A ⊂ B` if for
every maximal ideal `p` of `A₁ = integralClosure A K₁` and every maximal ideal `q` of
`B₁ = integralClosure B ((L ⊗[K] K₁)_red)` lying over `p`, the localized extension
`(A₁)_p ⊂ (B₁)_q` is weakly unramified. -/
def IsWeakSolutionFor : Prop :=
  ∀ (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p],
    IsWeakSolutionBranch p q

variable (A) (B) (K) (L) (K1) in
/-- A finite field extension `K₁ / K` is a solution for `A ⊂ B` if every localized extension
`(A₁)_p ⊂ (B₁)_q` from Remark `15.115.1` is formally smooth for the `q`-adic topology. -/
def IsSolutionFor : Prop :=
  ∀ (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p],
    IsSolutionBranch p q

variable (A) (B) (K) (L) (K1) in
/-- Companion bridge: the weak-solution condition is equivalent to the maximal-ideal equality on
each localized branch. -/
theorem isWeakSolutionFor_iff_map_maximalIdeal :
    IsWeakSolutionFor A B K L K1 ↔
      ∀ (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p],
        Ideal.map
            (Localization.localRingHom p q (algebraMap A1 B1) (q.over_def p))
            (maximalIdeal (Localization.AtPrime p)) =
          maximalIdeal (Localization.AtPrime q) := by
  sorry

variable (A) (B) (K) (L) (K1) in
/-- A separable solution is a solution for `A ⊂ B` whose field extension `K₁ / K` is separable. -/
def IsSeparableSolutionFor : Prop :=
  IsSolutionFor A B K L K1 ∧ Algebra.IsSeparable K K1

end

/-! ### Example_15_116_2 (from Chap15) -/
noncomputable section

universe u v

open IsLocalRing PowerSeries
open scoped UniformizerRoot

/-
Domain-style sampling for Example `15.116.2`.

- primary domain: finite base change of extensions of discrete valuation rings, specialized to the
  canonical radical extension `k[[x]] ⊂ k[[x]][x^{1/p}]`;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `IsSolutionFor`,
  `uniformizerRootExtensionRing`,
  `uniformizerRootExtensionField`;
- best owner abstraction: the source-facing example should reuse the chapter owners
  `IsWeakSolutionFor` / `IsSolutionFor` from `Definition_15_116_1` and the radical-extension owner
  API from `Lemma_15_115_2`, rather than rebuilding parallel local algebra/module wrappers;
- primitive-vs-derived split: the primitive data here are the power-series DVR `A = k[[x]]`, the
  canonical radical extension ring/field `A[π^(1/p)]` and `K[π^(1/p)]`, and the base-change field
  `K₁`; field, module, finite-dimensionality, DVR, fraction-field, and extension-of-DVR structure
  on `A[π^(1/p)]` and `K[π^(1/p)]` are derived API from the upstream owners.

Source/core/bridge triage:
- `source-facing`: the two example theorems about weak solutions and solutions for
  `k[[x]] ⊂ k[[x]][x^{1/p}]`;
- `core/canonical`: `IsWeakSolutionFor`, `IsSolutionFor`, `uniformizerRootExtensionRing`,
  `uniformizerRootExtensionField`;
- `bridge/view`: the owner-provided radical-extension tower, fraction-field, and
  `IsExtensionOfDiscreteValuationRings` bridges, specialized here to `π = X`.
-/

section

variable (k : Type u) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]

local notation "A" => PowerSeries k
local notation "K" => FractionRing A
local notation "π" => (X : A)

private lemma hp : 2 ≤ p :=
  Nat.Prime.two_le (Fact.out : Nat.Prime p)

omit [PerfectField k] in
private lemma hπ : Irreducible π :=
  (maximalIdeal_eq_span_singleton_iff_irreducible π).mp PowerSeries.maximalIdeal_eq_span_X

section BaseChange

variable (K₁ : Type v) [Field K₁] [Algebra (PowerSeries k) K₁]
variable [Algebra (FractionRing (PowerSeries k)) K₁]
variable [IsScalarTower (PowerSeries k) (FractionRing (PowerSeries k)) K₁]
variable [FiniteDimensional (FractionRing (PowerSeries k)) K₁]

local notation "B" => uniformizerRootExtensionRing π p
local notation "L" => uniformizerRootExtensionField π p

local instance : Fact (Irreducible π) := ⟨hπ k⟩

local instance : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : Nat.Prime p)⟩

local instance : Field L :=
  uniformizerRootExtensionField_field (hπ k)

local instance : Algebra K L :=
  uniformizerRootExtensionField_algebra

local instance : Algebra A L :=
  uniformizerRootExtensionField_baseAlgebra

local instance : IsScalarTower A K L :=
  uniformizerRootExtensionField_isScalarTower

local instance : FiniteDimensional (FractionRing A) (uniformizerRootExtensionField π p) :=
  uniformizerRootExtensionField_finiteDimensional
    (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))

local instance : IsDomain B :=
  uniformizerRootExtensionRing_isDomain

local instance : IsDiscreteValuationRing B :=
  uniformizerRootExtensionRing_isDiscreteValuationRing

local instance : Algebra B L :=
  uniformizerRootExtensionRingToField_algebra

local instance : IsScalarTower A B L :=
  uniformizerRootExtensionRingToField_isScalarTower

local instance : IsIntegralClosure B A L :=
  uniformizerRootExtensionRing_isIntegralClosure (hπ k) (hp p)

local instance : IsFractionRing B L :=
  uniformizerRootExtensionRing_isFractionRing

local instance : IsExtensionOfDiscreteValuationRings A B :=
  uniformizerRootExtensionRing_isExtensionOfDiscreteValuationRings
    (hπ k) (hp p)

-- Proof sketch: if `K₁ / k((x))` were separable, then the canonical radical extension
-- `k[[x]] ⊂ k[[x]][x^{1/p}]` would remain outside the weak-solution range from
-- Definition `15.116.1`: after base change, every local branch still has ramification index
-- divisible by `p`, so no weak solution exists.
/-- Example 15.116.2 (1): for a perfect field `k` of characteristic `p > 0`, any weak solution for
the canonical extension `k[[x]] ⊂ k[[x]][x^{1/p}]` is inseparable over `k((x))`. -/
theorem not_isSeparable_of_weakSolutionForPowerSeriesPthRoot
    (hWeak : IsWeakSolutionFor A A[π^(1/p)] K K[π^(1/p)] K₁) :
    ¬ Algebra.IsSeparable K K₁ := sorry

-- Proof sketch: for a finite inseparable extension `K₁ / k((x))`, the canonical pth-root
-- extension `k[[x]] ⊂ k[[x]][x^{1/p}]` becomes a solution in the sense of
-- Definition `15.116.1`: the inseparability forces the local branches after base change to be
-- formally smooth over the localized normalization.
/-- Example 15.116.2 (2): every finite inseparable extension of `k((x))` is a solution for the
canonical extension `k[[x]] ⊂ k[[x]][x^{1/p}]`. -/
theorem isSolutionForPowerSeriesPthRoot_of_not_isSeparable
    (hK₁ : ¬ Algebra.IsSeparable K K₁) :
    IsSolutionFor A A[π^(1/p)] K K[π^(1/p)] K₁ := sorry

end BaseChange
end

/-! ### Lemma_15_116_3 (from Chap15) -/
open Ideal IsLocalRing
open scoped TensorProduct

universe u v w

open IsExtensionOfDiscreteValuationRings

section

/-
Domain-style sampling for Lemma 15.116.3:
- primary domain: weakly unramified extensions of discrete valuation rings after base change along
  a finite separable totally ramified fraction-field extension;
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings`,
  `WeaklyUnramified`,
  `IsTotallyRamifiedWithRespectTo`,
  `integralClosure`;
- best owner abstraction: the chapter owners `IsExtensionOfDiscreteValuationRings`,
  `WeaklyUnramified`, and `IsTotallyRamifiedWithRespectTo`, with the integral closure
  `A1 = integralClosure A K1` as the owner ring for clause `(2)` and the tensor-product rings
  `L1 = L ⊗[K] K1` and `B1 = A1 ⊗[A] B` as the bridge objects for the base-change clauses;
- primitive-vs-derived split: the primitive data for clause `(2)` are the DVR `A`, the finite
  separable totally ramified extension `K1 / K`, and the integral closure `A1`; the additional DVR
  extension `A ⊆ B`, fraction field `L`, and the field/domain/DVR structures on `L1` and `B1` are
  only needed for clauses `(1)`, `(3)`, and `(4)`.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma 15.116.3;
- `core/canonical`: `IsExtensionOfDiscreteValuationRings`, `WeaklyUnramified`,
  `IsTotallyRamifiedWithRespectTo`, and `integralClosure`;
- `bridge/view`: the tensor-product rings `L1` and `B1`.
-/

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section IntegralClosure

variable {A : Type u} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K1] [Algebra A K1]
variable [Algebra (FractionRing A) K1] [IsScalarTower A (FractionRing A) K1]
variable [FiniteDimensional (FractionRing A) K1]
variable [Algebra.IsSeparable (FractionRing A) K1]
variable [IsTotallyRamifiedWithRespectTo A K1]

local notation "A1" => integralClosure A K1

/-- Lemma 15.116.3 (2): for a finite separable extension `K1 / FractionRing A` totally ramified
with respect to `A`, the integral closure `A1 = integralClosure A K1` is a discrete valuation
ring. -/
instance integralClosure_isDiscreteValuationRing_of_totallyRamified :
    IsDiscreteValuationRing A1 := sorry

end IntegralClosure

section WeaklyUnramifiedBaseChange

variable {A : Type u} {B : Type v} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
variable [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A B L] [IsScalarTower A (FractionRing A) L]
variable [Field K1] [Algebra A K1]
variable [Algebra (FractionRing A) K1] [IsScalarTower A (FractionRing A) K1]
variable [FiniteDimensional (FractionRing A) K1]
variable [Algebra.IsSeparable (FractionRing A) K1]
variable [IsTotallyRamifiedWithRespectTo A K1] [WeaklyUnramified A B]

local notation "K" => FractionRing A
local notation "A1" => integralClosure A K1
local notation "L1" => L ⊗[K] K1
local notation "B1" => A1 ⊗[A] B

-- Proof sketch: a finite separable totally ramified extension of the fraction field of a DVR has
-- trivial residue-field extension, so after tensoring with a weakly unramified extension the
-- tensor product stays local on the generic fiber. Equivalently, the unique prolongation of the
-- valuation from `K` to `K1` forces `L ⊗[K] K1` to have a single factor, hence it is a field.
/-- Lemma 15.116.3 (1): if `A ⊆ B` is a weakly unramified extension of discrete valuation rings
with fraction fields `K ⊆ L`, and `K1 / K` is finite separable and totally ramified with respect
to `A`, then `L1 = L ⊗[K] K1` is a field. -/
instance tensorProduct_fractionField_isField_of_weaklyUnramified_of_totallyRamified :
    IsField L1 := sorry

/-- The base-changed tensor product `B1 = A1 ⊗[A] B` is a domain when `A ⊆ B` is weakly
unramified. -/
instance tensorProduct_integralClosure_isDomain_of_weaklyUnramified_of_totallyRamified :
    IsDomain B1 := sorry

/-- Lemma 15.116.3 (3): if `A ⊆ B` is weakly unramified and `K1 / K` is totally ramified with
respect to `A`, then the base change `B1 = A1 ⊗[A] B` is a discrete valuation ring. -/
instance tensorProduct_integralClosure_isDiscreteValuationRing_of_weaklyUnramified_of_totallyRamified :
    IsDiscreteValuationRing B1 := sorry

/-- The canonical map `A1 → B1` obtained by base-changing `A → B` along `A → A1` is again an
extension of discrete valuation rings when `A ⊆ B` is weakly unramified. -/
instance isExtensionOfDiscreteValuationRings_integralClosure_tensorProduct_of_weaklyUnramified_of_totallyRamified :
    IsExtensionOfDiscreteValuationRings A1 B1 := sorry

-- Proof sketch: after (2) and (3), the extension `A1 ⊆ B1` is an extension of discrete valuation
-- rings by the preceding theorem. Total ramification of `K1 / K` leaves the ramification index
-- of `A ⊆ B` unchanged, so the ramification index remains `1` after passing to `A1 ⊆ B1`.
/-- Lemma 15.116.3 (4): with `A1 = integralClosure A K1` and `B1 = A1 ⊗[A] B`, the base-changed
extension `A1 ⊆ B1` is weakly unramified. -/
theorem weaklyUnramified_tensorProduct_integralClosure_of_totallyRamified :
    WeaklyUnramified A1 B1 := sorry

end WeaklyUnramifiedBaseChange

end

/-! ### Lemma_15_116_4 (from Chap15) -/
open IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped TensorProduct

universe u v w x y z

/- Domain-style sampling for Lemma 15.116.4:
- primary domain: finite base change of extensions of discrete valuation rings, organized around
  the chapter solution predicates and reduced tensor-product field-factor decompositions;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `IsSolutionFor`,
  `exists_fractionRingTensorProduct_decomposition_with_unramifiedFactors`,
  `isExtensionOfDiscreteValuationRings_localizationBranch`;
- best owner abstraction: the source-facing solution predicates are already owned by
  `Definition_15_116_1`, so this file should reuse `IsWeakSolutionFor` / `IsSolutionFor` directly;
  the reduced tensor-product decomposition hypothesis is only bridge/view data and should be
  stated with the canonical `L`-algebra product decomposition shape used nearby in
  `Lemma_15_115_9`;
- primitive-vs-derived split: the primitive data are the DVR tower `A ⊂ B ⊂ C`, fraction fields
  `K ⊂ L ⊂ M`, the finite extension `K₁ / K`, and a decomposition of `((L ⊗[K] K₁)_red)` into
  field factors; the weak/solution conditions on those factors are derived API via the chapter
  owners.

Source/core/bridge triage:
- `source-facing`: the four ascent/descent theorems of Lemma `15.116.4`;
- `core/canonical`: `IsWeakSolutionFor` and `IsSolutionFor` from `Definition_15_116_1`;
- `bridge/view`: the explicit `L`-algebra product decomposition hypotheses for
  `((L ⊗[K] K₁)_red)`, which relate its field factors to the chapter solution predicates for
  `B ⊂ C`.
-/

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type z} {K1 : Type (max x y z)}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra B M] [Algebra C M] [Algebra K M] [Algebra L M]
variable [IsFractionRing C M]
variable [IsScalarTower A C M] [IsScalarTower A K M]
variable [IsScalarTower B C M] [IsScalarTower B L M]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)

-- Proof sketch: localize the integral closure `A1 = integralClosure A K1` at a maximal ideal and
-- compare the corresponding branches of `A1 ⊗[A] B` and `A1 ⊗[A] C`. If the branch over `C` is
-- weakly unramified, then every intermediate local extension of discrete valuation rings remains
-- weakly unramified by multiplicativity of ramification indices in towers.
/-- Lemma 15.116.4 (1): if `K1 / K` is a weak solution for `A → C`, then it is a weak solution for
`A → B`. -/
theorem weakSolutionFor_of_weakSolutionFor_comp
    (hK1 : IsWeakSolutionFor A C K M K1) :
    IsWeakSolutionFor A B K L K1 := sorry

-- Proof sketch: use the weak-solution descent from the previous clause together with
-- Lemma `15.112.5`: separability of the residue-field extension for the branch over `C` implies
-- separability for the intermediate branch over `B`, so every solution branch over `C` yields a
-- solution branch over `B`.
/-- Lemma 15.116.4 (2): if `K1 / K` is a solution for `A → C`, then it is a solution for `A → B`.
-/
theorem solutionFor_of_solutionFor_comp
    (hK1 : IsSolutionFor A C K M K1) :
    IsSolutionFor A B K L K1 := sorry

-- Proof sketch: write `L1 = ((L ⊗[K] K1)_red)` as a finite product of fields by hypothesis. For
-- each factor field, choose the corresponding weak solution branch for `B → C`, and combine it
-- with the given weak solution branches for `A → B`. The local tower criterion for ramification
-- indices then shows that the induced branches for `A → C` are weakly unramified.
/-- Lemma 15.116.4 (3): if `K1 / K` is a weak solution for `A → B` and
`((L ⊗[K] K1)_red)` is a product of fields that are weak solutions for `B → C`, then `K1 / K` is
a weak solution for `A → C`. -/
theorem weakSolutionFor_comp_of_weakSolutionFor_of_reducedTensorProductFactors
    (hAB : IsWeakSolutionFor A B K L K1)
    (hBC :
      ∃ (ι : Type u) (_ : Fintype ι) (F : ι → Type (max u v w x y))
        (_ : ∀ i, Field (F i))
        (_ : ∀ i, Algebra B (F i))
        (_ : ∀ i, Algebra L (F i))
        (_ : ∀ i, IsScalarTower B L (F i))
        (_ : ∀ i, FiniteDimensional L (F i)),
        Nonempty (L1 ≃ₐ[L] ∀ i, F i) ∧ ∀ i, IsWeakSolutionFor B C L M (F i)) :
    IsWeakSolutionFor A C K M K1 := sorry

-- Proof sketch: refine the preceding ascent argument with Lemma `15.112.5`: the factor branches
-- for `B → C` have separable residue-field extensions, and separability is preserved when passing
-- to the composite local branch over `A`. Together with weakly unramifiedness, this yields a
-- solution branch for `A → C`.
/-- Lemma 15.116.4 (4): if `K1 / K` is a solution for `A → B` and `((L ⊗[K] K1)_red)` is a
product of fields that are solutions for `B → C`, then `K1 / K` is a solution for `A → C`. -/
theorem solutionFor_comp_of_solutionFor_of_reducedTensorProductFactors
    (hAB : IsSolutionFor A B K L K1)
    (hBC :
      ∃ (ι : Type u) (_ : Fintype ι) (F : ι → Type (max u v w x y))
        (_ : ∀ i, Field (F i))
        (_ : ∀ i, Algebra B (F i))
        (_ : ∀ i, Algebra L (F i))
        (_ : ∀ i, IsScalarTower B L (F i))
        (_ : ∀ i, FiniteDimensional L (F i)),
        Nonempty (L1 ≃ₐ[L] ∀ i, F i) ∧ ∀ i, IsSolutionFor B C L M (F i)) :
    IsSolutionFor A C K M K1 := sorry

end

/-! ### Lemma_15_116_5 (from Chap15) -/
open IsLocalRing

universe u v w x uA vA wA xA

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

/- Domain-style sampling for Lemma 15.116.5:
- primary domain: ramification-eliminating base change for extensions of discrete valuation
  rings, expressed through the chapter solution predicates and strict-henselization existence;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `IsSolutionFor`,
  `IsSeparableSolutionFor`,
  `IsStrictHenselizationOf`;
- best owner abstraction: the solution notions already belong to the chapter owners from
  `Definition_15_116_1`, so this lemma should remain a source-facing existence theorem relating
  those owners rather than introduce a second bundled square owner;
- primitive-vs-derived split: the primitive witness data are the DVR extensions `A → A'`,
  `B → B'`, `A' → B'`, the compatible fraction fields `K'`, `L'`, and the residue-field
  comparison algebras; the three descent clauses are derived API and should therefore be phrased
  directly with `IsWeakSolutionFor`, `IsSolutionFor`, and `IsSeparableSolutionFor`.

Source/core/bridge triage:
- `source-facing`: the existence theorem for a ramification-eliminating square;
- `core/canonical`: `IsWeakSolutionFor`, `IsSolutionFor`, `IsSeparableSolutionFor`, and the
  strict-henselization owner `IsStrictHenselizationOf` used in the proof sketch;
- `bridge/view`: the explicit existential witness rings and fields together with their algebraic
  and residue-field comparison properties.
-/

-- Proof sketch: choose `A'` as a directed colimit of finite étale local extensions of `A` whose
-- residue field is a separable closure of `ResidueField A`, choose `B'` as a strict henselization
-- of `B`, and use the strict-henselian lifting lemma to produce the commutative square. The
-- fraction-field and residue-field conditions come from the chosen constructions together with the
-- canonical tower compatibilities for the induced comparison maps, while descent of weak
-- solutions, solutions, and separable solutions follows by approximating a solution over
-- `A' → B'` at a finite étale stage and then applying Lemma `15.116.4`.
/-- Lemma 15.116.5: for an extension `A → B` of discrete valuation rings with fraction fields
`K ⊂ L`, there exist extensions of discrete valuation rings `A → A'`, `B → B'`, and
`A' → B'` with compatible induced maps on fraction fields and residue fields such that `K' / K`
and `L' / L` are separable algebraic, the residue fields of `A'` and `B'` are separable closures
of those of `A` and `B`, and the existence of a weak solution, a solution, or a separable
solution for `A' → B'` implies the corresponding existence statement for `A → B`. -/
theorem exists_ramificationEliminationSquare :
    ∃ (Aprime : Type uA) (_ : CommRing Aprime) (_ : IsDomain Aprime)
      (_ : IsDiscreteValuationRing Aprime) (_ : Algebra A Aprime)
      (_ : IsExtensionOfDiscreteValuationRings A Aprime)
      (Bprime : Type vA) (_ : CommRing Bprime) (_ : IsDomain Bprime)
      (_ : IsDiscreteValuationRing Bprime) (_ : Algebra B Bprime) (_ : Algebra Aprime Bprime)
      (_ : Algebra A Bprime) (_ : IsScalarTower A Aprime Bprime) (_ : IsScalarTower A B Bprime)
      (_ : IsExtensionOfDiscreteValuationRings B Bprime)
      (_ : IsExtensionOfDiscreteValuationRings Aprime Bprime)
      (Kprime : Type wA) (_ : Field Kprime) (_ : Algebra Aprime Kprime)
      (_ : IsFractionRing Aprime Kprime) (_ : Algebra K Kprime) (_ : Algebra A Kprime)
      (_ : IsScalarTower A Aprime Kprime) (_ : IsScalarTower A K Kprime)
      (Lprime : Type xA) (_ : Field Lprime) (_ : Algebra Bprime Lprime)
      (_ : IsFractionRing Bprime Lprime) (_ : Algebra L Lprime) (_ : Algebra B Lprime)
      (_ : IsScalarTower B Bprime Lprime) (_ : IsScalarTower B L Lprime)
      (_ : Algebra Kprime Lprime) (_ : Algebra Aprime Lprime)
      (_ : IsScalarTower Aprime Bprime Lprime) (_ : IsScalarTower Aprime Kprime Lprime)
      (_ : Algebra (ResidueField A) (ResidueField Aprime))
      (_ : Algebra (ResidueField B) (ResidueField Bprime))
      (_ : Algebra (ResidueField Aprime) (ResidueField Bprime))
      (_ : Algebra (ResidueField A) (ResidueField Bprime))
      (_ : IsScalarTower (ResidueField A) (ResidueField Aprime) (ResidueField Bprime))
      (_ : IsScalarTower (ResidueField A) (ResidueField B) (ResidueField Bprime)),
      Algebra.IsAlgebraic K Kprime ∧
        Algebra.IsSeparable K Kprime ∧
        Algebra.IsAlgebraic L Lprime ∧
        Algebra.IsSeparable L Lprime ∧
        IsSepClosure (ResidueField A) (ResidueField Aprime) ∧
        IsSepClosure (ResidueField B) (ResidueField Bprime) ∧
        ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
            (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
            (_ : IsScalarTower Aprime Kprime K1prime)
            (_ : FiniteDimensional Kprime K1prime),
            IsWeakSolutionFor Aprime Bprime Kprime Lprime K1prime) →
          ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
            (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
            IsWeakSolutionFor A B K L K1) ∧
        ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
            (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
            (_ : IsScalarTower Aprime Kprime K1prime)
            (_ : FiniteDimensional Kprime K1prime),
            IsSolutionFor Aprime Bprime Kprime Lprime K1prime) →
          ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
            (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
            IsSolutionFor A B K L K1) ∧
        ((∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
            (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
            (_ : IsScalarTower Aprime Kprime K1prime)
            (_ : FiniteDimensional Kprime K1prime),
            IsSeparableSolutionFor Aprime Bprime Kprime Lprime K1prime) →
          ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
            (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
            IsSeparableSolutionFor A B K L K1) := sorry

end

/-! ### Lemma_15_116_6 (from Chap15) -/
open Ideal
open IsLocalRing
open scoped Pointwise TensorProduct

universe u v w

noncomputable section

section B1Action

variable {B : Type v} {K : Type u} {L : Type v} {K1 : Type w}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Field K] [Algebra B K] [IsFractionRing B K]
variable [Field L] [Algebra B L] [Algebra K L] [IsScalarTower B K L]
variable [Field K1] [Algebra K K1]

local notation "G" => Gal(K1 / K)
local notation "L10" => TensorProduct K L K1
local notation "L1" => L10 ⧸ nilradical L10
local notation "B1" => integralClosure B L1

local instance l1CommRing : CommRing L1 :=
  Ideal.Quotient.commRing _

local instance b1CommRing : CommRing B1 :=
  inferInstance

local instance b1Algebra : Algebra B B1 :=
  inferInstance

/- Domain-style sampling for Lemma 15.116.6:
- primary domain: Galois actions on the reduced tensor-product base change and the induced action
  on the corresponding integral closure over a discrete valuation ring
- sampled owner declarations:
  `MulSemiringAction.compHom`,
  `quotientMulSemiringAction`,
  `AlgEquiv.mapIntegralClosure`,
  `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `exists_gal_smul_eq_of_isMaximal`
- best owner abstraction: the source-facing owner layer is the canonical `Gal(K1 / K)`-action on
  `L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)` together with the induced action on
  `B1 = integralClosure B L1` and its invariant-extension transitivity specialization
  `exists_gal_smul_eq_of_under_eq_of_reducedTensorBaseChange`; the maximal-ideal conjugacy
  statement should then be a thin specialization of that public owner layer
- primitive data: the reduced tensor product `L1 = (L ⊗[K] K1)_red`, the integral closure
  `B1 = integralClosure B L1`, and maximal ideals `m, m' : Ideal B1`
- derived API: the descended quotient action on `L1`, the induced action on `B1`, the invariant
  owner `Algebra.IsInvariant B B1 Gal(K1 / K)`, the under-equality transitivity theorem, and the
  maximal-ideal transitivity statement

Source/core/bridge triage:
- `source-facing`: transitivity of the `Gal(K1 / K)`-action on maximal ideals of `B1`
- `core/canonical`: `MulSemiringAction Gal(K1 / K) L1`,
  `MulSemiringAction Gal(K1 / K) B1`, and
  `Algebra.IsInvariant.exists_smul_of_under_eq`
- `bridge/view`: the tensor-product automorphisms of `L ⊗[K] K1`, their quotient descendant on
  `L1`, the induced integral-closure action on `B1`, and the source-facing under-equality
  specialization
-/

/-- The `K`-algebra automorphism of `L ⊗[K] K1` induced by a `K`-automorphism of `K1`. -/
private noncomputable def reducedBaseChangeAutAux (σ : Gal(K1/K)) :
    L10 ≃ₐ[K] L10 :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) σ

/-- The `B`-algebra automorphism of `L ⊗[K] K1` induced by a `K`-automorphism of `K1`. -/
private noncomputable def reducedBaseChangeAlgEquiv (σ : G) :
    L10 ≃ₐ[B] L10 where
  toRingEquiv := (reducedBaseChangeAutAux σ).toRingEquiv
  commutes' b := by
    change
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) σ)
          (algebraMap B L b ⊗ₜ[K] (1 : K1)) =
        algebraMap B L b ⊗ₜ[K] (1 : K1)
    simp

/-- The canonical `Gal(K1 / K)`-action on `L ⊗[K] K1`, acting through the `K1`-factor. -/
private noncomputable abbrev reducedBaseChangeMulSemiringAction :
    MulSemiringAction G L10 :=
  { smul := fun σ x ↦ reducedBaseChangeAutAux σ x
    one_smul := by
      sorry
    mul_smul := by
      sorry
    smul_zero := by
      sorry
    smul_add := by
      sorry
    smul_one := by
      sorry
    smul_mul := by
      sorry }

-- Proof sketch: ring automorphisms preserve nilpotent elements, so the nilradical is stable under
-- the induced action.
/-- The induced `Gal(K1 / K)`-action on `L ⊗[K] K1` preserves the nilradical. -/
private theorem reducedBaseChangeAutAux_map_nilradical (σ : G) :
    Ideal.map (reducedBaseChangeAutAux σ).toRingHom
        (nilradical L10) =
      nilradical L10 := sorry

/-- The canonical `Gal(K1 / K)`-action on
`L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)`. -/
noncomputable abbrev reducedTensorBaseChangeMulSemiringAction :
    MulSemiringAction G L1 :=
  let _ : MulSemiringAction G L10 := reducedBaseChangeMulSemiringAction
  quotientMulSemiringAction (nilradical L10) fun σ ↦ by
    simpa [Ideal.pointwise_smul_def, reducedBaseChangeMulSemiringAction, reducedBaseChangeAutAux]
      using reducedBaseChangeAutAux_map_nilradical σ

/-- The induced `B`-algebra automorphism of
`L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)`. -/
private noncomputable def reducedBaseChangeAut (σ : G) :
    L1 ≃ₐ[B] L1 :=
  let h :
      nilradical L10 =
        Ideal.map
          (reducedBaseChangeAutAux σ).toRingHom
          (nilradical L10) :=
    (reducedBaseChangeAutAux_map_nilradical σ).symm
  Ideal.quotientEquivAlg (nilradical L10) (nilradical L10) (reducedBaseChangeAlgEquiv σ) h

/-- The canonical `Gal(K1 / K)`-action on `B1 = integralClosure B L1`. -/
noncomputable abbrev reducedTensorBaseChangeIntegralClosureMulSemiringAction :
    MulSemiringAction G B1 :=
  { smul := fun σ x ↦
      (reducedBaseChangeAut σ).mapIntegralClosure x
    one_smul := by
      sorry
    mul_smul := by
      sorry
    smul_zero := by
      sorry
    smul_add := by
      sorry
    smul_one := by
      sorry
    smul_mul := by
      sorry }

local instance : SMul G B1 :=
  reducedTensorBaseChangeIntegralClosureMulSemiringAction.toSMul

local instance : MulSemiringAction G B1 :=
  reducedTensorBaseChangeIntegralClosureMulSemiringAction

/-- The canonical `Gal(K1 / K)`-action on the reduced tensor-base-change integral closure `B1`
commutes with the scalar action of `B`. -/
theorem reducedTensorBaseChangeIntegralClosure_smulCommClass :
    SMulCommClass G B B1 := by
  sorry

/-- The reduced tensor-base-change integral closure `B1 = integralClosure B L1` is invariant under
the canonical `Gal(K1 / K)`-action. -/
theorem reducedTensorBaseChangeIntegralClosure_isInvariant :
    Algebra.IsInvariant B B1 G := by
  sorry

attribute [local instance] reducedTensorBaseChangeIntegralClosure_smulCommClass
attribute [local instance] reducedTensorBaseChangeIntegralClosure_isInvariant

variable [FiniteDimensional K K1] [Normal K K1]

/-- Any maximal ideal of `B1 = integralClosure B L1` lies over `maximalIdeal B`. -/
private instance liesOver_maximalIdeal_of_isMaximal
    (m : Ideal B1) [m.IsMaximal] : m.LiesOver (maximalIdeal B) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

/-- If two prime ideals of `B1 = integralClosure B L1` contract to the same ideal of `B`, then
they are Galois-conjugate under the canonical `Gal(K1 / K)`-action. -/
theorem exists_gal_smul_eq_of_under_eq_of_reducedTensorBaseChange
    (m m' : Ideal B1) [m.IsPrime] [m'.IsPrime]
    (hunder : m.under B = m'.under B) :
    ∃ σ : G, σ • m = m' := by
  sorry

-- Proof sketch: maximal ideals of `B1` all lie over `maximalIdeal B`, so the under-equality
-- transitivity theorem above applies directly to the invariant extension `B → B1`.
/-- Lemma 15.116.6: with
`L1 = (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)` and `B1 = integralClosure B L1`, the canonical
`Gal(K1 / K)`-action on `B1` is transitive on the maximal ideals of `B1`. -/
theorem exists_gal_smul_eq_of_isMaximal_of_reducedTensorBaseChange
    (m m' : Ideal B1) (hm : m.IsMaximal) (hm' : m'.IsMaximal) :
    ∃ σ : G, σ • m = m' := by
  letI : m.IsMaximal := hm
  letI : m'.IsMaximal := hm'
  exact exists_gal_smul_eq_of_under_eq_of_reducedTensorBaseChange m m'
    ((m.over_def (maximalIdeal B)).symm.trans (m'.over_def (maximalIdeal B)))

end B1Action

/-! ### Lemma_15_116_7 (from Chap15) -/
open Ideal IsLocalRing

universe u v

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]

local notation "K" => FractionRing A

/-- A maximal ideal of the integral closure witnesses a totally ramified degree-`q` extension when
it is the unique prime above `maximalIdeal A`, its residue-field map is bijective, its
ramification index is `q`, and it is generated by a uniformizer satisfying the two displayed
equations. -/
structure IsRamificationEliminationWitness
    (L : Type v) [Field L] [Algebra A L]
    (π : A) (n q : ℕ) (P : Ideal (integralClosure A L))
    [P.IsMaximal] [P.LiesOver (maximalIdeal A)] : Prop where
  unique_maximalIdeal :
    ∀ (Q : Ideal (integralClosure A L)) [Q.IsMaximal] [Q.LiesOver (maximalIdeal A)], Q = P
  residueField_bijective :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A (integralClosure A L))
        (P.over_def (maximalIdeal A)))
  ramificationIdx_eq :
    Ideal.ramificationIdx (maximalIdeal A) P = q
  exists_uniformizer_data :
    ∃ πB b b' : integralClosure A L,
      P = Ideal.span ({πB} : Set (integralClosure A L)) ∧
      πB ^ q =
        algebraMap A (integralClosure A L) π +
          algebraMap A (integralClosure A L) (π ^ n) * b ∧
      πB ^ q =
        algebraMap A (integralClosure A L) π +
          πB ^ (n * q) * b'

-- Proof sketch: split according to the characteristic of `K = FractionRing A`. In equal
-- characteristic zero, use the radical extension from Lemma `15.115.2`. In characteristic `p`,
-- adjoin a root `z` of `z ^ q - π ^ n * z = π ^ (1 - q)`, set `π_B = π z`, and compute directly
-- that the resulting degree-`q` extension is totally ramified and that `π_B` satisfies the two
-- displayed congruences in the integral closure.
/-- Lemma 15.116.7: if `A` is a discrete valuation ring with uniformizer `π` and residue
characteristic `p > 0`, then for every integer `n > 1` and every `p`-power `q` there exists a
degree-`q` separable extension `L / FractionRing A` that is totally ramified with respect to `A`
and whose integral closure `B = integralClosure A L` has ramification index `q` and a uniformizer
`π_B` satisfying `π_B ^ q = π + π ^ n * b` and `π_B ^ q = π + π_B ^ (nq) * b'` for some
`b, b' ∈ B`. -/
theorem exists_totallyRamified_separable_extension_with_prescribed_uniformizer_congruence
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n q : ℕ} (hn : 1 < n) (hq : ∃ m : ℕ, q = p ^ m) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : IsScalarTower A K L) (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L)
      (P : Ideal (integralClosure A L)) (_ : P.IsMaximal) (_ : P.LiesOver (maximalIdeal A)),
      Module.finrank K L = q ∧ IsRamificationEliminationWitness L π n q P := sorry

end

/-! ### Lemma_15_116_8 (from Chap15) -/
open Polynomial IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]
variable (a : A)
variable (hresidue : ∀ x : ResidueField A, x ^ p ≠ residue A a)

local notation "K" => FractionRing A
local notation "f" => (X ^ p - C (algebraMap A K a) : Polynomial K)
local notation "L" => AdjoinRoot f
local notation "α" => (AdjoinRoot.root f : L)
local notation "B" => Algebra.adjoin A ({α} : Set L)

/- Domain-style sampling:
* primary domain: Kummer-type degree-`p` extensions over the fraction field of a discrete
  valuation ring and the induced normalization over the base DVR;
* sampled owner declarations:
  `Polynomial.X_pow_sub_C_irreducible_of_prime`,
  `IsIntegralClosure.adjoin_le_integralClosure`,
  `integralClosure_isDiscreteValuationRing_of_finite_purelyInseparable`,
  `IsExtensionOfDiscreteValuationRings.WeaklyUnramified`;
* best owner abstraction: the canonical normalization `integralClosure A L`, with the explicit
  adjoin presentation `A[α]` kept only as the source-facing bridge;
* primitive data: the element `a : A`, the residue-field non-`p`th-power hypothesis, the Kummer
  polynomial `f = X ^ p - a`, and its adjoined root `α`;
* derived API: the no-`p`th-root statement in `FractionRing A`, irreducibility of `f`, the
  normalization equality `integralClosure A L = A[α]`, and the DVR / weakly-unramified structure
  on that normalization.

Layer triage:
* `source-facing`: the equality identifying the normalization with `A[α]`;
* `core/canonical`: `integralClosure A L`, `IsExtensionOfDiscreteValuationRings`, and
  `WeaklyUnramified`;
* `bridge/view`: the theorem `integralClosure_eq_adjoin_pth_root_of_residue_not_pth_power`.
-/

-- Proof sketch: if `x ^ p = a` in `FractionRing A`, then applying the residue map to an integral
-- representative of `x` produces a `p`th root of `residue A a` in `ResidueField A`, contradicting
-- `hresidue`.
/-- Lemma 15.116.8 (1): if the residue class of `a` in `ResidueField A` is not a `p`th power, then
`a` is not a `p`th power in the fraction field `FractionRing A`. -/
theorem fractionRing_pow_ne_of_residue_not_pth_power (x : K) :
    x ^ p ≠ algebraMap A K a := sorry

-- Proof sketch: apply the Kummer irreducibility criterion to `X ^ p - C (algebraMap A K a)` over
-- `K = FractionRing A`, using `fractionRing_pow_ne_of_residue_not_pth_power` to rule out `p`th
-- roots in `K`.
/-- The Kummer polynomial `X ^ p - a` over `FractionRing A` is irreducible under the residue-field
non-`p`th-power hypothesis. -/
private theorem x_pow_sub_C_irreducible_of_residue_not_pth_power :
    Irreducible f := sorry

/-- The canonical adjunction `K[a^{1/p}] = AdjoinRoot (X ^ p - a)` is a domain under the
irreducibility of the Kummer polynomial. -/
private instance adjoinRoot_x_pow_sub_C_isDomain_of_residue_not_pth_power :
    IsDomain L := sorry

-- Proof sketch: let `α = AdjoinRoot.root f`. The element `α` is integral over `A` because it
-- satisfies the monic polynomial `X ^ p - C a`, so `A[α]` sits inside the integral closure. For
-- the reverse inclusion, use the irreducibility of `f` and the standard description of the
-- normalization of a DVR in this radicial degree-`p` extension.
/-- Lemma 15.116.8 (2): in the canonical adjunction `K[a^{1/p}] = AdjoinRoot (X ^ p - a)`, the
integral closure of `A` is exactly the `A`-subalgebra generated by the adjoined `p`th root. -/
theorem integralClosure_eq_adjoin_pth_root_of_residue_not_pth_power :
    integralClosure A L = B := sorry

-- Proof sketch: after identifying the integral closure with `B` by
-- `integralClosure_eq_adjoin_pth_root_of_residue_not_pth_power`, apply the discrete-valuation-ring
-- structure theorem for the normalization of a DVR in this degree-`p` extension.
/-- Lemma 15.116.8 (3): the normalization `integralClosure A L` is a discrete valuation ring;
equivalently, by part `(2)`, the presentation `A[a^{1/p}] = A[AdjoinRoot.root f]` is a discrete
valuation ring. -/
instance integralClosure_isDiscreteValuationRing_of_residue_not_pth_power :
    IsDiscreteValuationRing (integralClosure A L) := sorry

-- Proof sketch: the canonical map `A → integralClosure A L` is the normalization map into the DVR
-- from part `(3)`, and part `(2)` identifies this canonical owner with the textbook presentation
-- `A[a^{1/p}]`.
/-- The canonical normalization map `A ⊆ integralClosure A L` is an extension of discrete
valuation rings; via part `(2)`, this is the extension `A ⊆ A[a^{1/p}]`. -/
instance integralClosure_isExtensionOfDiscreteValuationRings_of_residue_not_pth_power :
    IsExtensionOfDiscreteValuationRings A (integralClosure A L) := sorry

-- Proof sketch: identify the integral closure with `B`, then use the standard criterion for
-- weakly unramified extensions of discrete valuation rings in this radicial extension: the
-- structure map is injective and the maximal ideal of `A` extends to the maximal ideal of `B`.
/-- Lemma 15.116.8 (4): the normalization extension `A ⊆ integralClosure A L` is weakly
unramified; via part `(2)`, this is exactly the extension `A ⊆ A[a^{1/p}]`. -/
theorem weaklyUnramified_integralClosure_of_residue_not_pth_power :
    WeaklyUnramified A (integralClosure A L) := sorry

end

/-! ### Lemma_15_116_9 (from Chap15) -/
open Ideal IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped TensorProduct

universe u v w x y

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [NagataRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type (max x y)}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
variable [Field M] [Algebra C M] [IsFractionRing C M]
variable [Algebra L M] [Algebra K M] [IsScalarTower K L M]
variable [FiniteDimensional L M] [IsPurelyInseparable L M]
variable {p : ℕ}

/-- The extension `C` is generated over `B` by a `p`th root of the chosen uniformizer `π`. -/
private def IsGeneratedByPthRootOfUniformizer
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (p : ℕ) (π : A) : Prop :=
  ∃ x : C, x ^ p = algebraMap A C π ∧ Algebra.adjoin B ({x} : Set C) = ⊤

/-- The separable base-change alternative from the ramification-elimination lemma. It records a
degree-`p` separable extension `K1 / K` that is totally ramified with respect to `A`, makes
`L ⊗[K] K1` and `M ⊗[K] K1` into fields, and whose induced maps on the corresponding integral
closures are weakly unramified extensions of discrete valuation rings. -/
private def HasWeaklyUnramifiedSeparableBaseChange
    (A : Type u) (B : Type v) (C : Type w) (K : Type x) (L : Type y) (M : Type (max x y))
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsExtensionOfDiscreteValuationRings A B]
    [IsExtensionOfDiscreteValuationRings B C]
    [IsExtensionOfDiscreteValuationRings A C]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Field M] [Algebra C M] [IsFractionRing C M]
    [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (p : ℕ) : Prop :=
  ∃ (K1 : Type (max u v w x y)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
    (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1) (_ : Algebra.IsSeparable K K1),
      Module.finrank K K1 = p ∧
        ∃ (P : Ideal (integralClosure A K1)) (_ : P.IsMaximal)
          (_ : P.LiesOver (maximalIdeal A)),
          (∀ (Q : Ideal (integralClosure A K1)) (_ : Q.IsMaximal)
            (_ : Q.LiesOver (maximalIdeal A)), Q = P) ∧
            Function.Bijective
              (Ideal.ResidueField.map (maximalIdeal A) P
                (algebraMap A (integralClosure A K1)) (P.over_def (maximalIdeal A))) ∧
            Ideal.ramificationIdx (maximalIdeal A) P = p ∧
              let A1 := integralClosure A K1
              let L1 := TensorProduct K L K1
              let M1 := TensorProduct K M K1
              let B1 := integralClosure B L1
              let C1 := integralClosure C M1
              ∃ (_ : IsField L1) (_ : IsField M1)
                (_ : IsDomain A1) (_ : IsDiscreteValuationRing A1)
                (_ : IsDomain B1) (_ : IsDiscreteValuationRing B1)
                (_ : IsDomain C1) (_ : IsDiscreteValuationRing C1)
                (_ : Algebra A1 B1) (_ : Algebra B1 C1)
                (_ : IsExtensionOfDiscreteValuationRings A1 B1)
                (_ : IsExtensionOfDiscreteValuationRings B1 C1),
                  WeaklyUnramified A1 B1 ∧ WeaklyUnramified B1 C1

-- Proof sketch: let `e` be the ramification index of `C` over `B`. If `e = 1`, transitivity gives
-- the weakly unramified case for `A → C`. Otherwise the purely inseparable degree-`p` hypothesis
-- forces `e = p`; writing a uniformizer of `C` as a `p`th root of `uπ`, either `u` is already a
-- `p`th power in `B`, which gives `C = B[π^(1/p)]`, or after adjoining the totally ramified
-- degree-`p` separable extension furnished by Lemma `15.116.7`, Lemma `15.116.8` makes both
-- induced maps on the integral closures weakly unramified.
/-- Lemma 15.116.9: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction fields
`K ⊆ L ⊆ M`, let `π ∈ A` be a uniformizer, assume `B` is Nagata and `A ⊆ B` is weakly
unramified, and assume `M / L` is purely inseparable of degree `p`. Then either `A → C` is
weakly unramified, or `C` is generated over `B` by a `p`th root of `π`, or there exists a
degree-`p` separable extension `K1 / K` totally ramified with respect to `A` such that
`L1 = L ⊗[K] K1` and `M1 = M ⊗[K] K1` are fields and the induced maps on the corresponding
integral closures `A1 → B1 → C1` are weakly unramified extensions of discrete valuation rings. -/
theorem ramification_elimination_of_purelyInseparable_degree_p
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    (hAB : WeaklyUnramified A B) (hLM : Module.finrank L M = p) :
    WeaklyUnramified A C ∨
      IsGeneratedByPthRootOfUniformizer A B C p π ∨
      HasWeaklyUnramifiedSeparableBaseChange
        A B C K L M p := sorry

end

/-! ### Lemma_15_116_10 (from Chap15) -/
open IsLocalRing

universe u

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

local notation "κA" => ResidueField A

/- Domain-style sampling:
- primary domain: coefficient fields of complete local rings and compatibility of those coefficient
  fields under local ring homomorphisms;
- sampled owner declarations:
  `IsCompleteLocalRing`,
  `isAdicComplete_of_pow_smul_top_eq_bot`,
  `exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver`,
  `ResidueField.map`,
  `IsLocalHom`;
- best owner abstraction: the complete-local-ring owner `IsCompleteLocalRing A` together with the
  coefficient-field section theorem
  `exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver`, and
  `ResidueField.map (algebraMap A A')` for the canonical residue-field comparison along a local
  homomorphism;
- primitive data: a local ring, nilpotence of its maximal ideal, and in the compatibility clause a
  local hom `A → A'` together with a chosen section `σ : ResidueField A →+* A` of `residue A`;
- derived API: completeness from nilpotence, the induced coefficient-field section, and the
  compatible lift along `ResidueField.map (algebraMap A A')`.

Source/core/bridge triage:
- `source-facing`: the two Lemma `15.116.10` existence statements about residue-field sections;
- `core/canonical`: `IsCompleteLocalRing` and
  `exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver`, together with the
  canonical residue-field map `ResidueField.map`;
- `bridge/view`: the private completeness upgrade from nilpotent maximal ideal, and the induced
  `ResidueField A`-algebra structure on `A'` used internally to construct a compatible section.
-/

private theorem isCompleteLocalRing_of_nilpotent_maximalIdeal
    (h_nil : IsNilpotent (maximalIdeal A)) : IsCompleteLocalRing A := by
  rcases h_nil with ⟨n, hn⟩
  let _ : IsAdicComplete (maximalIdeal A) A := by
    refine isAdicComplete_of_pow_smul_top_eq_bot (maximalIdeal A) n ?_
    simp [hn]
  infer_instance

-- Proof sketch: Proposition `10.158.9` makes the prime-field extension
-- `ZMod p → ResidueField A` formally smooth because `p` is prime. Since `maximalIdeal A` is
-- nilpotent, the residue map `A → ResidueField A` is a nilpotent thickening, so formal smoothness
-- produces a section `ResidueField A → A`.
/-- Lemma 15.116.10: if `A` is a local ring of characteristic `p` with nilpotent maximal ideal,
then the residue map `A → ResidueField A` admits a ring-theoretic section. -/
theorem exists_residueField_section_of_isNilpotent_maximalIdeal
    {p : ℕ} [Fact p.Prime] [CharP A p]
    (h_nil : IsNilpotent (maximalIdeal A)) :
    ∃ σ : κA →+* A, (residue A).comp σ = RingHom.id κA := by
  letI : IsCompleteLocalRing A := isCompleteLocalRing_of_nilpotent_maximalIdeal h_nil
  letI : Algebra (ZMod p) A := ZMod.algebra A p
  letI : Algebra (ZMod p) κA := ((residue A).comp (algebraMap (ZMod p) A)).toAlgebra
  rcases exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver A (ZMod p) with
      ⟨σ, hσ⟩
  exact ⟨σ.toRingHom, hσ⟩

section

variable {A' : Type u} [CommRing A'] [IsLocalRing A']
variable [Algebra A A'] [IsLocalHom (algebraMap A A')]

local notation "κA'" => ResidueField A'

/-- The canonical residue-field extension induced by a local homomorphism `A → A'`. -/
noncomputable instance residueFieldAlgebra : Algebra κA κA' :=
  (ResidueField.map (algebraMap A A')).toAlgebra

-- Proof sketch: derive a complete-local structure on `A'` from the nilpotence of its maximal
-- ideal. The chosen section `σ : ResidueField A → A` and the local map `A → A'` induce a
-- `ResidueField A`-algebra structure on `A'`; because `σ` is a section of `residue A`, the
-- induced residue-field map to `ResidueField A'` is the canonical comparison
-- `ResidueField.map (algebraMap A A')`. Lemma `15.38.3` then gives a section of `residue A'`
-- compatible with the chosen section on `A`.
/-- Lemma 15.116.10 (compatibility clause): let `A → A'` be a local homomorphism of local rings.
Assume the maximal ideal of `A'` is nilpotent, choose a section `σ : ResidueField A →+* A` of
`residue A`, and assume the canonical residue-field extension `ResidueField A' / ResidueField A`
is separable. Then there exists a section `σ' : ResidueField A' →+* A'` of `residue A'`
compatible with `σ` and the local map `A → A'`. -/
theorem exists_compatible_residueField_section_of_isNilpotent_maximalIdeal
    (h_nil' : IsNilpotent (maximalIdeal A'))
    (σ : κA →+* A)
    (hσ : (residue A).comp σ = RingHom.id κA)
    [Algebra.IsSeparableOver κA κA'] :
    ∃ σ' : κA' →+* A',
      (residue A').comp σ' = RingHom.id κA' ∧
        σ'.comp (ResidueField.map (algebraMap A A')) = (algebraMap A A').comp σ := by
  sorry

end

end

/-! ### Lemma_15_116_11 (from Chap15) -/
open IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped IntermediateField

universe u v

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable {p : ℕ} [Fact p.Prime] [CharP (FractionRing A) p]
variable {ξ : FractionRing A}

local notation "K" => FractionRing A
local notation "κA" => ResidueField A
local notation "B" => integralClosure A L

/- Domain-style sampling:
* primary domain: ramification theory for Artin-Schreier extensions of the fraction field of a
  discrete valuation ring in characteristic `p`;
* sampled owner declarations:
  `IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic`,
  `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`,
  `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`,
  `uniformizerRootFractionPolynomial_irreducible`,
  `primitiveRootElimination_weakly_unramified_residue_case_of_uniformizer_denominator`,
  `IsUnramifiedWithRespectTo`,
  `IsTotallyRamifiedWithRespectTo`,
  `WeaklyUnramified`,
  `residueDegree`,
  `residue`;
* best owner abstraction: the chapter ramification owners on `L / FractionRing A` and on the
  induced extension `A ⊆ integralClosure A L`, with the simple intermediate field `K⟮z⟯` as the
  canonical source-facing owner for the Artin-Schreier generator data;
* primitive data: a root `z` of `X ^ p - X - ξ` together with the owner-level generator condition
  `K⟮z⟯ = ⊤`, plus the denominator data `ξ = a / π^n`;
* derived API: the Galois and ramification alternatives, and in the `p ∣ n` branch the single
  existential weakly-unramified residue-field case, along with the finite-dimensionality and
  separability companion lemmas derived from the simple-generator owner.

Layer triage:
* `source-facing`: the Artin-Schreier extension statements in this file;
* `core/canonical`: `IsUnramifiedWithRespectTo`, `IsTotallyRamifiedWithRespectTo`,
  `WeaklyUnramified`, and `residue A`;
* `bridge/view`: the bridge back to `Algebra.adjoin K ({z} : Set L) = ⊤` when an implementation
  needs the subalgebra form, together with the local-extension and residue-field instances for
  `integralClosure A L`.
-/

private theorem finiteDimensional_of_artinSchreier_generator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    FiniteDimensional K L := by
  sorry

private theorem isSeparable_of_artinSchreier_generator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    Algebra.IsSeparable K L := by
  sorry

private theorem finiteDimensional_residueField_of_integralClosure
    [FiniteDimensional K L]
    [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) := by
  sorry

section ArtinSchreierGenerator

variable (z : L) (hz : z ^ p - z = algebraMap K L ξ)
variable (hgen : K⟮z⟯ = ⊤)

local instance : FiniteDimensional K L :=
  finiteDimensional_of_artinSchreier_generator z hz hgen

local instance : Algebra.IsSeparable K L :=
  isSeparable_of_artinSchreier_generator z hz hgen

local instance [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) :=
  finiteDimensional_residueField_of_integralClosure

-- Proof sketch: the polynomial `X ^ p - X - ξ` has derivative `-1`, so adjoining a root gives a
-- separable extension of degree dividing `p`; in characteristic `p` this is the Artin-Schreier
-- situation, hence the extension is Galois. The ramification alternatives come from the
-- classification of Artin-Schreier extensions over a discrete valuation ring, with the trivial
-- case recorded by `Module.finrank K L = 1` because the extension field is an arbitrary `K`-algebra
-- rather than literally the same type as `K`.
/-- Lemma 15.116.11: let `A` be a discrete valuation ring with fraction field `K = FractionRing A`
of characteristic `p > 0`, let `ξ : K`, and let `L` be obtained by adjoining to `K` a root `z`
of `z ^ p - z = ξ`. Then `L / K` is Galois and one of the following happens: the extension is
trivial, recorded as `Module.finrank K L = 1`; the extension is unramified of degree `p`; the
extension is totally ramified of degree `p`; or `B = integralClosure A L` is a discrete valuation
ring such that `A ⊆ B` is weakly unramified and the induced residue-field extension
`ResidueField B / ResidueField A` is purely inseparable of degree `p`. -/
theorem artin_schreier_extension_galois_and_has_ramification_case
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    :
    IsGalois K L ∧
      (Module.finrank K L = 1 ∨
        (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) ∨
        (Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L) ∨
        ∃ (_ : IsDiscreteValuationRing B),
          WeaklyUnramified A B ∧
            IsPurelyInseparable κA (ResidueField B) ∧
            residueDegree A B = p) := sorry

-- Proof sketch: if `ξ` comes from `A`, then the Artin-Schreier polynomial defines a finite étale
-- `A`-algebra. Over a discrete valuation ring this forces either the trivial case or the
-- unramified degree-`p` case.
/-- If `ξ` lies in the discrete valuation ring `A`, then the associated Artin-Schreier extension is
either trivial or unramified of degree `p`. -/
theorem artin_schreier_eq_or_unramified_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    Module.finrank K L = 1 ∨ (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) := sorry

-- Proof sketch: write the chosen root `z` in a localization of the integral closure of `A` and
-- compare valuations in the equation `z ^ p - z = ξ`. When the pole order `n` of `ξ` is positive
-- and not divisible by `p`, the valuation computation shows that the ramification index is
-- divisible by `p`; since the degree is at most `p`, the integral closure must be a discrete
-- valuation ring and the extension is totally ramified with ramification index `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∤ n`, and `a` a unit of `A`, then the associated
Artin-Schreier extension is in the totally ramified case with ramification index `p`. -/
theorem artin_schreier_totally_ramified_of_uniformizer_denominator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hndiv : ¬ p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L := sorry

-- Proof sketch: after multiplying the Artin-Schreier equation by the `p`th power of a
-- uniformizer, rewrite it in integral form over `A`. The resulting integral closure is weakly
-- unramified over `A`, and the assumption that the residue of `a` is not a `p`th power forces the
-- residue-field extension to be purely inseparable of degree `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∣ n`, and the residue class of the unit `a` is not a `p`th
power in `ResidueField A`, then `B = integralClosure A L` is a discrete valuation ring such that
`A ⊆ B` is weakly unramified and the residue-field extension `ResidueField B / ResidueField A` is
purely inseparable of degree `p`. -/
theorem artin_schreier_weakly_unramified_residue_case_of_uniformizer_denominator
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (ha : ¬ ∃ b : κA, b ^ p = residue A (a : A))
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    ∃ (_ : IsDiscreteValuationRing B),
      WeaklyUnramified A B ∧
        IsPurelyInseparable κA (ResidueField B) ∧
        residueDegree A B = p := sorry

end ArtinSchreierGenerator

end

/-! ### Lemma_15_116_12 (from Chap15) -/
open IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v w x y z

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [Algebra A L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra K M] [Algebra C M] [Algebra L M] [IsFractionRing C M]
variable [IsScalarTower A C M] [IsScalarTower A K M]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [FiniteDimensional L M] [IsGalois L M]

-- Proof sketch: choose an Artin-Schreier generator for the degree-`p` Galois extension `M / L`,
-- apply the ramification trichotomy over `B`, and use the hypothesis on
-- `⋂_{n ≥ 1} (ResidueField B)^(p^n)` together with the totally ramified degree-`p^r` extensions
-- from Lemma `15.116.7` to eliminate the bad residue terms inductively until the base change over
-- `C` becomes weakly unramified.
/-- Lemma 15.116.12: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction
fields `K ⊆ L ⊆ M`. Assume `A ⊆ B` is weakly unramified, `K` has characteristic `p`, `M / L` is
a degree-`p` Galois extension, and the image of `ResidueField A` in `ResidueField B` is exactly
the intersection of the subsets of `p^n`-powers in `ResidueField B`. Then there exists a finite
Galois extension `K₁ / K`, totally ramified with respect to `A`, which is a weak solution for the
extension `A → C`. -/
theorem exists_totallyRamified_galois_weakSolution_of_degree_p_galois_extension
    (hAB : WeaklyUnramified A B)
    (hLM : Module.finrank L M = p)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : Algebra (FractionRing A) K1)
      (_ : IsScalarTower A (FractionRing A) K1)
      (_ : FiniteDimensional K K1) (_ : FiniteDimensional (FractionRing A) K1)
      (_ : IsGalois K K1) (_ : Algebra.IsSeparable (FractionRing A) K1)
      (_ : IsTotallyRamifiedWithRespectTo A K1),
        IsWeakSolutionFor A C K M K1 := sorry

end

/-! ### Lemma_15_116_13 (from Chap15) -/
open scoped BigOperators
open Polynomial

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
variable {p : ℕ}

local notation "R₂" => MvPolynomial (Fin 2) A
local notation "X0" => (MvPolynomial.X (0 : Fin 2) : R₂)
local notation "X1" => (MvPolynomial.X (1 : Fin 2) : R₂)

/- Domain-style sampling:
* primary domain: source-facing quotient-polynomial identities attached to a primitive `p`th root
  of unity and its distinguished coefficient `1 - ζ`;
* sampled owner declarations:
  `IsPrimitiveRoot`,
  `Ideal.IsGabberHenselPolynomial`,
  `uniformizerRootPolynomial`,
  `RingHom.ShiftPowerPolynomialImageGenerating`;
* best owner abstraction: a source-facing predicate on the quotient polynomial `P` attached to
  `ζ`, with the distinguished coefficient kept as the canonical term `1 - ζ` rather than as a
  second primitive parameter;
* primitive data: coefficient witnesses `a i`, the displayed polynomial shape, and the quotient
  identity written with `1 - ζ`;
* derived API: coefficient/quotient projection lemmas, existence under `IsPrimitiveRoot ζ p`, and
  the additive identity derived from the quotient equation alone.

Layer triage:
* `source-facing`: the quotient polynomial attached to `ζ` and its source-form polynomial
  identities, since no chapter/project owner already packages this notion;
* `bridge/view`: the existence theorem specialized by `IsPrimitiveRoot ζ p`, and the additive
  identity derived from the quotient equation.
-/

/-- The quotient polynomial `P` from Lemma `15.116.13` attached to `ζ`, where the distinguished
coefficient is canonically `1 - ζ` and the intermediate coefficients lie in the principal ideal
generated by `1 - ζ`. -/
def IsOneSubZetaQuotientPolynomial (p : ℕ) (ζ : A) (P : A[X]) : Prop :=
  ∃ a : ℕ → A,
    (∀ i, 0 < i → i < p → a i ∈ Ideal.span ({1 - ζ} : Set A)) ∧
      P = X ^ p - X + ∑ i ∈ Finset.Icc 1 (p - 1), C (a i) * X ^ i ∧
      C ((1 - ζ) ^ p) * P = (C (1 : A) + C (1 - ζ) * X) ^ p - 1

namespace IsOneSubZetaQuotientPolynomial

theorem exists_coefficients {ζ : A} {P : A[X]} (hP : IsOneSubZetaQuotientPolynomial p ζ P) :
    ∃ a : ℕ → A,
      (∀ i, 0 < i → i < p → a i ∈ Ideal.span ({1 - ζ} : Set A)) ∧
        P = X ^ p - X + ∑ i ∈ Finset.Icc 1 (p - 1), C (a i) * X ^ i ∧
        C ((1 - ζ) ^ p) * P = (C (1 : A) + C (1 - ζ) * X) ^ p - 1 :=
  hP

theorem eq_polynomial {ζ : A} {P : A[X]} (hP : IsOneSubZetaQuotientPolynomial p ζ P) :
    ∃ a : ℕ → A, P = X ^ p - X + ∑ i ∈ Finset.Icc 1 (p - 1), C (a i) * X ^ i := by
  rcases hP.exists_coefficients with ⟨a, -, hshape, -⟩
  exact ⟨a, hshape⟩

theorem quotient_eq {ζ : A} {P : A[X]} (hP : IsOneSubZetaQuotientPolynomial p ζ P) :
    C ((1 - ζ) ^ p) * P = (C (1 : A) + C (1 - ζ) * X) ^ p - 1 := by
  rcases hP.exists_coefficients with ⟨_, _, _, hquot⟩
  exact hquot

end IsOneSubZetaQuotientPolynomial

-- Proof sketch: set `w = 1 - ζ`, expand `(1 + w X)^p` by the binomial theorem, use that `ζ` is a
-- primitive `p`th root of unity to show the numerator is divisible by `w^p`, and record the
-- remaining coefficients as elements of the ideal generated by `w`.
/-- Lemma 15.116.13 (1): if `A` contains a primitive `p`th root of unity `ζ`, then there is a
polynomial `P ∈ A[z]` representing `((1 + (1 - ζ) z)^p - 1) / (1 - ζ)^p`, and the intermediate
coefficients of `P` lie in the ideal `(1 - ζ)`. -/
theorem exists_oneSubZetaQuotientPolynomial
    [Fact p.Prime]
    {ζ : A}
    (hζ : IsPrimitiveRoot ζ p) :
    ∃ P : A[X], IsOneSubZetaQuotientPolynomial p ζ P := sorry

/-- Lemma 15.116.13 (2), core quotient form: any polynomial satisfying the quotient identity
`w^p P(z) = (1 + wz)^p - 1` also satisfies the two-variable additive formula. -/
theorem oneSubZetaQuotientPolynomial_add_formula
    {w : A}
    {P : A[X]}
    (hquot : C (w ^ p) * P = (C (1 : A) + C w * X) ^ p - 1) :
    (Polynomial.aeval (X0 + X1 + MvPolynomial.C w * X0 * X1) P : R₂) =
      Polynomial.aeval X0 P + Polynomial.aeval X1 P +
        MvPolynomial.C (w ^ p) * Polynomial.aeval X0 P * Polynomial.aeval X1 P := sorry

-- Proof sketch: use the quotient identity recorded in `hP`, written with the distinguished
-- element `w = 1 - ζ`, and compare the two ways of rewriting
-- `(1 + w (z₁ + z₂ + w z₁ z₂))^p - 1` in the two-variable polynomial ring `A[z₁, z₂]`.
/-- Lemma 15.116.13 (2): if `P` is the quotient polynomial from part `(1)`, then
`P(z₁ + z₂ + (1 - ζ) z₁ z₂) = P(z₁) + P(z₂) + (1 - ζ)^p P(z₁) P(z₂)` in `A[z₁, z₂]`. -/
theorem IsOneSubZetaQuotientPolynomial.add_formula
    {ζ : A}
    {P : A[X]}
    (hP : IsOneSubZetaQuotientPolynomial p ζ P) :
    (Polynomial.aeval (X0 + X1 + MvPolynomial.C (1 - ζ) * X0 * X1) P : R₂) =
      Polynomial.aeval X0 P + Polynomial.aeval X1 P +
        MvPolynomial.C ((1 - ζ) ^ p) * Polynomial.aeval X0 P * Polynomial.aeval X1 P := by
  exact oneSubZetaQuotientPolynomial_add_formula hP.quotient_eq

end
