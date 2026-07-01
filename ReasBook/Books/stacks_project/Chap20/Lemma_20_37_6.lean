import Mathlib
import stacks_project.Chap13.Remark_13_34_5
import stacks_project.Chap20.Lemma_20_32_3

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

/-- A derived `\mathcal O_X`-module has eventually vanishing local cohomology of its cohomology
sheaves near each point if, after shrinking inside any neighborhood of `x`, one gets a uniform
bound in each total degree beyond which the groups `H^p(U, H^{m-p}(E))` vanish. -/
def EventualCohomologySheafVanishingNear
    (E : DerivedCategory (ringedSpaceModuleCat X)) : Prop :=
  ∀ x : X, ∃ px : ℤ → ℤ,
    ∀ W : Opens X.carrier, x ∈ W →
      ∃ U : Opens X.carrier,
        x ∈ U ∧ U ≤ W ∧
          ∀ m : ℤ, ∀ p : ℕ, px m < (p : ℤ) →
            IsZero ((ringedSpaceCohomologySheaf X E (m - (p : ℤ))).H' p U)

-- Proof sketch: this is just the defining neighborhood-shrinking form of
-- `EventualCohomologySheafVanishingNear`.
/-- The local vanishing hypothesis can be used on any chosen neighborhood of a point. -/
theorem EventualCohomologySheafVanishingNear.exists_shrunk_open
    {E : DerivedCategory (ringedSpaceModuleCat X)}
    (hE : EventualCohomologySheafVanishingNear X E)
    (x : X) :
    ∃ px : ℤ → ℤ,
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧ U ≤ W ∧
            ∀ m : ℤ, ∀ p : ℕ, px m < (p : ℤ) →
              IsZero ((ringedSpaceCohomologySheaf X E (m - (p : ℤ))).H' p U) := sorry

-- Proof sketch: for each degree `m` and point `x`, choose `n(x)` from the local bounds in the
-- hypothesis so that the truncation triangles of Remark `13.12.4` force eventual stability of
-- the maps on `H^{m-1}(U,-)` and `H^m(U,-)` over a cofinal system of neighborhoods of `x`.
-- Lemma `20.37.5` then gives injectivity on stalks of the map
-- `H^m(L)_x → H^m(\tau_{\ge -n(x)}E)_x`; since `H^m(E) → H^m(\tau_{\ge -n(x)}E)` is an
-- isomorphism for `n(x) ≥ -m`, the induced stalk map `H^m(E)_x → H^m(L)_x` is bijective. Thus
-- every cohomology sheaf map induced by `c` is an isomorphism, so `c` is an isomorphism in the
-- derived category.
/-- Lemma 20.37.6: let `(X, \mathcal O_X)` be a ringed space and let `E ∈ D(\mathcal O_X)`.
Assume that for every point `x ∈ X` there is a function `p(x,-) : \mathbf Z → \mathbf Z` such
that, after shrinking inside any neighborhood of `x`, one has
`H^p(U, H^{m-p}(E)) = 0` for all `p > p(x,m)`. Then any compatible comparison morphism
`E ⟶ R\!\varprojlim_n \tau_{\ge -n}E` from Remark `13.34.5` is an isomorphism in
`D(\mathcal O_X)`. -/
theorem isIso_of_truncationDerivedLimitComparison_of_eventualCohomologySheafVanishingNear
    (E : DerivedCategory (ringedSpaceModuleCat X))
    {L : DerivedCategory (ringedSpaceModuleCat X)} (c : E ⟶ L)
    (hc : CategoryTheory.IsTruncationDerivedLimitComparison E L c)
    (hE : EventualCohomologySheafVanishingNear X E) :
    IsIso c := sorry

end

end AlgebraicGeometry.RingedSpace
