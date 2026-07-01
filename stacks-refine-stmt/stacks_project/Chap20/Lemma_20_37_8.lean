import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry
open DerivedCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of modules on a ringed space `X`. -/
abbrev ringedSpaceModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf of a derived
`\mathcal O_X`-module. -/
abbrev ringedSpaceCohomologySheaf (X : RingedSpace.{u})
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj
    ((DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q).obj K)

/-- The stage `τ_{\ge -n} E` in the canonical lower truncation tower of a derived
`\mathcal O_X`-module `E`. -/
noncomputable abbrev derivedTruncationGEStage
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    DerivedCategory (ringedSpaceModuleCat X) :=
  Q.obj ((Q.objPreimage E).truncGE (-((n : ℕ) : ℤ)))

/-- The transition morphism `τ_{\ge -(n + 1)} E ⟶ τ_{\ge -n} E` in the truncation tower. -/
noncomputable abbrev derivedTruncationGEStep
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    derivedTruncationGEStage E (n + 1) ⟶ derivedTruncationGEStage E n :=
  let E' := Q.objPreimage E
  let a : ℤ := -(((n + 1 : ℕ)) : ℤ)
  let b : ℤ := -((n : ℕ) : ℤ)
  let hab : a ≤ b :=
    neg_le_neg (show ((n : ℕ) : ℤ) ≤ (((n + 1 : ℕ)) : ℤ) from
      Int.ofNat_le.mpr (Nat.le_succ n))
  letI : (E'.truncGE b).IsStrictlyGE a :=
    (E'.truncGE b).isStrictlyGE_of_ge a b hab
  Q.map (CochainComplex.truncGEMap (E'.πTruncGE b) a) ≫
    inv (Q.map ((E'.truncGE b).πTruncGE a))

/-- The inverse system `n ↦ τ_{\ge -n} E` in the derived category of `\mathcal O_X`-modules. -/
noncomputable abbrev derivedTruncationGETower
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X)) :
    ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X) :=
  Functor.ofOpSequence (derivedTruncationGEStep E)

/-- The underlying family of objects of the truncation tower of `E`. -/
abbrev derivedTruncationGETowerFamily
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X)) :
    ℕ → DerivedCategory (ringedSpaceModuleCat X) :=
  fun n ↦ (derivedTruncationGETower E).obj (Opposite.op n)

/-- The Milnor difference map on the product of the truncation tower of `E`. -/
def derivedTruncationGETowerDifferenceMap
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X))
    [HasProduct (derivedTruncationGETowerFamily E)] :
    ∏ᶜ derivedTruncationGETowerFamily E ⟶ ∏ᶜ derivedTruncationGETowerFamily E :=
  Pi.lift fun n ↦
    Pi.π (derivedTruncationGETowerFamily E) n -
      Pi.π (derivedTruncationGETowerFamily E) (n + 1) ≫
        (derivedTruncationGETower E).map ((homOfLE (Nat.le_succ n)).op)

/-- The canonical morphism `E ⟶ τ_{\ge -n} E` obtained from truncating a chosen cochain-complex
representative of `E`. -/
noncomputable abbrev derivedTruncationGEToStage
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    E ⟶ derivedTruncationGEStage E n :=
  (Q.objObjPreimageIso E).inv ≫
    Q.map ((Q.objPreimage E).πTruncGE (-((n : ℕ) : ℤ)))

/-- A morphism `c : E ⟶ L` is a compatible comparison from `E` to a chosen derived limit of its
truncation tower if `L` fits into the Milnor triangle and the projections to each truncation stage
recover the canonical truncation maps. -/
def IsTruncationDerivedLimitComparison
    {X : RingedSpace.{u}}
    (E L : DerivedCategory (ringedSpaceModuleCat X)) (c : E ⟶ L) : Prop :=
  ∃ _ : HasProduct (derivedTruncationGETowerFamily E),
    ∃ (ι : L ⟶ ∏ᶜ derivedTruncationGETowerFamily E)
      (δ : ∏ᶜ derivedTruncationGETowerFamily E ⟶ L⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedTruncationGETowerDifferenceMap E) δ ∈
          distTriang (DerivedCategory (ringedSpaceModuleCat X)) ∧
        ∀ n : ℕ, c ≫ ι ≫ Pi.π (derivedTruncationGETowerFamily E) n =
          derivedTruncationGEToStage E n

/-- A derived `\mathcal O_X`-module has eventually vanishing local cohomology of its cohomology
sheaves near each point if, after shrinking inside any neighborhood of the point, one gets a
uniform bound in each total degree beyond which the groups `H^p(U, H^{m-p}(E))` vanish. -/
def EventualCohomologySheafVanishingNear
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (E : DerivedCategory (ringedSpaceModuleCat X)) : Prop :=
  ∀ x : X, ∃ px : ℤ → ℤ,
    ∀ W : Opens X.carrier, x ∈ W →
      ∃ U : Opens X.carrier,
        x ∈ U ∧ U ≤ W ∧
          ∀ m : ℤ, ∀ p : ℕ, px m < (p : ℤ) →
            IsZero ((ringedSpaceCohomologySheaf X E (m - (p : ℤ))).H' p U)

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

section UniformBasisVanishing

variable (E : DerivedCategory (ringedSpaceModuleCat X))
variable (cohomologyBound : ℤ → ℤ) (𝓑 : Set (Opens X.carrier))
variable
  (hcover :
    ∀ W : Opens X.carrier, ∃ ι : Type u, ∃ U : ι → Opens X.carrier,
      (∀ i, U i ∈ 𝓑) ∧ iSup U = W)
variable
  (hvanish :
    ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
      ∀ m : ℤ, ∀ p : ℕ, cohomologyBound m < (p : ℤ) →
        IsZero ((ringedSpaceCohomologySheaf X E (m - (p : ℤ))).H' p U))

-- Proof sketch: fix a point `x` and a neighborhood `W`. Choose a covering of `W` by opens in
-- `𝓑`, then pick one member containing `x`. The same global function `cohomologyBound` serves as
-- the local bound `p(x,-)`, and the given vanishing hypothesis on members of `𝓑` is exactly the
-- neighborhood condition required in `EventualCohomologySheafVanishingNear`.
/-- A uniform vanishing bound on a basis-like family of opens implies the pointwise shrinking
condition `EventualCohomologySheafVanishingNear`. -/
theorem eventualCohomologySheafVanishingNear_of_uniform_basis_vanishing :
    EventualCohomologySheafVanishingNear E := sorry

variable {L : DerivedCategory (ringedSpaceModuleCat X)} (c : E ⟶ L)
variable (hc : IsTruncationDerivedLimitComparison E L c)

-- Proof sketch: first use
-- `eventualCohomologySheafVanishingNear_of_uniform_basis_vanishing` to convert the global
-- basis-wise vanishing assumption into the local hypothesis of Lemma `20.37.6`. Then apply the
-- local-to-global truncation comparison criterion for a compatible map to the derived limit of the
-- truncation tower.
/-- Lemma 20.37.8: let `(X, \mathcal O_X)` be a ringed space and let `E ∈ D(\mathcal O_X)`.
Assume there exist a function `p(-) : \mathbf Z → \mathbf Z` and a set `\mathcal B` of opens of
`X` such that every open subset of `X` admits a covering by members of `\mathcal B`, and
`H^p(U, H^{m-p}(E)) = 0` for `p > p(m)` and `U ∈ \mathcal B`. Then any compatible comparison
morphism `E ⟶ R\!\varprojlim_n τ_{\ge -n} E` from Remark `13.34.5` is an isomorphism in
`D(\mathcal O_X)`. -/
theorem isIso_of_truncationDerivedLimitComparison_of_uniform_basis_vanishing :
    IsIso c := sorry

end UniformBasisVanishing

end

end AlgebraicGeometry.RingedSpace
