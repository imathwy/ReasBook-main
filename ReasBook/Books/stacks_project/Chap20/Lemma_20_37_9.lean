import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
abbrev ringedSpaceModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

/-- Sheaves of `\mathcal O_X`-modules form an abelian category. -/
local instance ringedSpaceModuleCatAbelian : Abelian (ringedSpaceModuleCat X) := inferInstance

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf `H^q(E)` of a derived
`\mathcal O_X`-module. -/
abbrev ringedSpaceCohomologySheaf
    (E : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj
    ((DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q).obj E)

/-- The stage `τ_{\ge -n} E` in the canonical truncation tower of a derived `\mathcal O_X`-module
`E`. -/
noncomputable abbrev derivedTruncationGEStage
    (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    DerivedCategory (ringedSpaceModuleCat X) :=
  Q.obj ((Q.objPreimage E).truncGE (-((n : ℕ) : ℤ)))

/-- The transition map `τ_{\ge -(n + 1)} E ⟶ τ_{\ge -n} E` in the truncation tower of `E`. -/
noncomputable abbrev derivedTruncationGEStep
    (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    derivedTruncationGEStage X E (n + 1) ⟶ derivedTruncationGEStage X E n :=
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

/-- The inverse system `n ↦ τ_{\ge -n} E` in `D(\mathcal O_X)`. -/
noncomputable abbrev derivedTruncationGETower
    (E : DerivedCategory (ringedSpaceModuleCat X)) :
    ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X) :=
  Functor.ofOpSequence (derivedTruncationGEStep X E)

/-- The family of objects underlying the truncation tower of `E`. -/
abbrev derivedTruncationGETowerFamily
    (E : DerivedCategory (ringedSpaceModuleCat X)) :
    ℕ → DerivedCategory (ringedSpaceModuleCat X) :=
  fun n ↦ (derivedTruncationGETower X E).obj (Opposite.op n)

/-- The Milnor difference map `(x_n) ↦ (x_n - f_{n+1}(x_{n+1}))` for the truncation tower of
`E`. -/
def derivedTruncationGETowerDifferenceMap
    (E : DerivedCategory (ringedSpaceModuleCat X))
    [HasProduct (derivedTruncationGETowerFamily X E)] :
    ∏ᶜ derivedTruncationGETowerFamily X E ⟶ ∏ᶜ derivedTruncationGETowerFamily X E :=
  Pi.lift fun n ↦
    Pi.π (derivedTruncationGETowerFamily X E) n -
      Pi.π (derivedTruncationGETowerFamily X E) (n + 1) ≫
        (derivedTruncationGETower X E).map ((homOfLE (Nat.le_succ n)).op)

/-- The canonical map `E ⟶ τ_{\ge -n} E` obtained from truncating a chosen cochain-complex
representative of `E`. -/
noncomputable abbrev derivedTruncationGEToStage
    (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    E ⟶ derivedTruncationGEStage X E n :=
  (Q.objObjPreimageIso E).inv ≫
    Q.map ((Q.objPreimage E).πTruncGE (-((n : ℕ) : ℤ)))

/-- A morphism `c : E ⟶ L` is a compatible comparison from `E` to a chosen derived limit of the
truncation tower `(\tau_{\ge -n} E)_n` if `L` sits in the Milnor triangle and the stage
projections recover the canonical maps `E ⟶ τ_{\ge -n} E`. -/
def IsTruncationDerivedLimitComparison
    (E L : DerivedCategory (ringedSpaceModuleCat X)) (c : E ⟶ L) : Prop :=
  ∃ _ : HasProduct (derivedTruncationGETowerFamily X E),
    ∃ (ι : L ⟶ ∏ᶜ derivedTruncationGETowerFamily X E)
      (δ : ∏ᶜ derivedTruncationGETowerFamily X E ⟶ L⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedTruncationGETowerDifferenceMap X E) δ ∈
          distTriang (DerivedCategory (ringedSpaceModuleCat X)) ∧
        ∀ n : ℕ, c ≫ ι ≫ Pi.π (derivedTruncationGETowerFamily X E) n =
          derivedTruncationGEToStage X E n

-- Proof sketch: apply Lemma `20.37.7` with the constant local bound `d_x = d` for every point
-- `x ∈ X`. Since `𝓑` is a topological basis, each neighborhood `W` of `x` contains some
-- `U ∈ 𝓑` with `x ∈ U ⊆ W`, and the assumed vanishing on basis opens supplies the required local
-- vanishing hypothesis for the negative cohomology sheaves of `E`.
/-- Lemma 20.37.9: let `(X, \mathcal O_X)` be a ringed space and let `E ∈ D(\mathcal O_X)`.
Assume there exist an integer `d ≥ 0` and a basis `\mathcal B` for the topology of `X` such
that `H^p(U, H^q(E)) = 0` for `U ∈ \mathcal B`, `p > d`, and `q < 0`. Then any compatible
comparison morphism formalizing the canonical map
`E \to R\!\varprojlim_n \tau_{\ge -n} E` from Remark `13.34.5` is an isomorphism in
`D(\mathcal O_X)`. -/
theorem truncationComparison_isIso_of_basiswise_negative_cohomologySheaf_vanishing
    (E : DerivedCategory (ringedSpaceModuleCat X))
    {K : DerivedCategory (ringedSpaceModuleCat X)}
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison X E K c)
    (𝓑 : Set (Opens X.carrier))
    (h𝓑 : Opens.IsBasis 𝓑)
    (d : ℕ)
    (hvanish :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, d < p →
          ∀ q : ℤ, q < 0 →
            IsZero ((ringedSpaceCohomologySheaf X E q).H' p U)) :
    IsIso c := sorry

end

end AlgebraicGeometry.RingedSpace
