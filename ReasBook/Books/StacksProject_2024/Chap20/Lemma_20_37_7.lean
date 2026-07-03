import Mathlib

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

/-- A derived `\mathcal O_X`-module has locally uniform vanishing of higher cohomology for its
negative cohomology sheaves if, near each point `x`, there is one bound `d_x` that annihilates
`H^p(U, H^q(E))` for all `q < 0` on some neighborhood basis of `x`. -/
def LocallyUniformNegativeCohomologySheafVanishing
    (E : DerivedCategory (ringedSpaceModuleCat X)) : Prop :=
  ∀ x : X, ∃ d : ℕ,
    ∀ W : Opens X.carrier, x ∈ W →
      ∃ U : Opens X.carrier,
        x ∈ U ∧ U ≤ W ∧
          ∀ q : ℤ, q < 0 →
            ∀ p : ℕ, d < p →
              IsZero ((ringedSpaceCohomologySheaf X E q).H' p U)

-- Proof sketch: this is immediate by unfolding
-- `LocallyUniformNegativeCohomologySheafVanishing`; the hypothesis already says that for each
-- point `x` and each neighborhood `W` of `x`, one may shrink to such a `U`.
/-- The local uniform vanishing hypothesis can be applied after shrinking inside any prescribed
open neighborhood of a point. -/
theorem LocallyUniformNegativeCohomologySheafVanishing.exists_shrunk_open
    {E : DerivedCategory (ringedSpaceModuleCat X)}
    (hE : LocallyUniformNegativeCohomologySheafVanishing X E) :
    ∀ x : X, ∃ d : ℕ,
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧ U ≤ W ∧
            ∀ q : ℤ, q < 0 →
              ∀ p : ℕ, d < p →
                IsZero ((ringedSpaceCohomologySheaf X E q).H' p U) := sorry

-- Proof sketch: convert the source hypothesis to
-- the eventual-vanishing criterion of Lemma `20.37.6` by choosing the bound
-- `p(x,m) = d_x + max (0, m)`. Then apply the previous lemma in the source development to deduce
-- that the canonical comparison map from `E` to the derived inverse limit of its truncation tower
-- is an isomorphism.
/-- Lemma 20.37.7: let `(X, \mathcal O_X)` be a ringed space and let `E ∈ D(\mathcal O_X)`.
Assume that for every `x ∈ X` there exist an integer `d_x ≥ 0` and a fundamental system of open
neighborhoods of `x` such that `H^p(U, H^q(E)) = 0` for all members `U` of that system, all
`p > d_x`, and all `q < 0`. Then any compatible comparison map
`E ⟶ R\!\varprojlim_n \tau_{\ge -n} E` from Remark `13.34.5` is an isomorphism in
`D(\mathcal O_X)`. -/
theorem isIso_of_truncationDerivedLimitComparison_of_locallyUniformNegativeCohomologySheafVanishing
    (E : DerivedCategory (ringedSpaceModuleCat X))
    {L : DerivedCategory (ringedSpaceModuleCat X)} (c : E ⟶ L)
    (hc : IsTruncationDerivedLimitComparison X E L c)
    (hE : LocallyUniformNegativeCohomologySheafVanishing X E) :
    IsIso c := sorry

end

end AlgebraicGeometry.RingedSpace
