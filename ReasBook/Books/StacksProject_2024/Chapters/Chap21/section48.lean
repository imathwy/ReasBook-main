import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_48_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X)]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).flip.obj X)]

/- Domain-style sampling for Lemma 21.48.1:
- primary domain: the symmetric monoidal structure on cochain complexes of `\mathcal O`-modules on
  a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  the Chapter 15 owner instance `SymmetricCategory (CochainComplex C ℤ)`,
  `SymmetricCategory`,
  `SymmetricCategory.symmetry`;
- best owner abstraction: `SymmetricCategory Cpx`;
- primitive data: the ambient owner category `Mod` and the monoidal symmetric/additive tensor data
  on `Mod` required by the Chapter 15 cochain-complex owner;
- derived API: the canonical braiding `β_` and its symmetry theorem
  `SymmetricCategory.symmetry`.

Source/core/bridge triage:
- `source-facing`: complexes of `\mathcal O`-modules on a ringed site form a symmetric monoidal
  category for total-complex tensor product;
- `core/canonical`: `SymmetricCategory Cpx`;
- `bridge/view`: the canonical braiding symmetry equation on `Cpx`.

This item is recall-only. The previous local `RingedSiteModules` alias, braiding wrapper, and
renamed symmetry theorem duplicated the chapter owner and mathlib owner API without adding new
mathematics, so they are removed in favor of direct canonical owner use specialized to `Cpx`.
-/

/- Lemma 21.48.1: the statement that cochain complexes of `\mathcal O`-modules on a ringed site
form a symmetric monoidal category for total-complex tensor product is the canonical owner
`SymmetricCategory`, specialized in this file to `Cpx = CochainComplex (ringedSiteModuleCategory
J 𝒪) ℤ`. -/
#synth SymmetricCategory Cpx

end

end SheafOfModules.RingedSite

/-! ### Example_21_48_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ
local notation "ModLoc" U => LocalizedRingedSiteModules J 𝒪 U

/-- Restriction to a localized ringed site preserves zero morphisms. -/
private instance localizedRestriction_preservesZeroMorphisms
    (U : C) :
    (RingedSite.Hom.localizedRestriction X U).PreservesZeroMorphisms where
  map_zero _ _ := by
    rfl

/-- Restriction of cochain complexes of `\mathcal O`-modules to the localized ringed site over
`U`. -/
private abbrev localizedRestrictionComplex (U : C) :
    Cpx ⥤ CochainComplex (ModLoc U) ℤ :=
  (RingedSite.Hom.localizedRestriction X U).mapHomologicalComplex (ComplexShape.up ℤ)

namespace CochainComplex

/-- A complex of `\mathcal O`-modules on a ringed site is locally strictly perfect if every object
`U` admits a covering on whose members the restricted complex is strictly perfect. -/
def IsLocallyStrictlyPerfect (E : Cpx) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    IsStrictlyPerfect ((localizedRestrictionComplex I.Y).obj E)

end CochainComplex

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

namespace CochainComplex

/-- Unfolding `IsLocallyStrictlyPerfect` gives the explicit covering criterion by strictly perfect
restrictions. -/
theorem cochainComplex_isLocallyStrictlyPerfect_iff
    (E : Cpx) :
    IsLocallyStrictlyPerfect E ↔
      ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
        IsStrictlyPerfect ((localizedRestrictionComplex I.Y).obj E) :=
  Iff.rfl

end CochainComplex

end

section DualitySetup

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

open SheafOfModules.RingedSite.CochainComplex

section Duality

variable [MonoidalCategory (CochainComplex (RingedSiteModules J 𝒪) ℤ)]
variable [BraidedCategory (CochainComplex (RingedSiteModules J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (RingedSiteModules J 𝒪) ℤ)]

/-- The internal-Hom dual complex of `F^\bullet`, namely the canonical internal-Hom object from
`F^\bullet` to the tensor unit. -/
abbrev ringedSiteModuleComplexDual (F : Cpx) : Cpx :=
  (ihom F).obj (𝟙_ Cpx)

/-- The canonical morphism
`K^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O) \to
\mathcal H\!\mathit{om}^\bullet(F^\bullet, K^\bullet)`. -/
noncomputable def ringedSiteModuleComplexEvaluationHom
    (F K : Cpx) :
    K ⊗ ringedSiteModuleComplexDual F ⟶ (ihom F).obj K :=
  (β_ K (ringedSiteModuleComplexDual F)).hom ≫
    (ringedSiteModuleComplexDual F ◁ (unitIsoSelf K).symm.hom) ≫
    comp F (𝟙_ Cpx) K

/-- The canonical tensor-to-endomorphism morphism
`F^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O) \to
\mathcal H\!\mathit{om}^\bullet(F^\bullet, F^\bullet)`. -/
noncomputable abbrev ringedSiteModuleComplexDualTensorToEnd
    (F : Cpx) :
    F ⊗ ringedSiteModuleComplexDual F ⟶ (ihom F).obj F :=
  ringedSiteModuleComplexEvaluationHom F F

-- Proof sketch: work locally on an arbitrary object `U` of the site. On a covering where the
-- restricted complex is strictly perfect, the degreewise finite projective duality from More on
-- Algebra, Lemma `15.73.2`, gives the tensor-to-endomorphism isomorphism on each localized ringed
-- site; then glue these local isomorphisms.
/-- The canonical tensor-to-endomorphism map is an isomorphism for a complex that is locally
strictly perfect on a ringed site. -/
theorem ringedSiteModuleComplexDualTensorToEnd_isIso_of_isLocallyStrictlyPerfect
    {F : Cpx}
    (hF : IsLocallyStrictlyPerfect F) :
    IsIso (ringedSiteModuleComplexDualTensorToEnd F) := sorry

/-- The source-facing evaluation morphism
`\mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O) \otimes F^\bullet \to \mathcal O`
for the internal-Hom dual complex. -/
noncomputable def ringedSiteModuleComplexDualEvaluation
    (F : Cpx) :
    ringedSiteModuleComplexDual F ⊗ F ⟶ 𝟙_ Cpx :=
  (β_ (ringedSiteModuleComplexDual F) F).hom ≫
    (ihom.ev F).app (𝟙_ Cpx)

/-- The source-facing coevaluation morphism
`\mathcal O \to F^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O)`
obtained from the identity of `F^\bullet` via the tensor-to-endomorphism isomorphism. -/
noncomputable def ringedSiteModuleComplexDualCoevaluation
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    𝟙_ Cpx ⟶ F ⊗ ringedSiteModuleComplexDual F :=
  MonoidalClosed.curry' (𝟙 F) ≫
    inv (ringedSiteModuleComplexDualTensorToEnd F)

-- Proof sketch: transport the identity endomorphism of the dual complex across the
-- tensor-to-endomorphism isomorphism. Under the closed monoidal adjunction this becomes exactly
-- the first triangle identity.
/-- The source-facing coevaluation and evaluation maps of the internal-Hom dual satisfy the first
triangle identity. -/
theorem ringedSiteModuleComplexDual_coevaluation_evaluation
    {F : Cpx}
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    ringedSiteModuleComplexDual F ◁ ringedSiteModuleComplexDualCoevaluation F ≫
        (α_ _ _ _).inv ≫
        ringedSiteModuleComplexDualEvaluation F ▷ ringedSiteModuleComplexDual F =
      (ρ_ (ringedSiteModuleComplexDual F)).hom ≫
        (λ_ (ringedSiteModuleComplexDual F)).inv := sorry

-- Proof sketch: transport the identity of `F^\bullet` across the same tensor-to-endomorphism
-- isomorphism. The defining property of the coevaluation map then yields the second triangle
-- identity.
/-- The source-facing coevaluation and evaluation maps of the internal-Hom dual satisfy the second
triangle identity. -/
theorem ringedSiteModuleComplexDual_evaluation_coevaluation
    {F : Cpx}
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    ringedSiteModuleComplexDualCoevaluation F ▷ F ≫
        (α_ _ _ _).hom ≫
        F ◁ ringedSiteModuleComplexDualEvaluation F =
      (λ_ F).hom ≫ (ρ_ F).inv := sorry

/-- The source-facing tensor/unit maps package `\mathcal H\!\mathit{om}^\bullet(F^\bullet,
\mathcal O)` as the right-dual-style bridge needed before passing to the canonical left-dual owner
surface. -/
@[reducible] private noncomputable def exactPairingOfIsIso
    (F : Cpx)
    [IsIso (ringedSiteModuleComplexDualTensorToEnd F)] :
    ExactPairing (ringedSiteModuleComplexDual F) F :=
  letI : ExactPairing F (ringedSiteModuleComplexDual F) :=
    { coevaluation' := ringedSiteModuleComplexDualCoevaluation F
      evaluation' := ringedSiteModuleComplexDualEvaluation F
      coevaluation_evaluation' := ringedSiteModuleComplexDual_coevaluation_evaluation
      evaluation_coevaluation' := ringedSiteModuleComplexDual_evaluation_coevaluation }
  BraidedCategory.exactPairing_swap F (ringedSiteModuleComplexDual F)

/-- Example 21.48.2: if a complex `\mathcal F^\bullet` of `\mathcal O`-modules on a ringed site
is locally strictly perfect, then the internal-Hom dual
`\mathcal G^\bullet = \mathcal H\!\mathit{om}^\bullet(\mathcal F^\bullet, \mathcal O)` is a left
dual of `\mathcal F^\bullet`. In Lean this left-duality datum is packaged by the canonical owner
`CategoryTheory.ExactPairing (ringedSiteModuleComplexDual F) (\mathcal F^\bullet)`. -/
noncomputable abbrev ringedSiteModuleComplexDualExactPairing
    {F : Cpx}
    (hF : IsLocallyStrictlyPerfect F) :
    ExactPairing (ringedSiteModuleComplexDual F) F := by
  letI : IsIso (ringedSiteModuleComplexDualTensorToEnd F) :=
    ringedSiteModuleComplexDualTensorToEnd_isIso_of_isLocallyStrictlyPerfect hF
  exact exactPairingOfIsIso F

end Duality

end DualitySetup

end SheafOfModules.RingedSite

/-! ### Lemma_21_48_3 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

section

variable [MonoidalCategory (CochainComplex (RingedSiteModules J 𝒪) ℤ)]

-- Proof sketch: write the coevaluation and evaluation of the chosen left dual degreewise. The
-- triangle identities induce left duals between `G.X n` and `F.X n`, so Lemma `18.29.2`
-- applied on each localized ringed site shows that every term of `F` becomes locally a direct
-- summand of a finite free module. As in the module-complex argument of More on Algebra,
-- Lemma `15.73.2`, the coevaluation has only finitely many nonzero homogeneous components after
-- passing to a cover, which yields local boundedness and hence local strict perfectness.
/-- Lemma 21.48.3: if a complex `\mathcal F^\bullet` of `\mathcal O`-modules on a ringed site has
a left dual in the monoidal category of complexes of `\mathcal O`-modules, then
`\mathcal F^\bullet` is locally strictly perfect, i.e. every object `U` admits a covering on
whose members the restricted complex is strictly perfect. -/
theorem exactPairing_isLocallyStrictlyPerfect
    {F G : Cpx} (hpair : ExactPairing G F) :
    CochainComplex.IsLocallyStrictlyPerfect F := sorry

section

variable [BraidedCategory (CochainComplex (RingedSiteModules J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (RingedSiteModules J 𝒪) ℤ)]

/-- The canonical uniqueness isomorphism from a chosen left dual of `F^\bullet` to the internal-Hom
object `\mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O)` produced in Example `21.48.2`
once `F^\bullet` is known to be locally strictly perfect. -/
noncomputable def exactPairing_leftDualIso_internalHomToUnit
    {F G : Cpx} (hpair : ExactPairing G F) :
    G ≅ (ihom F).obj (𝟙_ Cpx) :=
  leftDualIso hpair
    (ringedSiteModuleComplexDualExactPairing
      (exactPairing_isLocallyStrictlyPerfect hpair))

end

end

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_48_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.48.5:
- primary domain: the symmetric monoidal structure on the derived category of sheaves of modules on
  a ringed site;
- sampled owner declarations:
  `RingedSiteModules`,
  `DerivedCategory`,
  `SymmetricCategory`,
  `SymmetricCategory.symmetry`;
- best owner abstraction: `SymmetricCategory (DerivedCategory (RingedSiteModules J 𝒪))`;
- primitive data: the ringed-site module category `RingedSiteModules J 𝒪`, its derived category,
  and the ambient monoidal/symmetric structure on that derived category;
- derived API: the canonical braiding `β_` and the symmetry theorem
  `SymmetricCategory.symmetry`.

Source/core/bridge triage:
- `source-facing`: the commutativity constraint for derived tensor product on `D(\mathcal O)` is
  involutive;
- `core/canonical`: `SymmetricCategory DMod` for `DMod := DerivedCategory (RingedSiteModules J 𝒪)`;
- `bridge/view`: the specialization of `SymmetricCategory.symmetry` to objects of `D(\mathcal O)`.

This item is bridge/view only. The previous local wheel duplicated the canonical owner
`SymmetricCategory.symmetry`; the refined file now recalls that owner directly on the chapter
vocabulary `D(\mathcal O)` without importing unrelated ringed-site restriction API.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "DMod" => DerivedCategory Mod

variable [MonoidalCategory DMod]
variable [SymmetricCategory DMod]

/- Lemma 21.48.5: for the derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on
a ringed site, the symmetry relation for the derived-tensor braiding is exactly the canonical
theorem `SymmetricCategory.symmetry` specialized to `D(\mathcal O)`. -/
recall SymmetricCategory.symmetry (X Y : DMod) :
  (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y)

end

end SheafOfModules.RingedSite
