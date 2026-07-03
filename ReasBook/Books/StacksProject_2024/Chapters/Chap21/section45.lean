import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_45_1 (from Chap21) -/
open CategoryTheory
open ComplexShape
open RingedSite.Hom

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Definition 21.45.1:
- primary domain: pseudo-coherence for complexes and derived `\mathcal O`-modules on a ringed
  site, expressed through local strictly perfect models on localized ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `RingedSite.Hom.localizedRestriction`,
  `CochainComplex.IsStrictlyPerfect`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `ringedSiteModuleCategory`;
- best owner abstraction: keep the pseudo-coherence predicates as the source-facing owners, but
  organize the ambient module and derived categories through the ringed-site owner
  `X := RingedSite.ofCommRingSheaf J 𝒪`, reusing `ModuleCat X`, `ModuleDerived X`,
  `localizedRestriction X U`, and `localizedRestrictionDerived X U` instead of parallel local
  wheel declarations; representative criteria remain bridge theorems;
- primitive data: a cover of each localized object, a strictly perfect complex on each cover
  member, and a comparison morphism controlling cohomology above degree `m` and in degree `m`;
- derived API: the complex predicates and the intrinsic derived predicates.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent`;
- `core/canonical`: `RingedSite.Hom.ModuleCat`, `RingedSite.Hom.ModuleDerived`,
  `CochainComplex.IsStrictlyPerfect`, `RingedSite.Hom.localizedRestrictionDerived`,
  `DerivedCategory.IsMPseudoCoherent`, and `DerivedCategory.IsPseudoCoherent`;
- `bridge/view`: the representative criteria for the derived predicates.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ((J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v}))]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, ((J.over U).WEqualsLocallyBijective AddCommGrpCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ
local notation "ModLoc" U => LocalizedRingedSiteModules J 𝒪 U

variable [∀ U : C,
  (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).PreservesZeroMorphisms]
variable [∀ U : C, (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
variable [∀ U : C,
  CategoryTheory.Limits.PreservesFiniteLimits
    (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C,
  CategoryTheory.Limits.PreservesFiniteColimits
    (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]

variable [CategoryWithHomology Mod]
variable [∀ U : C, CategoryWithHomology (ModLoc U)]

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪

namespace CochainComplex

/-- Definition 21.45.1: a complex of `\mathcal O`-modules on a ringed site is
`m`-pseudo-coherent if, after passing to a covering of every object `U`, its restriction to each
member of the cover admits a map from a strictly perfect complex inducing cohomology
isomorphisms in degrees `> m` and a surjection in degree `m`. -/
def IsMPseudoCoherent (E : Cpx) (m : ℤ) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
      CochainComplex.IsStrictlyPerfect E' ∧
        ∃ α :
          E' ⟶
            ((localizedRestriction X I.Y).mapHomologicalComplex (up ℤ)).obj E,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α m)

/-- A complex of `\mathcal O`-modules on a ringed site is pseudo-coherent if it is
`m`-pseudo-coherent for every integer `m`. -/
def IsPseudoCoherent (E : Cpx) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent E m

end CochainComplex

variable [Abelian Mod]
local notation "DMod" => ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)

namespace DerivedCategory

/-- Definition 21.45.1 (derived `m`-version): an object of `D(\mathcal O)` is
`m`-pseudo-coherent if, after passing to a covering of every object `U`, each restricted derived
object is approximated by a strictly perfect complex inducing cohomology isomorphisms in degrees
`> m` and an epimorphism in degree `m`. -/
def IsMPseudoCoherent (K : DMod) (m : ℤ) : Prop :=
  ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
      CochainComplex.IsStrictlyPerfect E' ∧
        ∃ α :
          DerivedCategory.Q.obj E' ⟶
            (localizedRestrictionDerived X I.Y).obj K,
          (∀ j : ℤ, m < j →
            IsIso ((DerivedCategory.homologyFunctor (ModLoc I.Y) j).map α)) ∧
              Epi ((DerivedCategory.homologyFunctor (ModLoc I.Y) m).map α)

/-- An object of `D(\mathcal O)` is pseudo-coherent if it is `m`-pseudo-coherent for every
integer `m`. -/
def IsPseudoCoherent (K : DMod) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent K m

end DerivedCategory

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_45_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable (Mod : Type w) [Category.{v} Mod] [Abelian Mod]
variable (ModLoc : C → Type w)
variable [∀ U : C, Category.{v} (ModLoc U)]
variable [∀ U : C, Abelian (ModLoc U)]

/- The parameter `strictlyPerfect U` stands for the strict-perfectness predicate on complexes of
`\mathcal O_U`-modules. -/
variable (strictlyPerfect : ∀ U : C, CochainComplex (ModLoc U) ℤ → Prop)

/- The parameter `localizedRestrictionDerived U` stands for the derived restriction functor
`D(\mathcal O) → D(\mathcal O_U)`. -/
variable (localizedRestrictionDerived :
  ∀ U : C, DerivedCategory Mod ⥤ DerivedCategory (ModLoc U))

/- The parameter `complexIsMPseudoCoherent` stands for the complex-level `m`-pseudo-coherence
predicate from Definition `21.45.1`. -/
variable (complexIsMPseudoCoherent : CochainComplex Mod ℤ → ℤ → Prop)

/- The parameter `derivedIsMPseudoCoherent` stands for the derived-category `m`-pseudo-coherence
predicate from Definition `21.45.1`. -/
variable (derivedIsMPseudoCoherent : DerivedCategory Mod → ℤ → Prop)

/- The parameter `localizedDerivedIsMPseudoCoherent U` stands for `m`-pseudo-coherence on the
localized ringed site over `U`. -/
variable (localizedDerivedIsMPseudoCoherent :
  ∀ U : C, DerivedCategory (ModLoc U) → ℤ → Prop)

section

variable {J : GrothendieckTopology C}
variable {Mod : Type w} [Category.{v} Mod] [Abelian Mod]
variable {ModLoc : C → Type w}
variable [∀ U : C, Category.{v} (ModLoc U)]
variable [∀ U : C, Abelian (ModLoc U)]
variable {strictlyPerfect : ∀ U : C, CochainComplex (ModLoc U) ℤ → Prop}
variable {localizedRestrictionDerived :
  ∀ U : C, DerivedCategory Mod ⥤ DerivedCategory (ModLoc U)}

/-- A localized derived object over `U` admits a strict-perfect approximation in degree `m` when
it is represented by a strictly perfect complex whose comparison morphism induces cohomology
isomorphisms above `m` and an epimorphism in degree `m`. -/
abbrev HasStrictlyPerfectApproximationInDegree
    (U : C) (K : DerivedCategory Mod) (m : ℤ) : Prop :=
  ∃ E' : CochainComplex (ModLoc U) ℤ,
    strictlyPerfect U E' ∧
      ∃ α :
        ((DerivedCategory.Q :
            CochainComplex (ModLoc U) ℤ ⥤
              DerivedCategory (ModLoc U)).obj E') ⟶
          (localizedRestrictionDerived U).obj K,
        (∀ j : ℤ, m < j →
          IsIso ((DerivedCategory.homologyFunctor (ModLoc U) j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor (ModLoc U) m).map α)

end

/- Local shorthand for the strict-perfect approximation predicate used in Lemma `21.45.2`. -/
local notation "LocalApproximationInDegree" =>
  @HasStrictlyPerfectApproximationInDegree
    C Mod _ _ ModLoc _ _ strictlyPerfect localizedRestrictionDerived

-- Proof sketch: choose a complex representing `K`. By Lemma `21.44.8`, after refining the given
-- cover of the final object `X`, each local derived morphism from a strictly perfect complex is
-- represented by an actual chain map to the localized representative complex. Since `X` is final,
-- covers of `X` restrict to covers of every object of `C`, and the resulting local chain maps are
-- exactly the data required in Definition `21.45.1`.
/-- Lemma 21.45.2 (1): if a derived `\mathcal O`-module admits on a cover of a final object local
strictly perfect approximations with cohomology isomorphisms above `m` and an epimorphism in
degree `m`, then it is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_exists_cover_on_finalObject
    (K : DerivedCategory Mod) (m : ℤ) (X : C) (_hX : Limits.IsTerminal X)
    (hcover :
      ∃ T : J.Cover X, ∀ I : T.Arrow,
        LocalApproximationInDegree I.Y K m) :
    derivedIsMPseudoCoherent K m := sorry

-- Proof sketch: unfold `derivedIsMPseudoCoherent K m` to obtain some representing complex `E`.
-- Transport the chosen representation `F ≅ K` to an isomorphism `Q.obj F ≅ Q.obj E`. Refining
-- the local covers and applying Lemma `21.44.8` transfers the strictly perfect local
-- approximations from `E` to `F`, which is exactly the condition `complexIsMPseudoCoherent F m`.
/-- Lemma 21.45.2 (2): if `K` is `m`-pseudo-coherent, then every complex representing `K` is
`m`-pseudo-coherent as a complex of `\mathcal O`-modules. -/
theorem cochainComplex_isMPseudoCoherent_of_represents_isMPseudoCoherent
    (K : DerivedCategory Mod) (F : CochainComplex Mod ℤ) (m : ℤ)
    (e : ((DerivedCategory.Q : CochainComplex Mod ℤ ⥤ DerivedCategory Mod).obj F) ≅ K)
    (hK : derivedIsMPseudoCoherent K m) :
    complexIsMPseudoCoherent F m := sorry

-- Proof sketch: apply the local hypothesis to the terminal object `U` occurring in the definition
-- of complex-level `m`-pseudo-coherence. For each member of the chosen cover of `U`, unfold the
-- assumption that the restriction of `K` is `m`-pseudo-coherent and compose the corresponding
-- covers using the site-composition axiom from Definition `7.6.2`; this gives the local strictly
-- perfect approximations required for `K` itself.
/-- Lemma 21.45.2 (3): if every object of the site admits a covering on which the localized
restriction of `K` is `m`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_locally_isMPseudoCoherent
    (K : DerivedCategory Mod) (m : ℤ)
    (hlocal :
      ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
        localizedDerivedIsMPseudoCoherent I.Y
          ((localizedRestrictionDerived I.Y).obj K) m) :
    derivedIsMPseudoCoherent K m := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_45_3 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪D : Sheaf JC RingCat.{max u v}} {𝒪C : Sheaf JD RingCat.{max u v}}
variable (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪C)
variable [(SheafOfModules.pushforward φ).IsRightAdjoint]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on a ringed site with
structure sheaf `\mathcal O`. -/
private abbrev RingedSiteModules
    {E : Type u} [Category.{v} E] (J : GrothendieckTopology E)
    (𝒪 : Sheaf J RingCat.{max u v}) :=
  SheafOfModules 𝒪

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules. -/
private abbrev RingedSiteDerived
    {E : Type u} [Category.{v} E] (J : GrothendieckTopology E)
    (𝒪 : Sheaf J RingCat.{max u v}) :=
  DerivedCategory (RingedSiteModules J 𝒪)

/-- The quasi-isomorphisms in the homotopy category of cochain complexes of
`\mathcal O`-modules. -/
private abbrev RingedSiteQis
    {E : Type u} [Category.{v} E] (J : GrothendieckTopology E)
    (𝒪 : Sheaf J RingCat.{max u v}) :=
  HomotopyCategory.quasiIso (RingedSiteModules J 𝒪) (up ℤ)

/-- The pullback functor on module sheaves attached to the site-presented morphism of ringed
sites determined by `φ`. -/
private abbrev pullbackFunctor
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪C)
    [(SheafOfModules.pushforward φ).IsRightAdjoint] :
    RingedSiteModules JC 𝒪D ⥤ RingedSiteModules JD 𝒪C :=
  SheafOfModules.pullback φ

/-- The functor on homotopy categories induced by pullback on module sheaves. -/
private abbrev mapHomotopyCategoryToDerived
    {A B : Type _} [Category A] [Preadditive A] [Category B] [Abelian B] (G : A ⥤ B)
    [G.Additive] :
    HomotopyCategory A (up ℤ) ⥤ DerivedCategory B :=
  G.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The functor on homotopy categories induced by pullback on module sheaves. -/
private abbrev pullbackToDerived
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪C)
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    [(pullbackFunctor F φ).Additive] :=
  mapHomotopyCategoryToDerived (pullbackFunctor F φ)

/-- The unbounded derived pullback functor `Lf^* : D(\mathcal O_\mathcal D) \to
D(\mathcal O_\mathcal C)`. -/
private noncomputable abbrev pullbackDerived
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪C)
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    [(pullbackFunctor F φ).Additive]
    [Functor.HasLeftDerivedFunctor (pullbackToDerived F φ) (RingedSiteQis JC 𝒪D)] :
    RingedSiteDerived JC 𝒪D ⥤ RingedSiteDerived JD 𝒪C :=
  Functor.totalLeftDerived (pullbackToDerived F φ)
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSiteModules JC 𝒪D) (up ℤ) ⥤
        RingedSiteDerived JC 𝒪D)
    (RingedSiteQis JC 𝒪D)

-- Proof sketch: choose a representative complex for `E` together with local strictly perfect
-- approximations realizing `m`-pseudo-coherence. Pull those approximations back along `f`,
-- localize to reduce to the final-object case, preserve strict perfectness under pullback, and
-- use the cone-vanishing argument for left derived functors to keep the cohomological control in
-- degrees `> m` and degree `m`.
/-- Lemma 21.45.3: for a site-presented morphism of ringed sites determined by `φ`, if
`E ∈ D(\mathcal O_\mathcal D)` is `m`-pseudo-coherent, then the derived pullback `Lf^*E` is
`m`-pseudo-coherent in `D(\mathcal O_\mathcal C)`. -/
theorem pullbackDerived_isMPseudoCoherent
    (sourceIsMPseudoCoherent : RingedSiteDerived JC 𝒪D → ℤ → Prop)
    (targetIsMPseudoCoherent : RingedSiteDerived JD 𝒪C → ℤ → Prop)
    [(pullbackFunctor F φ).Additive]
    [Functor.HasLeftDerivedFunctor (pullbackToDerived F φ) (RingedSiteQis JC 𝒪D)]
    (E : RingedSiteDerived JC 𝒪D) (m : ℤ)
    (hE : sourceIsMPseudoCoherent E m) :
    targetIsMPseudoCoherent ((pullbackDerived F φ).obj E) m := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_45_4 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => DerivedCategory Mod

variable [Abelian Mod]

/- The parameter `IsMPseudoCoherent` stands for the site-level `m`-pseudo-coherence predicate on
`D(\mathcal O)` from Definition `21.45.1`. -/
variable (IsMPseudoCoherent : DMod → ℤ → Prop)

variable {J 𝒪 IsMPseudoCoherent}
variable {m : ℤ}

-- Proof sketch: choose strictly perfect local models for `T.obj₁` in degree `m + 1` and for
-- `T.obj₂` in degree `m`, lift the morphism `T.mor₁ : T.obj₁ ⟶ T.obj₂` locally to a morphism of
-- complexes, and compare the cone triangle with `T`. The cone stays strictly perfect, and the
-- long exact homology sequence shows the third vertex is `m`-pseudo-coherent.
/-- Lemma 21.45.4 (1): in a distinguished triangle in `D(\mathcal O)`, if the first term is
`(m + 1)`-pseudo-coherent and the second term is `m`-pseudo-coherent, then the third term is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₃_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : IsMPseudoCoherent T.obj₁ (m + 1))
    (h₂ : IsMPseudoCoherent T.obj₂ m) :
    IsMPseudoCoherent T.obj₃ m := sorry

-- Proof sketch: rotate the distinguished triangle once and apply part `(1)` to the rotated
-- triangle, where the hypotheses on the first and third vertices become the required first-two
-- hypotheses after rotation.
/-- Lemma 21.45.4 (2): in a distinguished triangle in `D(\mathcal O)`, if the first and third
terms are `m`-pseudo-coherent, then the second term is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₂_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : IsMPseudoCoherent T.obj₁ m)
    (h₃ : IsMPseudoCoherent T.obj₃ m) :
    IsMPseudoCoherent T.obj₂ m := sorry

-- Proof sketch: rotate the distinguished triangle so that the original third vertex becomes the
-- second and the original first vertex becomes the shifted first term, then apply part `(1)` to
-- conclude that the original first term is `(m + 1)`-pseudo-coherent.
/-- Lemma 21.45.4 (3): in a distinguished triangle in `D(\mathcal O)`, if the second term is
`(m + 1)`-pseudo-coherent and the third term is `m`-pseudo-coherent, then the first term is
`(m + 1)`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₁_of_distinguished_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : IsMPseudoCoherent T.obj₂ (m + 1))
    (h₃ : IsMPseudoCoherent T.obj₃ m) :
    IsMPseudoCoherent T.obj₁ (m + 1) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_45_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped RingedSiteDerivedTensor

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => DerivedCategory Mod
local notation "H" => DerivedCategory.homologyFunctor Mod

/- Domain-style sampling for Lemma 21.45.5:
- primary domain: pseudo-coherence for derived `\mathcal O`-modules on a ringed site and its
  behavior under derived tensor product;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.derivedTensorProduct`,
  `SheafOfModules.RingedSite.DerivedCategory.IsMPseudoCoherent`,
  `SheafOfModules.RingedSite.DerivedCategory.IsPseudoCoherent`;
- best owner abstraction: the source-facing theorem should use the ambient module-category owner
  `ringedSiteModuleCategory J 𝒪` and its derived category `DerivedCategory Mod`, together with the
  intrinsic predicates `K.IsMPseudoCoherent m` and `K.IsPseudoCoherent` and the canonical Chapter
  21 derived tensor object `K ⊗^L L`;
- primitive data: the ringed site, the derived objects `K` and `L`, the integer bounds
  `n m a b`, and the homology-vanishing hypotheses;
- derived API: tensor-product closure theorems for `m`-pseudo-coherence and pseudo-coherence.

Source/core/bridge triage:
- `source-facing`: Lemma 21.45.5 itself, asserting pseudo-coherence for a derived tensor product;
- `core/canonical`: the owner predicates `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`, the owner `derivedTensorProduct` with notation `K ⊗^L L`,
  and the chapter owner `ringedSiteModuleCategory J 𝒪` with its derived category
  `DerivedCategory Mod`;
- `bridge/view`: the bounded-above representative and local strictly perfect model arguments used
  in proofs, which should not be promoted to a second public owner layer.
-/

variable [Abelian Mod]
variable [CategoryWithHomology Mod]
variable [HasCountableCoproducts Mod]
variable [MonoidalCategory Mod]
variable [MonoidalPreadditive Mod]
variable [HasColimits Mod]
variable [(curriedTensor Mod).Additive]
variable [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]
variable [∀ (K L : CochainComplex Mod ℤ), CochainComplex.HasMapBifunctor K L (curriedTensor Mod)]

-- Proof sketch: apply the local strictly perfect approximation criterion from Definition
-- `21.45.1` to `K` and `L` on a common covering, tensor the local models, and use the Tor spectral
-- sequence together with the vanishing hypotheses to obtain the bound `max (m + a, n + b)`.
/-- Lemma 21.45.5 (1): if `K` is `n`-pseudo-coherent with vanishing cohomology above `a` and `L`
is `m`-pseudo-coherent with vanishing cohomology above `b`, then
`K \otimes_{\mathcal O}^{\mathbf L} L` is `max (m + a, n + b)`-pseudo-coherent. -/
theorem derivedTensorProduct_isMPseudoCoherent_of_isMPseudoCoherent_of_vanishingAbove
    (K L : DMod) (n m a b : ℤ)
    (hK : K.IsMPseudoCoherent n)
    (hKvanish : ∀ i : ℤ, a < i → IsZero ((H i).obj K))
    (hL : L.IsMPseudoCoherent m)
    (hLvanish : ∀ j : ℤ, b < j → IsZero ((H j).obj L)) :
    (K ⊗^L L).IsMPseudoCoherent (max (m + a) (n + b)) :=
  sorry

-- Proof sketch: choose pseudo-coherent representatives for `K` and `L`, replace them locally by
-- bounded-above strictly perfect models as in the textbook proof, and apply part `(1)` degreewise
-- to conclude that the canonical derived tensor object is pseudo-coherent.
/-- Lemma 21.45.5 (2): if `K` and `L` are pseudo-coherent, then
`K \otimes_{\mathcal O}^{\mathbf L} L` is pseudo-coherent. -/
theorem derivedTensorProduct_isPseudoCoherent_of_isPseudoCoherent
    (K L : DMod)
    (hK : K.IsPseudoCoherent)
    (hL : L.IsPseudoCoherent) :
    (K ⊗^L L).IsPseudoCoherent :=
  sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_45_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => DerivedCategory Mod

/-
The parameter `IsMPseudoCoherent` stands for the site-level `m`-pseudo-coherence predicate from
Definition `21.45.1`, used here as the ambient notion on `D(\mathcal O)`.
-/
variable (IsMPseudoCoherent : DerivedCategory (ringedSiteModuleCategory J 𝒪) → ℤ → Prop)

/-- A derived `\mathcal O`-module on a ringed site is pseudo-coherent if it is
`m`-pseudo-coherent for every integer `m`. -/
def IsPseudoCoherent (K : DMod) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent K m

-- Proof sketch: represent the biproduct by the split distinguished triangle from Derived
-- Categories, Lemma `13.4.10`, use Lemma `21.45.4` to show that the iterated shifts
-- `L[n] ⊞ L[n + 1]` remain `m`-pseudo-coherent, and then work backwards through the split
-- triangles to conclude that the left summand is `m`-pseudo-coherent.
/-- Lemma 21.45.6 (1): if `K ⊞ L` is `m`-pseudo-coherent in `D(\mathcal O)`, then `K` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_left_of_biprod
    (K L : DMod) (m : ℤ)
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent K m := sorry

-- Proof sketch: the same split-triangle argument, now exchanging the two summands, proves that
-- `m`-pseudo-coherence also descends to the right direct summand.
/-- Lemma 21.45.6 (2): if `K ⊞ L` is `m`-pseudo-coherent in `D(\mathcal O)`, then `L` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_right_of_biprod
    (K L : DMod) (m : ℤ)
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent L m := sorry

-- Proof sketch: unfold pseudo-coherence as `m`-pseudo-coherence for every integer and apply part
-- `(1)` degreewise.
/-- Lemma 21.45.6 (3): if `K ⊞ L` is pseudo-coherent in `D(\mathcal O)`, then `K` is
pseudo-coherent. -/
theorem isPseudoCoherent_left_of_biprod
    (K L : DMod)
    (hKL : IsPseudoCoherent J 𝒪 IsMPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent J 𝒪 IsMPseudoCoherent K := sorry

-- Proof sketch: unfold pseudo-coherence as `m`-pseudo-coherence for every integer and apply part
-- `(2)` degreewise.
/-- Lemma 21.45.6 (4): if `K ⊞ L` is pseudo-coherent in `D(\mathcal O)`, then `L` is
pseudo-coherent. -/
theorem isPseudoCoherent_right_of_biprod
    (K L : DMod)
    (hKL : IsPseudoCoherent J 𝒪 IsMPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent J 𝒪 IsMPseudoCoherent L := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_45_7 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The abelian category `\mathrm{Mod}(\mathcal O_U)` on the localized ringed site
`X.localization U`. -/
private abbrev LocalizedRingedSiteModuleCat (X : RingedSite.{u, v}) (U : X) :=
  SheafOfModules (X.structureSheaf.over U)

/-- Restriction of `\mathcal O_X`-modules to the localized ringed site `X.localization U`. -/
private abbrev localizedRestrictionFunctor (X : RingedSite.{u, v}) (U : X) :
    RingedSiteModuleCat X ⥤ LocalizedRingedSiteModuleCat X U :=
  SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U))

/-- Restriction to a localized ringed site preserves zero morphisms. -/
instance localizedRestrictionFunctor_preservesZeroMorphisms
    (X : RingedSite.{u, v}) (U : X) :
    (localizedRestrictionFunctor X U).PreservesZeroMorphisms := sorry

/-- Restriction of cochain complexes of `\mathcal O_X`-modules to the localized ringed site
`X.localization U`. -/
private abbrev localizedRestrictionComplex (X : RingedSite.{u, v}) (U : X) :
    CochainComplex (RingedSiteModuleCat X) ℤ →
      CochainComplex (LocalizedRingedSiteModuleCat X U) ℤ :=
  fun E ↦ ((localizedRestrictionFunctor X U).mapHomologicalComplex (up ℤ)).obj E

/-- A complex of `\mathcal O_U`-modules on a localized ringed site is strictly perfect when it is
bounded and each term is a retract of a finite free module. -/
private def localizedComplexIsStrictlyPerfect
    (X : RingedSite.{u, v}) {U : X}
    (E : CochainComplex (LocalizedRingedSiteModuleCat X U) ℤ) : Prop :=
  (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
    ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
      Nonempty
        (Retract (E.X i)
          (SheafOfModules.free.{max u v} I : LocalizedRingedSiteModuleCat X U))

namespace DerivedCategory

/-- A derived `\mathcal O_X`-module is `m`-pseudo-coherent if it is represented by a complex whose
restriction to every localized site becomes, after some cover, cohomologically approximable by a
strictly perfect complex above degree `m` and surjectively in degree `m`. -/
def IsMPseudoCoherent
    (X : RingedSite.{u, v}) (K : DerivedCategory (RingedSiteModuleCat X)) (m : ℤ) : Prop :=
  ∃ E : CochainComplex (RingedSiteModuleCat X) ℤ,
    (∃ _ :
        K ≅
          ((DerivedCategory.Q :
              CochainComplex (RingedSiteModuleCat X) ℤ ⥤
                DerivedCategory (RingedSiteModuleCat X)).obj E),
      ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow,
        ∃ EI : CochainComplex (LocalizedRingedSiteModuleCat X I.Y) ℤ,
          ∃ α : EI ⟶ localizedRestrictionComplex X I.Y E,
            localizedComplexIsStrictlyPerfect X EI ∧
            (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α m))

-- Proof sketch: this is a direct unfolding of the local strictly-perfect approximation condition
-- built into `IsMPseudoCoherent`.
/-- Unfolding `IsMPseudoCoherent` gives a representing complex whose localized restrictions admit
strictly perfect approximations after covers, with the specified cohomological control. -/
theorem isMPseudoCoherent_iff
    (X : RingedSite.{u, v}) (K : DerivedCategory (RingedSiteModuleCat X)) (m : ℤ) :
    IsMPseudoCoherent X K m ↔
      ∃ E : CochainComplex (RingedSiteModuleCat X) ℤ,
        (∃ _ :
            K ≅
              ((DerivedCategory.Q :
                  CochainComplex (RingedSiteModuleCat X) ℤ ⥤
                    DerivedCategory (RingedSiteModuleCat X)).obj E),
          ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow,
            ∃ EI : CochainComplex (LocalizedRingedSiteModuleCat X I.Y) ℤ,
              ∃ α : EI ⟶ localizedRestrictionComplex X I.Y E,
                localizedComplexIsStrictlyPerfect X EI ∧
                (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
                Epi (HomologicalComplex.homologyMap α m)) := sorry

end DerivedCategory

section

variable (X : RingedSite.{u, v})

local notation "ModX" => RingedSiteModuleCat X
local notation "DModX" => DerivedCategory ModX

variable [Abelian ModX]
variable [CategoryWithHomology ModX]

-- Proof sketch: fix an object `U` of the site and use `m`-pseudo-coherence to refine `U` by a
-- cover on which `K` is approximated by a strictly perfect complex inducing cohomology
-- isomorphisms above `m` and an epimorphism in degree `m`. The vanishing of `H^i(K)` for `i > m`
-- lets one trim the strictly perfect complex from the top degree downward, showing locally that
-- `H^m(K)` is a quotient of a finite free module and hence of finite type.
/-- Lemma 21.45.7 (1): if `K ∈ D(\mathcal O_X)` is `m`-pseudo-coherent and has no cohomology
above degree `m`, then `H^m(K)` is a finite type `\mathcal O_X`-module. -/
theorem top_cohomology_isFiniteType_of_isMPseudoCoherent
    (K : DModX) (m : ℤ)
    (hK : DerivedCategory.IsMPseudoCoherent X K m)
    (hvanish :
      ∀ i : ℤ, m < i →
        IsZero ((DerivedCategory.homologyFunctor ModX i).obj K)) :
    ((DerivedCategory.homologyFunctor ModX m).obj K).IsFiniteType := sorry

-- Proof sketch: again work locally on an arbitrary object and replace `K` by a strictly perfect
-- approximation controlling cohomology in degrees `> m` and degree `m`. The stronger vanishing
-- above `m + 1` lets one cut the approximation down so that locally it is concentrated in degrees
-- `≤ m + 1`, after which `H^{m+1}(K)` is identified with the cokernel of a morphism between
-- finite free modules, hence is finitely presented.
/-- Lemma 21.45.7 (2): if `K ∈ D(\mathcal O_X)` is `m`-pseudo-coherent and has no cohomology
above degree `m + 1`, then `H^{m + 1}(K)` is a finitely presented `\mathcal O_X`-module. -/
theorem next_cohomology_isFinitePresentation_of_isMPseudoCoherent
    (K : DModX) (m : ℤ)
    (hK : DerivedCategory.IsMPseudoCoherent X K m)
    (hvanish :
      ∀ i : ℤ, m + 1 < i →
        IsZero ((DerivedCategory.homologyFunctor ModX i).obj K)) :
    ((DerivedCategory.homologyFunctor ModX (m + 1)).obj K).IsFinitePresentation := sorry

end

end RingedSite
