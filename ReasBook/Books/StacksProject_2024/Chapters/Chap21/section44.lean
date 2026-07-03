import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Retract

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_44_1 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Definition 21.44.1:
- primary domain: strictly perfect cochain complexes of sheaves of modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsStrictlyGE`,
  `CochainComplex.IsStrictlyLE`,
  `SheafOfModules.free`;
- best owner abstraction: the source-facing predicate
  `CochainComplex.IsStrictlyPerfect` on the chapter vocabulary
  `RingedSiteModules J 𝒪`;
- primitive data: the ambient module category on the ringed site and, in each degree, a retract
  presentation by a finite free module;
- derived API: localized specializations on `(J.over U, 𝒪.over U)` and later local/derived
  perfectness notions built from this owner.

Source/core/bridge triage:
- `source-facing`: strict perfectness of a cochain complex of `𝒪`-modules;
- `core/canonical`: the ambient module category owner from Chapter 18 together with the single
  predicate below;
- `bridge/view`: localized and derived variants in downstream files.

There is no earlier project owner for strict perfectness itself. The duplicate wheel to remove here
is the repeated local rebinding of the ambient module category, so this file exposes the stable
chapter vocabulary below for downstream reuse. -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on a ringed site. -/
abbrev RingedSiteModules (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  ringedSiteModuleCategory J 𝒪

/-- The category `\mathrm{Mod}(\mathcal O_U)` on the localized ringed site
`(\mathcal C/U, J.over U, \mathcal O_U)`. -/
abbrev LocalizedRingedSiteModules
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C) :=
  RingedSiteModules (J.over U) (𝒪.over U)

local notation "Mod" => RingedSiteModules J 𝒪

/-- Definition 21.44.1: a complex of `\mathcal O`-modules on a ringed site `(\mathcal C,
\mathcal O)` is strictly perfect if it is zero in all but finitely many degrees and each term is a
direct summand of a finite free `\mathcal O`-module. -/
def CochainComplex.IsStrictlyPerfect
    (E : CochainComplex Mod ℤ) : Prop :=
  (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
    ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
      Nonempty (Retract (E.X i) (SheafOfModules.free I : Mod))

-- Proof sketch: unfold `CochainComplex.IsStrictlyPerfect`; for cochain complexes indexed by `ℤ`,
-- vanishing outside finitely many degrees is equivalent to simultaneous lower and upper bounds,
-- and the second clause is exactly the termwise direct-summand condition from the definition.
/-- Unfolding `IsStrictlyPerfect` gives boundedness together with the requirement that each degree
term is a retract of a finite free `\mathcal O`-module. -/
theorem cochainComplex_isStrictlyPerfect_iff
    (E : CochainComplex Mod ℤ) :
    CochainComplex.IsStrictlyPerfect E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
          Nonempty (Retract (E.X i) (SheafOfModules.free I : Mod)) :=
  Iff.rfl

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_44_2 (from Chap21) -/
noncomputable section

open CategoryTheory
open CochainComplex

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

variable {K L : Cpx}

-- Proof sketch: unfold `CochainComplex.IsStrictlyPerfect`. The cone of `f` is still bounded
-- because mapping cones of bounded cochain complexes are bounded, and each degree of
-- `CochainComplex.mappingCone f` is the biproduct of a term of `L` with a shifted term of `K`.
-- Combining the given retract presentations by finite free modules for those two terms yields the
-- corresponding retract presentation for each cone term.
/-- Lemma 21.44.2: the cone on a morphism of strictly perfect complexes of `\mathcal O`-modules on
a ringed site is strictly perfect. -/
theorem mappingCone_isStrictlyPerfect (f : K ⟶ L)
    (hK : CochainComplex.IsStrictlyPerfect K)
    (hL : CochainComplex.IsStrictlyPerfect L) :
    CochainComplex.IsStrictlyPerfect (mappingCone f) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_44_3 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace SheafOfModules.RingedSite

section

/-
Domain-style sampling for Lemma 21.44.3:
- primary domain: total tensor products of strictly perfect cochain complexes of `\mathcal O`-modules
  on a ringed site;
- sampled owner declarations:
  `RingedSiteModules`,
  `CochainComplex.IsStrictlyPerfect`,
  `HomologicalComplex.HasTensor`,
  `HomologicalComplex.tensorObj`;
- best owner abstraction: the source-facing notion is still
  `CochainComplex.IsStrictlyPerfect`, but the tensor product complex itself should be the canonical
  total tensor object `HomologicalComplex.tensorObj K L`, not an arbitrary monoidal tensor on the
  whole complex category;
- primitive data: the ambient monoidal module category `RingedSiteModules J 𝒪`, the additive
  hypotheses needed for the total tensor construction, the complexes `K`, `L`, and the instance
  `[HomologicalComplex.HasTensor K L]`;
- derived API: this lemma is the ringed-site source-facing strict-perfectness statement for that
  canonical total tensor object.

Source/core/bridge triage:
- `source-facing`: strict perfectness of the tensor product complex on a ringed site;
- `core/canonical`: `HomologicalComplex.tensorObj`;
- `bridge/view`: this file is a thin source-facing specialization of the canonical total tensor
  owner to strict perfectness on `RingedSiteModules J 𝒪`. -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [HasZeroObject (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteModules J 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules J 𝒪)]
variable [(curriedTensor (RingedSiteModules J 𝒪)).Additive]
variable [∀ M : RingedSiteModules J 𝒪,
  ((curriedTensor (RingedSiteModules J 𝒪)).obj M).Additive]

variable {K L : CochainComplex (RingedSiteModules J 𝒪) ℤ}
variable [HomologicalComplex.HasTensor K L]

-- Proof sketch: boundedness of the tensor total complex follows from boundedness of `K` and `L`.
-- In each degree, the total tensor term is assembled from finitely many tensor products of terms of
-- `K` and `L`; since retracts of finite free module sheaves are preserved under these finite
-- tensor/direct-sum constructions, each degree remains a retract of a finite free module sheaf.
/-- Lemma 21.44.3: the total complex associated to the tensor product of two strictly perfect
complexes of `\mathcal O`-modules on a ringed site is strictly perfect. In Lean, this total
complex is the canonical total tensor product `HomologicalComplex.tensorObj K L`. -/
theorem tensor_isStrictlyPerfect_of_isStrictlyPerfect
    (hK : CochainComplex.IsStrictlyPerfect K)
    (hL : CochainComplex.IsStrictlyPerfect L) :
    CochainComplex.IsStrictlyPerfect (HomologicalComplex.tensorObj K L) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_44_4 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

/-
Domain-style sampling for Lemma 21.44.4:
- primary domain: strictly perfect cochain complexes of module sheaves on ringed sites, and their
  inverse-image functors;
- inspected owner declarations:
  `SheafOfModules.RingedSite.RingedSiteModules`,
  `SheafOfModules.RingedSite.pullbackFunctor`,
  `CochainComplex.IsStrictlyPerfect`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullback_isFiniteFree`;
- best owner abstraction: the public owner layer is
  `RingedSiteModules`, `CochainComplex.IsStrictlyPerfect`, and the chapter owner
  `pullbackFunctor`; the pullback side should be expressed through that owner rather than through
  a parallel local structure-map wrapper;
- primitive data: the site-presented structure morphism of `RingCat`-valued sheaves induced by
  `φ`;
- derived API: the pullback preservation statement for strict perfectness.

Source/core/bridge triage:
- `source-facing`: pullback preserves strictly perfect complexes for the site-presented morphism;
- `core/canonical`: `RingedSiteModules`, `CochainComplex.IsStrictlyPerfect`,
  `ringedSiteUnderlyingStructureMap`, and `pullbackFunctor`;
- `bridge/view`: the induced `RingCat`-valued structure morphism attached to `φ`, used through
  `ringedSiteUnderlyingStructureMap`.
-/
variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify JC AddCommGrpCat]
variable [JC.WEqualsLocallyBijective AddCommGrpCat]
variable [HasWeakSheafify JD AddCommGrpCat]
variable [JD.WEqualsLocallyBijective AddCommGrpCat]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪D : Sheaf JC CommRingCat.{max u v}} {𝒪C : Sheaf JD CommRingCat.{max u v}}
variable (φ : 𝒪D ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} JC JD).obj 𝒪C)
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
variable [(pullbackFunctor F φ).Additive]

-- Proof sketch: unpack `CochainComplex.IsStrictlyPerfect`. The pullback functor on module sheaves
-- is additive, so the induced functor on cochain complexes preserves strict lower and upper
-- bounds. In each degree, Lemma `18.17.2` shows that pullback carries finite free modules to
-- finite free modules, and functoriality sends a retract presentation of `E.X i` to a retract
-- presentation of the pulled-back term.
/-- Lemma 21.44.4: for a site-presented morphism of ringed topoi determined by `φ`, if
`\mathcal F^\bullet` is a strictly perfect complex of `\mathcal O_\mathcal D`-modules, then the
pulled-back complex `f^*\mathcal F^\bullet` is a strictly perfect complex of
`\mathcal O_\mathcal C`-modules. -/
theorem cochainComplex_isStrictlyPerfect_pullback
    (E : CochainComplex (RingedSiteModules JC 𝒪D) ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    CochainComplex.IsStrictlyPerfect
      (((pullbackFunctor F φ).mapHomologicalComplex (up ℤ)).obj E) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_44_5 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "ModLoc" U => ringedSiteModuleCategory (J.over U) (𝒪.over U)

/-- Restriction from `\mathcal O_U`-modules to the iterated localization over `V : Over U`. -/
private abbrev localizedRestrictionToOver
    {U : C} (V : Over U) :
    ModLoc U ⥤ ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V) :=
  SheafOfModules.pushforward (𝟙 (((ringSheaf J 𝒪).over U).over V))

-- Proof sketch: choose a retract of `ℰ` from a finite free `\mathcal O_U`-module. For the
-- finitely many basis sections, use that an epimorphism of sheaves of modules is locally
-- surjective on the slice site `(C/U, J.over U)` to lift their images through `p` after refining
-- by a cover. These local lifts assemble to a lift from the finite free module, and composing with
-- the retraction data yields the desired local lifts from `ℰ`.
/-- Lemma 21.44.5: if `\mathcal E` is a direct summand of a finite free `\mathcal O_U`-module and
`p : \mathcal G \to \mathcal F` is surjective, then every morphism
`f : \mathcal E \to \mathcal F` lifts after passing to a covering of `U`. -/
theorem exists_cover_lift_of_epi_of_retract_finiteFree
    {U : C} {ℰ ℱ 𝒢 : ModLoc U}
    (f : ℰ ⟶ ℱ) (p : 𝒢 ⟶ ℱ) [Epi p]
    (hℰ : ∃ I : Type (max u v), Finite I ∧
      Nonempty (Retract ℰ (SheafOfModules.free I : ModLoc U))) :
    ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
      ∀ i : ι, ∃ l : ℰ.over (cover i) ⟶ 𝒢.over (cover i),
        l ≫ (localizedRestrictionToOver (𝒪 := 𝒪) (cover i)).map p =
          (localizedRestrictionToOver (𝒪 := 𝒪) (cover i)).map f := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_21_44_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {U : C}

local notation "ModU" => LocalizedRingedSiteModules J 𝒪 U
local notation "ModOver" V =>
  LocalizedRingedSiteModules (J := J.over U) (𝒪 := 𝒪.over U) V

/-- Restriction from `\mathcal O_U`-modules to the iterated localization over `V : Over U`. -/
abbrev localizedRestrictionToOver
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    ModU ⥤ ModOver V :=
  SheafOfModules.pushforward
    (𝟙 ((((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U).over V))

/-- Restriction to an iterated localization preserves zero morphisms. -/
local instance localizedRestrictionToOver_preservesZeroMorphisms
    {U : C} (V : Over U) :
    (localizedRestrictionToOver 𝒪 V).PreservesZeroMorphisms where
  map_zero X Y := by
    ext W m
    rfl

/-- Restriction of cochain complexes of `\mathcal O_U`-modules to the iterated localization over
`V : Over U`. -/
abbrev localizedRestrictionComplexToOver
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    CochainComplex ModU ℤ ⥤ CochainComplex (ModOver V) ℤ :=
  (localizedRestrictionToOver 𝒪 V).mapHomologicalComplex (up ℤ)

/-- A morphism of complexes on `(C/U, \mathcal O_U)` is locally null-homotopic if, after passing
to a covering of `U`, each restriction to an iterated localization is homotopic to zero. -/
def IsLocallyNullHomotopic {U : C}
    {E F : CochainComplex ModU ℤ} (α : E ⟶ F) : Prop :=
  ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
    ∀ i : ι,
      Nonempty (Homotopy ((localizedRestrictionComplexToOver 𝒪 (cover i)).map α) 0)

-- Proof sketch: this is the defining expansion of `IsLocallyNullHomotopic`.
/-- Unfolding `IsLocallyNullHomotopic` gives a covering family on which each restricted morphism is
homotopic to zero. -/
theorem isLocallyNullHomotopic_iff {U : C}
    {E F : CochainComplex ModU ℤ} (α : E ⟶ F) :
    IsLocallyNullHomotopic α ↔
      ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
        ∀ i : ι,
          Nonempty (Homotopy ((localizedRestrictionComplexToOver 𝒪 (cover i)).map α) 0) := sorry

-- Proof sketch: apply the bounded-below statement in part `(2)` with the same lower bound as any
-- strict lower bound for `E`; acyclicity of `F` gives vanishing of all homology objects, hence the
-- required local null-homotopies on a covering of `U`.
/-- Lemma 21.44.6 (1): if `\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` is a morphism of
complexes of `\mathcal O_U`-modules with `\mathcal E^\bullet` strictly perfect and
`\mathcal F^\bullet` acyclic, then after a covering of `U` each restriction of `\alpha` is
homotopic to zero. -/
theorem exists_cover_homotopy_zero_of_isStrictlyPerfect_of_acyclic {U : C}
    [CategoryWithHomology ModU] (E F : CochainComplex ModU ℤ) (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E) (hF : F.Acyclic) :
    IsLocallyNullHomotopic α := sorry

-- Proof sketch: argue by induction on the length of the strictly perfect complex `E`. The top
-- nonzero term is a retract of a finite free module, and the vanishing `H^i(F^\bullet)=0` for
-- `i ≥ a` makes the relevant cocycle sheaf a local quotient of the previous term, so Lemma
-- `21.44.5` yields a local null-homotopy on that top summand. Truncating `E` shortens the complex
-- and closes the induction.
/-- Lemma 21.44.6 (2): if `\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` is a morphism of
complexes of `\mathcal O_U`-modules with `\mathcal E^\bullet` strictly perfect,
`\mathcal E^i = 0` for `i < a`, and `H^i(\mathcal F^\bullet) = 0` for `i \ge a`, then after a
covering of `U` each restriction of `\alpha` is homotopic to zero. -/
theorem exists_cover_homotopy_zero_of_isStrictlyPerfect_of_isStrictlyGE_of_homology_isZero
    {U : C} [CategoryWithHomology ModU]
    (E F : CochainComplex ModU ℤ) (α : E ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) :
    IsLocallyNullHomotopic α := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_44_7 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {U : C}

local notation "ModU" => LocalizedRingedSiteModules J 𝒪 U
local notation "ModOver" V =>
  LocalizedRingedSiteModules (J := J.over U) (𝒪 := 𝒪.over U) V

/-- Restriction from `\mathcal O_U`-modules to the iterated localization over `V : Over U`. -/
abbrev localizedRestrictionToOver
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    ModU ⥤ ModOver V :=
  SheafOfModules.pushforward
    (𝟙 ((((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U).over V))

/-- Restriction to an iterated localization preserves zero morphisms. -/
instance localizedRestrictionToOver_preservesZeroMorphisms
    {U : C} (V : Over U) :
    (localizedRestrictionToOver 𝒪 V).PreservesZeroMorphisms := sorry

/-- Restriction of cochain complexes of `\mathcal O_U`-modules to the iterated localization over
`V : Over U`. -/
abbrev localizedRestrictionComplexToOver
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    CochainComplex ModU ℤ ⥤ CochainComplex (ModOver V) ℤ :=
  (localizedRestrictionToOver 𝒪 V).mapHomologicalComplex (ComplexShape.up ℤ)

-- Proof sketch: form the composite `E ⟶ F ⟶ C(f)` with the canonical map to the mapping cone.
-- The hypotheses on `HomologicalComplex.homologyMap f` imply that `C(f)` has vanishing homology
-- in degrees `≥ a`, so Lemma `21.44.6` makes this composite locally null-homotopic after a cover
-- of `U`. Over each member of that cover, a null-homotopy of the composite yields a factorization
-- through the restricted cone, and the mapping-cone triangle then provides the desired local lift
-- of `α` through the restriction of `f` up to homotopy.
/-- Lemma 21.44.7: if `\alpha : \mathcal E^\bullet \to \mathcal F^\bullet` and
`f : \mathcal G^\bullet \to \mathcal F^\bullet` are morphisms of complexes of
`\mathcal O_U`-modules, `\mathcal E^\bullet` is strictly perfect, `\mathcal E^j = 0` for
`j < a`, and `H^j(f)` is an isomorphism for `j > a` and surjective for `j = a`, then after a
covering of `U` each restriction of `\alpha` lifts through the restriction of `f` up to
homotopy. -/
theorem exists_cover_lift_up_to_homotopy_of_isStrictlyPerfect_of_isStrictlyGE_of_homologyMap_isIso_of_epi
    [CategoryWithHomology ModU]
    (E F G : CochainComplex ModU ℤ) (α : E ⟶ F) (f : G ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (hf_iso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_epi : Epi (HomologicalComplex.homologyMap f a)) :
    ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
      ∀ i : ι, ∃ β :
        ((localizedRestrictionComplexToOver 𝒪 (cover i)).obj E) ⟶
          ((localizedRestrictionComplexToOver 𝒪 (cover i)).obj G),
        Nonempty
          (Homotopy
            ((localizedRestrictionComplexToOver 𝒪 (cover i)).map α)
            (β ≫ (localizedRestrictionComplexToOver 𝒪 (cover i)).map f)) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_44_8 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {U : C}

local notation "ModU" => LocalizedRingedSiteModules J 𝒪 U
local notation "ModOver" V =>
  LocalizedRingedSiteModules (J := J.over U) (𝒪 := 𝒪.over U) V

/-- Restriction from `\mathcal O_U`-modules to the iterated localization over `V : Over U`. -/
abbrev localizedRestrictionToOver
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    ModU ⥤ ModOver V :=
  SheafOfModules.pushforward
    (𝟙 ((((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U).over V))

/-- Restriction to an iterated localization preserves zero morphisms. -/
instance localizedRestrictionToOver_preservesZeroMorphisms
    (V : Over U) :
    (localizedRestrictionToOver 𝒪 V).PreservesZeroMorphisms := sorry

/-- Restriction of cochain complexes of `\mathcal O_U`-modules to the iterated localization over
`V : Over U`. -/
abbrev localizedRestrictionComplexToOver
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    CochainComplex ModU ℤ ⥤ CochainComplex (ModOver V) ℤ :=
  (localizedRestrictionToOver 𝒪 V).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The localization functor from complexes of `\mathcal O_U`-modules to the derived category
`D(\mathcal O_U)`. -/
abbrev localizedDerivedCategoryQuotient
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C) :
    CochainComplex ModU ℤ ⥤ DerivedCategory ModU :=
  DerivedCategory.Q

local notation "DModU" => DerivedCategory ModU

variable [Abelian ModU]
variable [∀ V : Over U, Abelian (ModOver V)]

/-- A morphism in `D(\mathcal O_U)` between the objects represented by complexes `E` and `F`. -/
abbrev LocalizedDerivedMorphism
    (E F : CochainComplex ModU ℤ) :=
  (localizedDerivedCategoryQuotient 𝒪 U).obj E ⟶
    (localizedDerivedCategoryQuotient 𝒪 U).obj F

/-- The proposition that a derived morphism from a strictly perfect complex admits a roof whose
restricted numerators are locally represented by chain maps. -/
def HasLocalRoofRepresentative
    (E F : CochainComplex ModU ℤ)
    (α : LocalizedDerivedMorphism E F) : Prop :=
  ∃ G : CochainComplex ModU ℤ, ∃ f : F ⟶ G, ∃ β : E ⟶ G,
    ∃ e :
      (localizedDerivedCategoryQuotient 𝒪 U).obj F ≅
        (localizedDerivedCategoryQuotient 𝒪 U).obj G,
      e.hom = (localizedDerivedCategoryQuotient 𝒪 U).map f ∧
        α = (localizedDerivedCategoryQuotient 𝒪 U).map β ≫ e.inv ∧
      ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
        ∀ i : ι,
          ∃ αi : ((localizedRestrictionComplexToOver 𝒪 (cover i)).obj E) ⟶
              ((localizedRestrictionComplexToOver 𝒪 (cover i)).obj F),
            Nonempty
              (Homotopy
                (αi ≫ (localizedRestrictionComplexToOver 𝒪 (cover i)).map f)
                ((localizedRestrictionComplexToOver 𝒪 (cover i)).map β))

/-- The proposition that a morphism of complexes becomes zero in `D(\mathcal O_U)`. -/
def MapsToZeroInLocalizedDerivedCategory
    (E F : CochainComplex ModU ℤ) (α : E ⟶ F) : Prop :=
  (localizedDerivedCategoryQuotient 𝒪 U).map α = 0

/-- The proposition that a morphism of complexes is locally homotopic to zero after restricting to
a covering of `U`. -/
def HasLocalNullHomotopy
    (E F : CochainComplex ModU ℤ) (α : E ⟶ F) : Prop :=
  ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
    ∀ i : ι,
      Nonempty (Homotopy ((localizedRestrictionComplexToOver 𝒪 (cover i)).map α) 0)

/-- Lemma 21.44.8 (1): a morphism in the localized derived category from a strictly perfect
complex is locally represented by a morphism of complexes after restricting to a cover of `U`. -/
abbrev exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect
    (E F : CochainComplex ModU ℤ)
    (α : LocalizedDerivedMorphism E F) :
    Prop :=
  CochainComplex.IsStrictlyPerfect E →
    HasLocalRoofRepresentative E F α

-- Proof sketch: unfold
-- `exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect`; the abbreviation is exactly the
-- implication from strict perfectness of `E` to the local roof-representative property for `α`.
/-- Applying the main abbreviation to a strictly perfect source complex yields a local roof
representative for the given derived morphism. -/
def exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect_apply
    (E F : CochainComplex ModU ℤ)
    (α : LocalizedDerivedMorphism E F)
    (h : exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect E F α)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    HasLocalRoofRepresentative E F α := sorry

/-- If a morphism of complexes from a strictly perfect complex becomes zero in the localized
derived category, then after restricting to a cover of `U` it is homotopic to zero. -/
abbrev exists_cover_homotopicToZero_of_isStrictlyPerfect_of_Q_map_eq_zero
    (E F : CochainComplex ModU ℤ)
    (α : E ⟶ F) :
    Prop :=
  CochainComplex.IsStrictlyPerfect E →
    MapsToZeroInLocalizedDerivedCategory E F α →
      HasLocalNullHomotopy E F α

end

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {U : C}
variable [Abelian ModU]
variable [∀ V : Over U, Abelian (ModOver V)]

-- Proof sketch: unfold
-- `exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect`; the theorem simply restates the
-- proposition abbreviation as its defining implication.
/-- Unfolding the main abbreviation identifies it with the implication from strict perfectness of
`E` to the existence of a local roof representative for `α`. -/
theorem exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect_iff
    (E F : CochainComplex ModU ℤ)
    (α : LocalizedDerivedMorphism E F) :
    exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect E F α ↔
      CochainComplex.IsStrictlyPerfect E →
        HasLocalRoofRepresentative E F α := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_21_44_9 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u v

set_option checkBinderAnnotations false

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on a ringed
site. -/
abbrev RingedSiteModules
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [HasZeroObject (RingedSiteModules J 𝒪)]
variable [HasProducts (RingedSiteModules J 𝒪)]
variable [HasBinaryBiproducts (RingedSiteModules J 𝒪)]
variable [HasCountableCoproducts (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteModules J 𝒪)]
variable [SymmetricCategory (RingedSiteModules J 𝒪)]
variable [MonoidalClosed (RingedSiteModules J 𝒪)]
variable [(curriedTensor (RingedSiteModules J 𝒪)).PreservesZeroMorphisms]
variable [∀ X : RingedSiteModules J 𝒪,
  ((curriedTensor (RingedSiteModules J 𝒪)).obj X).PreservesZeroMorphisms]
variable [(curriedTensor (RingedSiteModules J 𝒪)).Additive]
variable [∀ X : RingedSiteModules J 𝒪,
  ((curriedTensor (RingedSiteModules J 𝒪)).obj X).Additive]
variable [∀ (K L : CochainComplex (RingedSiteModules J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSiteModules J 𝒪))]
variable [CategoryWithHomology (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules J 𝒪))]
variable [MonoidalClosed (DerivedCategory (RingedSiteModules J 𝒪))]

local instance instPreadditiveRingedSiteModules : Preadditive (RingedSiteModules J 𝒪) :=
  (inferInstance : Abelian (RingedSiteModules J 𝒪)).toPreadditive

local notation "Mod" => RingedSiteModules J 𝒪
local notation "CpxO" => CochainComplex Mod ℤ
local notation "DMod" => DerivedCategory Mod

/-- The degree-`n` term of the internal-Hom complex of two cochain complexes of
`\mathcal O`-modules on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomDegree
    (K L : CpxO) (n : ℤ) : Mod :=
  Limits.piObj (fun p : ℤ ↦ (ihom (K.X p)).obj (L.X (n + p)))

-- Proof sketch: if `j` is the successor of `i` in the cochain-complex shape, then `j = i + 1`,
-- so both index expressions simplify to the same integer.
/-- Reindexing the target degree in the differential of the internal-Hom complex. -/
theorem ringedSiteModuleComplexInternalHom_succIndexEq
    {i j p : ℤ} (hij : (up ℤ).Rel i j) :
    i + (p + 1) = j + p := sorry

/-- The postcomposition contribution to the internal-Hom differential in degree `(i,j,p)`. -/
noncomputable def ringedSiteModuleComplexInternalHomPostcompose
    (K L : CpxO) (i j p : ℤ) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) p ≫
    (ihom (K.X p)).map (L.d (i + p) (j + p))

/-- The precomposition contribution to the internal-Hom differential in degree `(i,j,p)`. -/
noncomputable def ringedSiteModuleComplexInternalHomPrecompose
    (K L : CpxO) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) (p + 1) ≫
    (ihom (K.X (p + 1))).map
      (eqToHom (congrArg (fun q : ℤ ↦ L.X q)
        (ringedSiteModuleComplexInternalHom_succIndexEq hij))) ≫
    (MonoidalClosed.pre (K.d p (p + 1))).app (L.X (j + p))

/-- The degree-`(i,j,p)` component of the internal-Hom differential. -/
noncomputable def ringedSiteModuleComplexInternalHomDComponent
    (K L : CpxO) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  if Even i then
    ringedSiteModuleComplexInternalHomPostcompose K L i j p -
      ringedSiteModuleComplexInternalHomPrecompose K L i j p hij
  else
    ringedSiteModuleComplexInternalHomPostcompose K L i j p +
      ringedSiteModuleComplexInternalHomPrecompose K L i j p hij

/-- The differential on the internal-Hom complex of two cochain complexes of `\mathcal O`-modules
on a ringed site. -/
noncomputable def ringedSiteModuleComplexInternalHomD
    (K L : CpxO) (i j : ℤ) :
    ringedSiteModuleComplexInternalHomDegree K L i ⟶
      ringedSiteModuleComplexInternalHomDegree K L j :=
  if hij : (up ℤ).Rel i j then
    Pi.lift (fun p : ℤ ↦
      ringedSiteModuleComplexInternalHomDComponent K L i j p hij)
  else
    0

-- Proof sketch: by definition, the differential is zero unless `j = i + 1`, i.e. unless the
-- cochain-complex shape relation `ComplexShape.up ℤ` holds between `i` and `j`.
/-- The internal-Hom differential vanishes away from adjacent cohomological degrees. -/
theorem ringedSiteModuleComplexInternalHomShape
    (K L : CpxO) (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomD K L i j = 0 := sorry

-- Proof sketch: expand the two successive internal-Hom differentials, use `d ≫ d = 0` in both
-- source and target complexes, and cancel the mixed terms using the standard cochain sign
-- convention.
/-- Two consecutive differentials in the internal-Hom complex compose to zero. -/
theorem ringedSiteModuleComplexInternalHomDCompD
    (K L : CpxO) (i j k : ℤ)
    (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    ringedSiteModuleComplexInternalHomD K L i j ≫
        ringedSiteModuleComplexInternalHomD K L j k =
      0 := sorry

/-- The internal-Hom complex of two cochain complexes of `\mathcal O`-modules on a ringed
site. -/
noncomputable def ringedSiteModuleComplexInternalHom
    (K L : CpxO) : CpxO where
  X := ringedSiteModuleComplexInternalHomDegree K L
  d := ringedSiteModuleComplexInternalHomD K L
  shape := fun i j hij ↦ ringedSiteModuleComplexInternalHomShape K L i j hij
  d_comp_d' := fun i j k hij hjk ↦
    ringedSiteModuleComplexInternalHomDCompD K L i j k hij hjk

/-- A complex is termwise a retract of a finite free `\mathcal O`-module sheaf if every degree
retracts from a finite free sheaf. -/
def CochainComplex.TermwiseFiniteFreeRetract (E : CpxO) : Prop :=
  ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
    Nonempty (Retract (E.X i) (SheafOfModules.free I : Mod))

-- Proof sketch: this is just the defining predicate, rewritten without the auxiliary name.
/-- Unfolding `TermwiseFiniteFreeRetract` gives the degreewise finite-free retract condition. -/
theorem cochainComplex_termwiseFiniteFreeRetract_iff (E : CpxO) :
    CochainComplex.TermwiseFiniteFreeRetract E ↔
      ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
        Nonempty (Retract (E.X i) (SheafOfModules.free I : Mod)) := sorry

/-- The object of the derived category `D(\mathcal O)` represented by a complex of
`\mathcal O`-modules on the ringed site. -/
noncomputable abbrev ringedSiteDerivedObject
    (K : CpxO) : DMod :=
  DerivedCategory.Q.obj K

-- Proof sketch: unfold the abbreviation `ringedSiteDerivedObject`.
/-- The abbreviation `ringedSiteDerivedObject` applies the localization functor
`C(\mathcal O) \to D(\mathcal O)` to a complex of `\mathcal O`-modules. -/
theorem ringedSiteDerivedObject_def
    (K : CpxO) :
    ringedSiteDerivedObject K = DerivedCategory.Q.obj K := sorry

/-- The proposition that a complex represents the derived internal Hom of two complexes on the
given ringed site. -/
private noncomputable abbrev ringedSiteDerivedInternalHomObject
    (E F : CpxO) : DMod :=
  (ihom (ringedSiteDerivedObject E)).obj (ringedSiteDerivedObject F)

/-- The proposition that a complex represents the derived internal Hom of two complexes on the
given ringed site. -/
noncomputable def ringedSiteDerivedInternalHomRepresentation
    (E F H : CpxO) : Prop :=
  IsIsomorphic
    (ringedSiteDerivedObject H)
    (ringedSiteDerivedInternalHomObject E F)

-- Proof sketch: unfold `ringedSiteDerivedInternalHomRepresentation` and
-- `ringedSiteDerivedObject`.
/-- Unfolding `ringedSiteDerivedInternalHomRepresentation` says exactly that `Q(H)` is
isomorphic to the derived internal-Hom object `R\mathcal H\!\mathit{om}(Q(E), Q(F))`. -/
theorem ringedSiteDerivedInternalHomRepresentation_def
    (E F H : CpxO) :
    ringedSiteDerivedInternalHomRepresentation E F H ↔
      IsIsomorphic
        (ringedSiteDerivedObject H)
        (ringedSiteDerivedInternalHomObject E F) := sorry

/-- The canonical internal-Hom complex, with the ambient ringed-site parameters fixed. -/
private noncomputable def internalHomCpx
    (E F : CpxO) : CpxO :=
  show CpxO from ringedSiteModuleComplexInternalHom E F

-- Proof sketch: this is the definition of `internalHomCpx`.
/-- The internal helper `internalHomCpx` is definitionally the canonical internal-Hom complex
`ringedSiteModuleComplexInternalHom E F`. -/
theorem internalHomCpx_eq
    (E F : CpxO) :
    internalHomCpx E F = ringedSiteModuleComplexInternalHom E F := rfl

/-- The canonical internal-Hom complex on the fixed ringed site represents the derived internal
Hom of `E` and `F`. -/
def internalHomCpxRepresentsDerivedInternalHom
    (E F : CpxO) : Prop :=
  ringedSiteDerivedInternalHomRepresentation E F (internalHomCpx E F)

-- Proof sketch: unfold `internalHomCpxRepresentsDerivedInternalHom`.
/-- Unfolding `internalHomCpxRepresentsDerivedInternalHom` says that the canonical internal-Hom
complex represents the derived internal Hom of `E` and `F`. -/
theorem internalHomCpxRepresentsDerivedInternalHom_def
    (E F : CpxO) :
    internalHomCpxRepresentsDerivedInternalHom E F ↔
      ringedSiteDerivedInternalHomRepresentation E F (internalHomCpx E F) := by
  rfl

-- Proof sketch: choose a K-injective resolution `F ⟶ I`. By Section `21.35`, the complex
-- `ringedSiteModuleComplexInternalHom E I` represents `R\mathcal H\!\mathit{om}(E, F)`. Since
-- `E` is strictly perfect, only finitely many terms contribute in each degree, so the canonical
-- map `ringedSiteModuleComplexInternalHom E F ⟶ ringedSiteModuleComplexInternalHom E I` is a
-- quasi-isomorphism by the local comparison argument of Lemma `21.44.8`.
/-- Lemma 21.44.9: for complexes `\mathcal E^\bullet` and `\mathcal F^\bullet` of
`\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, if
`\mathcal E^\bullet` is strictly perfect, then the derived internal Hom
`R\mathcal H\!\mathit{om}(\mathcal E^\bullet, \mathcal F^\bullet)` is represented by the
canonical internal-Hom complex `ringedSiteModuleComplexInternalHom E F`. Because `E` is strictly
perfect, the degreewise products in this complex are finite and match the textbook formula
`\bigoplus_{n = p + q}\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal E^{-q}, \mathcal F^p)`. -/
def ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_isStrictlyPerfect
    : CpxO → CpxO → Prop :=
  fun E F ↦
    (∃ a : ℤ, E.IsStrictlyGE a) →
      (∃ b : ℤ, E.IsStrictlyLE b) →
        CochainComplex.TermwiseFiniteFreeRetract E →
          internalHomCpxRepresentsDerivedInternalHom (E := E) (F := F)

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_44_10 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

set_option checkBinderAnnotations false

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type} [Category C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat}
variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [HasProducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]
variable [MonoidalClosed (DerivedCategory (ringedSiteModuleCategory J 𝒪))]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex Mod ℤ
local notation "DMod" => DerivedCategory Mod

local instance instPreadditiveMod : Preadditive Mod :=
  (inferInstance : Abelian Mod).toPreadditive

/- Domain-style sampling for Lemma 21.44.10:
- primary domain: derived internal Hom for complexes of `\mathcal O`-modules on a ringed site
  under boundedness and termwise finite-free-retract hypotheses;
- sampled owner declarations:
  `ringedSiteModuleComplexInternalHom`,
  `DerivedCategory.Q.obj`,
  `CochainComplex.IsStrictlyGE`,
  `CochainComplex.IsStrictlyLE`;
- best owner abstraction: the Chapter 21 internal-Hom owner
  `ringedSiteModuleComplexInternalHom`; the bounded-above variant here keeps the degreewise
  retract-of-finite-free hypothesis as primitive source data rather than repackaging it;
- primitive data: the complexes `E`, `F`, the bounded-below hypothesis on `F`, the bounded-above
  hypothesis on `E`, and the pointwise retract-of-finite-free hypothesis on each `E.X i`;
- derived API: the represented derived internal-Hom object in `DerivedCategory Mod`.

Source/core/bridge triage:
- `source-facing`: Lemma 21.44.10, whose bounded-below and bounded-above hypotheses are genuine
  source content;
- `core/canonical`: `ringedSiteModuleComplexInternalHom` and `DerivedCategory.Q.obj`;
- `bridge/view`: the explicit degreewise retract-of-finite-free hypothesis, kept source-facing
  instead of being repackaged through a local strict-perfect wrapper.

This file therefore keeps the source-facing boundedness statement, but reuses the owner property
for the internal-Hom complex instead of introducing a second local representation wrapper. -/

-- Proof sketch: boundedness of `F` from below and boundedness of `E` from above, together with
-- the termwise finite-free retract hypothesis, imply that `E` is locally represented by a bounded
-- complex of finite free modules in the range relevant for the internal-Hom total degree. This is
-- exactly the bounded-above variant of the strict-perfect argument from Lemma `21.44.9`, so the
-- canonical internal-Hom complex still computes the derived internal Hom.
/-- Lemma 21.44.10: for complexes `\mathcal E^\bullet` and `\mathcal F^\bullet` of
`\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, if
`\mathcal F^\bullet` is bounded below, `\mathcal E^\bullet` is bounded above, and each term of
`\mathcal E^\bullet` is a direct summand of a finite free `\mathcal O`-module, then the derived
internal Hom `R\mathcal H\!\mathit{om}(\mathcal E^\bullet, \mathcal F^\bullet)` is represented by
the canonical internal-Hom complex `ringedSiteModuleComplexInternalHom E F`. Under these
hypotheses, the degreewise products in this complex are finite and match the textbook direct-sum
formula `\bigoplus_{n = p + q}\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal E^{-q}, \mathcal F^p)`.
-/
theorem ringedSiteModuleComplexInternalHom_represents_derivedInternalHom_of_boundedBelow_of_boundedAbove_of_termwise_finiteFreeRetract
    (E F : CpxO)
    (hF_boundedBelow : ∃ a : ℤ, F.IsStrictlyGE a)
    (hE_boundedAbove : ∃ b : ℤ, E.IsStrictlyLE b)
    (hE_termwise_finiteFreeRetract :
      ∀ i : ℤ, ∃ I : Type, Finite I ∧
        Nonempty (Retract (E.X i) (SheafOfModules.free I : Mod))) :
    IsIsomorphic
      ((((DerivedCategory.Q : CpxO ⥤ DMod)).obj
        (show CpxO from ringedSiteModuleComplexInternalHom E F)) : DMod)
      ((ihom (((DerivedCategory.Q : CpxO ⥤ DMod)).obj E)).obj
        (((DerivedCategory.Q : CpxO ⥤ DMod)).obj F)) := by
  sorry

end

end SheafOfModules.RingedSite
