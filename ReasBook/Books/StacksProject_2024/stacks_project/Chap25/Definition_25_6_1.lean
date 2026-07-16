import StacksProject_2024.stacks_project.Chap07.Example_7_10_2
import StacksProject_2024.stacks_project.Chap25.Definition_25_2_2
import StacksProject_2024.stacks_project.Chap25.Lemma_25_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open scoped CategoryTheory.SemiRepresentableFamily
open scoped Simplicial
open scoped TerminalPresheaf

noncomputable section

universe w v u

namespace CategoryTheory

-- Semantic search note: `lean_leansearch` points to mathlib's one-hypercover and simplicial
-- coskeleton APIs; the owner choice here follows the local Chapter 25 `SR(C)`/`toPresheaf` API,
-- the generic simplicial-presheaf comparison maps from Lemma 25.4.4, and the Chapter 6/7
-- sheafification-surjectivity precedent.

/- Source/core/bridge triage for Definition 25.6.1 (1):
- `source-facing`: `HypercoveringOf J 𝒢`;
- `core/canonical`: `SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max w v))`, together with the generic
  simplicial-presheaf augmentation maps
  `simplicialPresheafZeroMap`, `simplicialPresheafOneMap`, `simplicialPresheafHigherMap`,
  together with the canonical owner `Presheaf.IsLocallySurjective`;
- `bridge/view`: the hypercovering-specific specializations below, obtained from the simplicial
  presheaf `K ⋙ SemiRepresentableFamily.toPresheaf`.

The source defines a hypercovering of a presheaf, so the public owner stays source-facing. The
comparison-map API, however, is not a new owner: it is a thin specialization of the existing
generic simplicial-presheaf augmentation package from Lemma 25.4.4. -/

variable {C : Type u} [Category.{v} C]

/-- The simplicial presheaf attached to a simplicial semi-representable family. -/
def hypercoveringPresheaf (K : SimplicialObject (SR(C))) :
    SimplicialObject (Cᵒᵖ ⥤ Type (max w v)) :=
  K ⋙ SemiRepresentableFamily.toPresheaf

/-- The degree-`n` presheaf attached to a simplicial semi-representable family. -/
def hypercoveringTerm (K : SimplicialObject (SR(C))) (n : ℕ) :
    Cᵒᵖ ⥤ Type (max w v) :=
  (hypercoveringPresheaf K).obj (op ⦋n⦌)

/-- The degree-`0` augmentation map of a simplicial semi-representable family. -/
abbrev hypercoveringZeroMap
    {𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    (K : SimplicialObject (SR(C)))
    (augmentation :
      K ⋙ SemiRepresentableFamily.toPresheaf ⟶
        (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :
    hypercoveringTerm K 0 ⟶ 𝒢 :=
  simplicialPresheafZeroMap augmentation

/-- The two degree-`1` face maps become equal after composing with the degree-`0` augmentation. -/
theorem hypercoveringOneMap_condition
    {𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    (K : SimplicialObject (SR(C)))
    (augmentation :
      K ⋙ SemiRepresentableFamily.toPresheaf ⟶
        (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :
    SemiRepresentableFamily.toPresheaf.map (K.δ 0) ≫
        hypercoveringZeroMap K augmentation =
      SemiRepresentableFamily.toPresheaf.map (K.δ 1) ≫
        hypercoveringZeroMap K augmentation :=
  by
    simpa [hypercoveringZeroMap] using
      simplicialPresheafOneMap_condition augmentation

/-- The degree-`1` matching map induced by the two face maps and the augmentation. -/
noncomputable def hypercoveringOneMap
    {𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    (K : SimplicialObject (SR(C)))
    (augmentation :
      K ⋙ SemiRepresentableFamily.toPresheaf ⟶
        (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :
    hypercoveringTerm K 1 ⟶
      (pullback
        (hypercoveringZeroMap K augmentation)
        (hypercoveringZeroMap K augmentation) : Cᵒᵖ ⥤ Type (max w v)) :=
  simplicialPresheafOneMap augmentation

/-- The higher matching map into the `(n + 1)`-st level of the `n`-coskeleton. -/
abbrev hypercoveringHigherMap
    (K : SimplicialObject (SR(C))) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    hypercoveringTerm K (n + 1) ⟶
      ((SimplicialObject.cosk n).obj (hypercoveringPresheaf K)).obj (op ⦋n + 1⦌) :=
  simplicialPresheafHigherMap (hypercoveringPresheaf K) n

variable (J : GrothendieckTopology C)

section WithLocalSurjectivity

variable [HasEqualizers C] [HasPullbacks C]
variable [HasWeakSheafify J (Type (max w v))]

/-- The degree-`0` local-surjectivity condition in Definition 25.6.1. -/
def HypercoveringOf.ZeroLocallySurjective
    {𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    (simplicial : SimplicialObject (SR(C)))
    (augmentation :
      simplicial ⋙ SemiRepresentableFamily.toPresheaf ⟶
        (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) : Prop :=
  Presheaf.IsLocallySurjective J (hypercoveringZeroMap simplicial augmentation)

/-- The degree-`1` local-surjectivity condition in Definition 25.6.1. -/
def HypercoveringOf.OneLocallySurjective
    {𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    (simplicial : SimplicialObject (SR(C)))
    (augmentation :
      simplicial ⋙ SemiRepresentableFamily.toPresheaf ⟶
        (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) : Prop :=
  Presheaf.IsLocallySurjective J (hypercoveringOneMap simplicial augmentation)

/-- The higher matching-map local-surjectivity condition in Definition 25.6.1. -/
def HypercoveringOf.HigherLocallySurjective
    (simplicial : SimplicialObject (SR(C))) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] : Prop :=
  Presheaf.IsLocallySurjective J (hypercoveringHigherMap simplicial n)

/-- Definition 25.6.1 (1): a hypercovering of a presheaf `𝒢` is a simplicial object of `SR(C)`
endowed with an augmentation to `𝒢` such that the degree-`0`, degree-`1`, and higher matching
maps become locally surjective after sheafification. -/
@[stacks 09VU]
structure HypercoveringOf
    (𝒢 : Cᵒᵖ ⥤ Type (max w v)) where
  /-- The underlying simplicial object of semi-representable families. -/
  simplicial : SimplicialObject (SR(C))
  /-- The augmentation to the target presheaf `𝒢`. -/
  augmentation :
    simplicial ⋙ SemiRepresentableFamily.toPresheaf ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢
  /-- After sheafification, the degree-`0` augmentation is locally surjective. -/
  zero_locallySurjective : HypercoveringOf.ZeroLocallySurjective J simplicial augmentation
  /-- After sheafification, the degree-`1` matching map is locally surjective. -/
  one_locallySurjective : HypercoveringOf.OneLocallySurjective J simplicial augmentation
  /-- After sheafification, each higher matching map from stage `n + 1` onward is locally
  surjective. -/
  higher_locallySurjective (n : ℕ)
      [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
        (SimplexCategory.Truncated.inclusion (n + 1)).op.HasRightKanExtension F] :
      HypercoveringOf.HigherLocallySurjective J simplicial (n + 1)

end WithLocalSurjectivity

namespace HypercoveringOf

/-- Every simplicial semi-representable family has the canonical augmentation to the terminal
presheaf. -/
def terminalAugmentation (L : SimplicialObject (SR(C))) :
    L ⋙ SemiRepresentableFamily.toPresheaf ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj *ₚ[C] where
  app Δ :=
    { app := fun X _ ↦ PUnit.unit
      naturality := by
        intro X Y f
        rfl }
  naturality := by
    intro Δ Γ f
    ext X x
    rfl

/-- The terminal augmentation sends every section to the unique element of `PUnit`. -/
@[simp] theorem terminalAugmentation_app_apply
    (L : SimplicialObject (SR(C))) (Δ : SimplexCategoryᵒᵖ)
    (X : Cᵒᵖ) (x : ((L ⋙ SemiRepresentableFamily.toPresheaf).obj Δ).obj X) :
    ((terminalAugmentation L).app Δ).app X x = PUnit.unit :=
  rfl

variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

/-- A hypercovering of `𝒢` can be used as its underlying simplicial semi-representable family. -/
instance instCoeToSimplicialObject :
    CoeOut (HypercoveringOf J 𝒢) (SimplicialObject (SR(C))) where
  coe H := H.simplicial

/-- The degree-`0` augmentation map of a hypercovering. -/
def zeroMap (H : HypercoveringOf J 𝒢) :
    hypercoveringTerm H.simplicial 0 ⟶ 𝒢 :=
  hypercoveringZeroMap H.simplicial H.augmentation

/-- The degree-`1` matching map of a hypercovering. -/
def oneMap (H : HypercoveringOf J 𝒢) :
    hypercoveringTerm H.simplicial 1 ⟶
      (pullback H.zeroMap H.zeroMap : Cᵒᵖ ⥤ Type (max w v)) :=
  hypercoveringOneMap H.simplicial H.augmentation

/-- The two degree-`1` face maps of a hypercovering agree after composing with `zeroMap`. -/
theorem oneMap_condition (H : HypercoveringOf J 𝒢) :
    SemiRepresentableFamily.toPresheaf.map (H.simplicial.δ 0) ≫ H.zeroMap =
      SemiRepresentableFamily.toPresheaf.map (H.simplicial.δ 1) ≫ H.zeroMap :=
  hypercoveringOneMap_condition H.simplicial H.augmentation

/-- The higher matching map of a hypercovering. -/
def higherMap (H : HypercoveringOf J 𝒢) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    hypercoveringTerm H.simplicial (n + 1) ⟶
      ((SimplicialObject.cosk n).obj (hypercoveringPresheaf H.simplicial)).obj
        (op ⦋n + 1⦌) :=
  hypercoveringHigherMap H.simplicial n

section

variable [HasWeakSheafify J (Type (max w v))]

omit [HasWeakSheafify J (Type (max w v))] in
/-- The reindexed higher-stage field recovers the original `n ≥ 1` matching-map formulation. -/
theorem higher_locallySurjective_of_one_le (H : HypercoveringOf J 𝒢) (n : ℕ) (hn : 1 ≤ n)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    Presheaf.IsLocallySurjective J (hypercoveringHigherMap H.simplicial n) := by
  cases n with
  | zero =>
      cases Nat.not_succ_le_zero 0 hn
  | succ n =>
      simpa using H.higher_locallySurjective n

end

section

variable [HasWeakSheafify J (Type (max w v))]
variable [HasSheafify J AddCommGrpCat.{max w v}]

omit [HasWeakSheafify J (Type (max w v))] in
/-- Lemma 25.4.4 (1) specialized to a hypercovering of `𝒢`: the positive-degree homology sheaves
of the associated simplicial presheaf vanish. -/
theorem homology_succ_isZero (H : HypercoveringOf J 𝒢) (n : ℕ) :
    IsZero
      (simplicialPresheafHomology J (hypercoveringPresheaf H.simplicial) (n + 1)) :=
  simplicialPresheafHomology_succ_isZero_of_augmentedLocalHypercover J
    H.augmentation
    H.zero_locallySurjective
    H.one_locallySurjective
    H.higher_locallySurjective_of_one_le
    n

omit [HasWeakSheafify J (Type (max w v))] in
/-- Lemma 25.4.4 (2) specialized to a hypercovering of `𝒢`: the degree-`0` homology of the
associated simplicial presheaf identifies with the free abelian sheaf on `𝒢`. -/
theorem homology_zeroToFreeAbelianSheaf_isIso (H : HypercoveringOf J 𝒢) :
    IsIso (simplicialPresheafHomology_zeroToFreeAbelianSheaf J H.augmentation) :=
  simplicialPresheafHomology_zeroToFreeAbelianSheaf_isIso_of_augmentedLocalHypercover J
    H.augmentation
    H.zero_locallySurjective
    H.one_locallySurjective
    H.higher_locallySurjective_of_one_le

end

end HypercoveringOf

/-
Source/core/bridge triage for Definition 25.6.1 (2):
- `source-facing`: a hypercovering of the site;
- `core/canonical`: `HypercoveringOf J (*ₚ[C] : Cᵒᵖ ⥤ Type (max w v))`;
- `bridge/view`: the terminal-presheaf specialization `HypercoveringOf.Terminal`, together with
  `HypercoveringOf.Terminal.ofSimplicial` and the canonical terminal-augmentation lemmas.

The source's site-level notion is exactly the terminal-presheaf specialization, so the public
bridge here stays a thin specialization of `HypercoveringOf` rather than a second packaged
structure or a duplicate root `Hypercovering` owner. -/
/-- Definition 25.6.1 (2): a hypercovering is a hypercovering of the terminal presheaf. -/
@[stacks 09VU]
abbrev HypercoveringOf.Terminal :=
  HypercoveringOf J *ₚ[C]

namespace HypercoveringOf.Terminal

section WithLocalSurjectivity

variable [HasEqualizers C] [HasPullbacks C]
variable [HasWeakSheafify J (Type (max w v))]

/-- The degree-`0` local-surjectivity condition for a hypercovering of the site. -/
def ZeroLocallySurjective
    (simplicial : SimplicialObject (SR(C))) : Prop :=
  HypercoveringOf.ZeroLocallySurjective
    J simplicial (HypercoveringOf.terminalAugmentation simplicial)

/-- The degree-`1` local-surjectivity condition for a hypercovering of the site. -/
def OneLocallySurjective
    (simplicial : SimplicialObject (SR(C))) : Prop :=
  HypercoveringOf.OneLocallySurjective
    J simplicial (HypercoveringOf.terminalAugmentation simplicial)

/-- The higher matching-map local-surjectivity condition for a hypercovering of the site. -/
def HigherLocallySurjective
    (simplicial : SimplicialObject (SR(C))) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] : Prop :=
  HypercoveringOf.HigherLocallySurjective J simplicial n

/-- A site-level hypercovering is determined by its simplicial semi-representable family and the
local-surjectivity conditions, since the augmentation to the terminal presheaf is canonical. -/
abbrev ofSimplicial
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ,
        ∀ [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
          (SimplexCategory.Truncated.inclusion (n + 1)).op.HasRightKanExtension F],
          HigherLocallySurjective J simplicial (n + 1)) :
    HypercoveringOf.Terminal J :=
  { simplicial := simplicial
    augmentation := HypercoveringOf.terminalAugmentation simplicial
    zero_locallySurjective := zero_locallySurjective
    one_locallySurjective := one_locallySurjective
    higher_locallySurjective := higher_locallySurjective }

end WithLocalSurjectivity

/-- `HypercoveringOf.Terminal.ofSimplicial` has the expected underlying simplicial object. -/
@[simp] theorem ofSimplicial_simplicial
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ,
        ∀ [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
          (SimplexCategory.Truncated.inclusion (n + 1)).op.HasRightKanExtension F],
          HigherLocallySurjective J simplicial (n + 1)) :
    (ofSimplicial J simplicial zero_locallySurjective one_locallySurjective
      higher_locallySurjective).simplicial = simplicial :=
  rfl

/-- `HypercoveringOf.Terminal.ofSimplicial` stores the canonical terminal augmentation. -/
@[simp] theorem ofSimplicial_augmentation
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ,
        ∀ [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
          (SimplexCategory.Truncated.inclusion (n + 1)).op.HasRightKanExtension F],
          HigherLocallySurjective J simplicial (n + 1)) :
    (ofSimplicial J simplicial zero_locallySurjective one_locallySurjective
      higher_locallySurjective).augmentation =
        HypercoveringOf.terminalAugmentation simplicial :=
  rfl

/-- `HypercoveringOf.Terminal.ofSimplicial` stores the given degree-`0` local-surjectivity
hypothesis. -/
@[simp] theorem ofSimplicial_zero_locallySurjective
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ,
        ∀ [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
          (SimplexCategory.Truncated.inclusion (n + 1)).op.HasRightKanExtension F],
          HigherLocallySurjective J simplicial (n + 1)) :
    (ofSimplicial J simplicial zero_locallySurjective one_locallySurjective
      higher_locallySurjective).zero_locallySurjective = zero_locallySurjective :=
  rfl

/-- `HypercoveringOf.Terminal.ofSimplicial` stores the given degree-`1` local-surjectivity
hypothesis. -/
@[simp] theorem ofSimplicial_one_locallySurjective
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ,
        ∀ [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
          (SimplexCategory.Truncated.inclusion (n + 1)).op.HasRightKanExtension F],
          HigherLocallySurjective J simplicial (n + 1)) :
    (ofSimplicial J simplicial zero_locallySurjective one_locallySurjective
      higher_locallySurjective).one_locallySurjective = one_locallySurjective :=
  rfl

/-- `HypercoveringOf.Terminal.ofSimplicial` stores the given higher matching-map
local-surjectivity hypotheses. -/
@[simp] theorem ofSimplicial_higher_locallySurjective
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ,
        ∀ [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
          (SimplexCategory.Truncated.inclusion (n + 1)).op.HasRightKanExtension F],
          HigherLocallySurjective J simplicial (n + 1))
    (n : ℕ)
    [∀ F : (SimplexCategory.Truncated (n + 1))ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max w v)),
      (SimplexCategory.Truncated.inclusion (n + 1)).op.HasRightKanExtension F] :
    (ofSimplicial J simplicial zero_locallySurjective one_locallySurjective
      higher_locallySurjective).higher_locallySurjective n =
        higher_locallySurjective n :=
  rfl

end HypercoveringOf.Terminal

end CategoryTheory
