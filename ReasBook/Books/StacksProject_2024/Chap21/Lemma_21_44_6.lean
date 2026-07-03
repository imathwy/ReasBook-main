import Mathlib
import StacksProject_2024.Chap21.Definition_21_44_1

-- Declarations for this item will be appended below by the statement pipeline.

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
