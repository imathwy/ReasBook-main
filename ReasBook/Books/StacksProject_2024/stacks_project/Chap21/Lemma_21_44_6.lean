import StacksProject_2024.stacks_project.Chap21.Definition_21_44_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

/-
Domain-style sampling for Lemma 21.44.6:
- primary domain: local null-homotopies of morphisms from strictly perfect cochain complexes on a
  localized ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `ringSheaf`,
  `ringedSiteLocalizedRestriction`,
  `Functor.mapHomologicalComplex`,
  `CochainComplex.IsStrictlyPerfect`,
  `Homotopy`;
- best owner abstraction: the canonical iterated localized restriction owner
  `ringedSiteLocalizedRestriction (J := J.over U) (𝒪 := 𝒪.over U) V`, together with its induced
  functor on cochain complexes;
- primitive data: the morphism `α : E ⟶ F` and a covering family `cover : ι → Over U`;
- derived API: the source-facing predicate `IsLocallyNullHomotopic` and the two vanishing lemmas
  below.

Source/core/bridge triage:
- `source-facing`: `IsLocallyNullHomotopic`;
- `core/canonical`: `ringedSiteModuleCategory`, `ringSheaf`, `SheafOfModules.pushforward`, and
  `Functor.mapHomologicalComplex`;
- `bridge/view`: none.

This file should therefore own the local-null-homotopy predicate, while direct downstream files
reuse the canonical iterated localized restriction owner on the localized ringed site instead of a
parallel local complex wrapper. -/
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "ModLoc" U => ringedSiteModuleCategory (J.over U) (𝒪.over U)

variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {U : C}

local notation "res[" V "]" =>
  ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V

/-- A morphism of complexes on `(C/U, 𝒪_U)` is locally null-homotopic if, after passing
to a covering of `U`, each restriction to an iterated localization is homotopic to zero. -/
def IsLocallyNullHomotopic {E F : CochainComplex (ModLoc U) ℤ} (α : E ⟶ F) : Prop :=
  ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
    ∀ i : ι, Nonempty (Homotopy (((res[cover i]).mapHomologicalComplex (up ℤ)).map α) 0)

omit [HasBinaryProducts C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})] in
/-- Unfolding `IsLocallyNullHomotopic` gives the explicit cover-wise null-homotopy criterion. -/
theorem isLocallyNullHomotopic_iff
    {E F : CochainComplex (ModLoc U) ℤ} (α : E ⟶ F) :
    IsLocallyNullHomotopic α ↔
      ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
        ∀ i : ι,
          Nonempty (Homotopy (((res[cover i]).mapHomologicalComplex (up ℤ)).map α) 0) :=
  Iff.rfl

variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

-- Proof sketch: apply the bounded-below statement in part `(2)` with the same lower bound as any
-- strict lower bound for `E`; acyclicity of `F` gives vanishing of all homology objects, hence the
-- required local null-homotopies on a covering of `U`.
--
-- As in the nearby Chapter 21 owners `Lemma_21_44_2` and `Lemma_21_44_4`, the site hypotheses
-- `[HasWeakSheafify J AddCommGrpCat]` and `[J.WEqualsLocallyBijective AddCommGrpCat]` are
-- internal proof infrastructure here. The source-facing statement only concerns the local
-- null-homotopy criterion on `(C/U, 𝒪_U)`, so those classes are omitted from the public
-- theorem surface.
omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Lemma 21.44.6 (1): if `α : 𝓔^• ⟶ 𝓕^•` is a morphism of complexes of `𝒪_U`-modules with `𝓔^•`
strictly perfect and `𝓕^•` acyclic, then after a covering of `U` each restriction of `α` is
homotopic to zero. -/
@[stacks 08FP]
theorem exists_cover_homotopy_zero_of_isStrictlyPerfect_of_acyclic {U : C}
    [CategoryWithHomology (ModLoc U)]
    (E F : CochainComplex (ModLoc U) ℤ) (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E) (hF : F.Acyclic) :
    IsLocallyNullHomotopic α := sorry

-- Proof sketch: argue by induction on the length of the strictly perfect complex `E`. The top
-- nonzero term is a retract of a finite free module, and the vanishing `H^i(𝓕^•) = 0` for
-- `i ≥ a` makes the relevant cocycle sheaf a local quotient of the previous term, so Lemma
-- `21.44.5` yields a local null-homotopy on that top summand. Truncating `E` shortens the complex
-- and closes the induction.
omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Lemma 21.44.6 (2): if `α : 𝓔^• ⟶ 𝓕^•` is a morphism of complexes of `𝒪_U`-modules with `𝓔^•`
strictly perfect, `𝓔^i = 0` for `i < a`, and `H^i(𝓕^•) = 0` for `i ≥ a`, then after a covering of
`U` each restriction of `α` is homotopic to zero. -/
@[stacks 08FP]
theorem exists_cover_homotopy_zero_of_isStrictlyPerfect_of_isStrictlyGE_of_homology_isZero
    {U : C} [CategoryWithHomology (ModLoc U)]
    (E F : CochainComplex (ModLoc U) ℤ) (α : E ⟶ F) (a : ℤ)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (hE_ge : E.IsStrictlyGE a)
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) :
    IsLocallyNullHomotopic α := sorry

end

end SheafOfModules.RingedSite
