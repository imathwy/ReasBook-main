import StacksProject_2024.Chap21.Definition_21_17_2
import StacksProject_2024.Chap22.Definition_22_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace SheafOfModules.RingedSite

section

-- Semantic search note: `lean_leansearch` was unavailable in this runner; the statement shape was
-- checked against the local Chapter 22 admissible-short-exact owner and the Chapter 24 `IsGood`
-- owner from the neighboring file `Lemma_24_23_3`.

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor Mod).Additive]
variable [∀ M : Mod, ((curriedTensor Mod).obj M).Additive]

namespace CochainComplex

/-- A good differential graded module on a ringed site, formalized on the canonical
cochain-complex owner, is termwise flat, K-flat, and remains termwise flat and K-flat after every
site-presented pullback. Since the pullback-stability clause is already a theorem-level
consequence of termwise flatness and K-flatness in the surrounding Chapter 21 API, the public
owner keeps only that nonredundant core data on the underlying cochain complex. -/
@[mk_iff isGood_iff]
class IsGood (K : Cpx) : Prop where
  /-- The underlying graded module is termwise flat. -/
  termwiseFlat : IsTermwiseFlat K
  /-- The underlying cochain complex is K-flat. -/
  kFlat : K.IsKFlat

/-- Constructor for the nonredundant fieldwise form of `IsGood`. -/
theorem IsGood.of_termwiseFlat_kFlat
    {K : Cpx}
    (termwiseFlat : IsTermwiseFlat K)
    (kFlat : K.IsKFlat) :
    IsGood K :=
  ⟨termwiseFlat, kFlat⟩

/-- A good complex is termwise flat and K-flat. -/
theorem IsGood.termwiseFlat_kFlat {K : Cpx} (hK : IsGood K) :
    IsTermwiseFlat K ∧ K.IsKFlat :=
  ⟨hK.termwiseFlat, hK.kFlat⟩

/-- An admissible short exact sequence of cochain complexes on a ringed site is a short exact
sequence that splits degreewise after forgetting the differential. This is the source-facing
specialization of the Chapter 22 admissibility owner to cochain complexes of `\mathcal O`-modules
on the ambient ringed site. -/
abbrev IsAdmissibleShortExact (S : ShortComplex Cpx) : Prop :=
  _root_.IsAdmissibleShortExact (HomologicalComplex.forget Mod (ComplexShape.up ℤ)) S

/-- The source-facing cochain-complex admissibility condition is equivalent to the canonical
split-monomorphism and split-epimorphism conditions on the underlying graded maps after forgetting
the differential. -/
theorem isAdmissibleShortExact_iff
    (S : ShortComplex Cpx) :
    IsAdmissibleShortExact S ↔
      S.ShortExact ∧
        IsSplitMono ((HomologicalComplex.forget Mod (ComplexShape.up ℤ)).map S.f) ∧
        IsSplitEpi ((HomologicalComplex.forget Mod (ComplexShape.up ℤ)).map S.g) := by
  rfl

/-- Lemma 24.23.2 (1): for an admissible short exact sequence
`0 ⟶ \mathcal P ⟶ \mathcal P' ⟶ \mathcal P'' ⟶ 0` of differential graded modules on a ringed
site, formalized on the underlying cochain-complex short exact sequence with admissibility meaning
a degreewise splitting after forgetting the differential, if `\mathcal P` and `\mathcal P'` are
good, then `\mathcal P''` is good. -/
@[stacks 0FSC]
theorem isGood_X₃_of_isAdmissibleShortExact
    (S : ShortComplex Cpx)
    (hS : S.ShortExact)
    (hAdm : IsAdmissibleShortExact S)
    (h₁ : IsGood S.X₁)
    (h₂ : IsGood S.X₂) :
    IsGood S.X₃ := by
  sorry


/-- Lemma 24.23.2 (2): for an admissible short exact sequence
`0 ⟶ \mathcal P ⟶ \mathcal P' ⟶ \mathcal P'' ⟶ 0` of differential graded modules on a ringed
site, formalized on the underlying cochain-complex short exact sequence with admissibility meaning
a degreewise splitting after forgetting the differential, if `\mathcal P` and `\mathcal P''` are
good, then `\mathcal P'` is good. -/
@[stacks 0FSC]
theorem isGood_X₂_of_isAdmissibleShortExact
    (S : ShortComplex Cpx)
    (hS : S.ShortExact)
    (hAdm : IsAdmissibleShortExact S)
    (h₁ : IsGood S.X₁)
    (h₃ : IsGood S.X₃) :
    IsGood S.X₂ := by
  sorry


/-- Lemma 24.23.2 (3): for an admissible short exact sequence
`0 ⟶ \mathcal P ⟶ \mathcal P' ⟶ \mathcal P'' ⟶ 0` of differential graded modules on a ringed
site, formalized on the underlying cochain-complex short exact sequence with admissibility meaning
a degreewise splitting after forgetting the differential, if `\mathcal P'` and `\mathcal P''` are
good, then `\mathcal P` is good. -/
@[stacks 0FSC]
theorem isGood_X₁_of_isAdmissibleShortExact
    (S : ShortComplex Cpx)
    (hS : S.ShortExact)
    (hAdm : IsAdmissibleShortExact S)
    (h₂ : IsGood S.X₂)
    (h₃ : IsGood S.X₃) :
    IsGood S.X₁ := by
  sorry


end CochainComplex

end

end SheafOfModules.RingedSite
