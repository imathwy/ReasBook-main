import Mathlib
import stacks_project.Chap21.«21_30_0_1»
import stacks_project.Chap21.Lemma_21_30_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}

/-- The terminal object of the localized category `Over X`. -/
abbrev terminalOver (X : C) : Over X :=
  Over.mk (𝟙 X)

/-- The direct-image functor of the localized topology-comparison morphism
`ε_X : Sh(C_τ / X) ⥤ Sh(C_{τ'} / X)` for abelian-group-valued sheaves. -/
noncomputable abbrev localizedTopologyComparisonPushforwardAb'
    (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ.over X) AddCommGrpCat ⥤ Sheaf (τ'.over X) AddCommGrpCat :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    id_isContinuous_of_le (comparisonOver_le hle X)
  (𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat (τ'.over X) (τ.over X)

/-- The localized topology-comparison pushforward is additive on abelian sheaves. -/
instance localizedTopologyComparisonPushforwardAb'_additive
    (hle : τ' ≤ τ) (X : C) :
    Functor.Additive (localizedTopologyComparisonPushforwardAb' hle X) := sorry

/-- The objectwise degree-`n` cohomology of a sheaf on a localized site, evaluated at the
terminal object of `Over X`. -/
abbrev terminalOverCohomology {X : C} {J : GrothendieckTopology (Over X)}
    [HasSheafify J AddCommGrpCat]
    [HasExt (Sheaf J AddCommGrpCat)]
    (ℱ : Sheaf J AddCommGrpCat) (n : ℕ) : AddCommGrpCat :=
  ℱ.H' n (terminalOver X)

/-- The `q`-th higher direct image of an abelian sheaf on `(C_τ/X)` along the localized
topology-comparison morphism `ε_X`. -/
abbrev localizedComparisonHigherDirectImage
    (hle : τ' ≤ τ) (X : C)
    [HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat)]
    (ℱ : Sheaf (τ.over X) AddCommGrpCat) (q : ℕ) :
    Sheaf (τ'.over X) AddCommGrpCat :=
  ((localizedTopologyComparisonPushforwardAb' hle X).rightDerived q).obj ℱ

/-- The vanishing hypothesis `(V_n)` at a fixed object `X`: positive-degree objectwise cohomology
of the higher direct images `R^q ε_{X,*} \mathcal F` vanishes on the terminal object of
`Over X` for `1 ≤ q ≤ n`. -/
abbrev localizedComparisonVCondition
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ'.over X) AddCommGrpCat]
    [HasExt (Sheaf (τ'.over X) AddCommGrpCat)]
    [HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat)]
    (ℱ : Sheaf (τ.over X) AddCommGrpCat) (n : ℕ) : Prop :=
  ∀ q p : ℕ, 1 ≤ q → q ≤ n → 0 < p →
    Limits.IsZero
      (terminalOverCohomology (localizedComparisonHigherDirectImage hle X ℱ q) p)

/-- A degree-`n + 1` cohomology class on `(C_τ/X)` becomes trivial on a `τ'`-covering of `X` if
it restricts to zero on each member of some `τ'`-cover of the terminal object of `Over X`. -/
abbrev becomesTrivialOnTauPrimeCovering
    (τPrime : GrothendieckTopology C) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat]
    [HasExt (Sheaf (τ.over X) AddCommGrpCat)]
    (ℱ : Sheaf (τ.over X) AddCommGrpCat) (n : ℕ)
    (ξ : terminalOverCohomology ℱ (n + 1)) : Prop :=
  ∃ T : (τPrime.over X).Cover (terminalOver X), ∀ I : T.Arrow,
    (((ℱ.cohomologyPresheaf (n + 1)).map I.f.op) ξ = 0)

/-- The predicate cutting out the degree-`n + 1` classes on `(C_τ/X)` that are locally trivial on
some `τ'`-covering of `X`. -/
abbrev locallyTrivialOnTauPrimeCovering
    (τPrime : GrothendieckTopology C) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat]
    [HasExt (Sheaf (τ.over X) AddCommGrpCat)]
    (ℱ : Sheaf (τ.over X) AddCommGrpCat) (n : ℕ) :
    terminalOverCohomology ℱ (n + 1) → Prop :=
  fun ξ ↦ becomesTrivialOnTauPrimeCovering τPrime X ℱ n ξ

-- Proof sketch: apply the Leray spectral sequence for the localized topology-comparison morphism
-- `ε_X`. The hypothesis `(V_n)` kills the terms `E₂^{p,q}` with `p > 0` and `1 ≤ q ≤ n`, so the
-- edge morphism in total degree `n + 1` is injective. The following map to
-- `H^0_{τ'}(X, R^{n + 1} ε_{X,*} \mathcal F)` detects precisely the classes whose restrictions
-- vanish on a `τ'`-covering of `X`.
/-- Lemma 21.30.5: assume `τ' ≤ τ` and the vanishing condition `(V_n)` for a sheaf
`\mathcal F` on `(C_\tau / X)`. Then there exists a degree-`n + 1` comparison morphism from the
`τ'`-cohomology of `ε_{X,*}\mathcal F` to the `τ`-cohomology of `\mathcal F`, written here in the
terminal-over-site formulation, whose underlying function is injective and whose image consists
exactly of the classes that become zero on some `τ'`-covering of `X`. -/
theorem exists_objectwiseLocalizedComparison_injective_with_locallyTrivial_image_of_VCondition
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat]
    [HasExt (Sheaf (τ.over X) AddCommGrpCat)]
    [HasSheafify (τ'.over X) AddCommGrpCat]
    [HasExt (Sheaf (τ'.over X) AddCommGrpCat)]
    [HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat)]
    (ℱ : Sheaf (τ.over X) AddCommGrpCat)
    (n : ℕ) (hVn : localizedComparisonVCondition hle X ℱ n) :
    ∃ comparison :
      terminalOverCohomology ((localizedTopologyComparisonPushforwardAb' hle X).obj ℱ) (n + 1) ⟶
        terminalOverCohomology ℱ (n + 1),
      Function.Injective comparison ∧
        ∀ ξ : terminalOverCohomology ℱ (n + 1),
          (∃ η :
            terminalOverCohomology
              ((localizedTopologyComparisonPushforwardAb' hle X).obj ℱ) (n + 1),
              comparison η = ξ) ↔
            locallyTrivialOnTauPrimeCovering τ' X ℱ n ξ := sorry

end CategoryTheory.GrothendieckTopology
