import Mathlib
import stacks_project.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ'.over X) (τ'.over Y))]

-- Proof sketch: this is exactly the coarser-topology sheaf condition supplied by
-- `Situation 21.30.1` for every object of `A'_X`.
/-- In Situation `21.30.1`, each object of `A'_X` may be regarded as a sheaf for the coarser
topology `τ.over X`. -/
theorem comparisonObject_isSheafForCoarser
    (h : cohomology_comparison_situation τ τ' P A')
    {X : C} {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{u}}
    (hℱ : A' X ℱ) :
    CategoryTheory.Presheaf.IsSheaf (τ.over X) ℱ.1 :=
  h.isSheaf_for_coarser_topology hℱ

/-- An object of `A'_X` viewed as a sheaf for the coarser topology `τ.over X`. -/
abbrev comparisonObjectAsCoarserSheaf
    (h : cohomology_comparison_situation τ τ' P A')
    {X : C} (ℱ : Sheaf (τ'.over X) AddCommGrpCat.{u}) (hℱ : A' X ℱ) :
    Sheaf (τ.over X) AddCommGrpCat.{u} :=
  ⟨ℱ.1, comparisonObject_isSheafForCoarser P A' h hℱ⟩

variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]

/-- A degree-`n + 1` cohomology class on an object `U/X` of the localized `τ`-site is locally
zero for `τ'` if it restricts to zero on each member of some `τ'`-covering of `U` over `X`. -/
abbrev localizedComparisonObjectwiseCohomology
    {X : C}
    (ℱ : Sheaf (τ.over X) AddCommGrpCat.{u})
    (U : Over X) (n : ℕ) : AddCommGrpCat.{u} :=
  (ℱ.cohomologyPresheaf (n + 1)).obj (op U)

/-- A degree-`n + 1` cohomology class on an object `U/X` of the localized `τ`-site is locally
zero for `τ'` if it restricts to zero on each member of some `τ'`-covering of `U` over `X`. -/
abbrev localizedComparisonClassLocallyZero
    {X : C}
    (ℱ : Sheaf (τ.over X) AddCommGrpCat.{u})
    (U : Over X) (n : ℕ)
    (ξ : localizedComparisonObjectwiseCohomology ℱ U n) : Prop :=
  ∃ T : (τ'.over X).Cover U, ∀ I : T.Arrow,
    (((ℱ.cohomologyPresheaf (n + 1)).map I.f.op) ξ = 0)

/-- The source-facing comparison condition `(V_n)` says that for every `X`, every sheaf
`\mathcal F ∈ A_X`, every object `U/X`, and every class in `H^{n + 1}_τ(U, \mathcal F)`, the
class becomes zero after passing to a `τ'`-covering of `U`. -/
def localizedComparisonLocalVanishingCondition
    (h : cohomology_comparison_situation τ τ' P A')
    (n : ℕ) : Prop :=
  ∀ (X : C) (ℱ : Sheaf (τ'.over X) AddCommGrpCat.{u}),
    (hℱ : A' X ℱ) →
      ∀ (U : Over X)
        (ξ :
          localizedComparisonObjectwiseCohomology
            (comparisonObjectAsCoarserSheaf P A' h ℱ hℱ) U n),
        @localizedComparisonClassLocallyZero C _ τ τ' _ _ X
          (comparisonObjectAsCoarserSheaf P A' h ℱ hℱ) U n ξ

-- Proof sketch: start with a class `ξ ∈ H^{n + 2}_τ(U, \mathcal F)` for `\mathcal F ∈ A_X` and
-- use locality to reduce to the case of a singleton `τ`-cover in the morphism property `P`.
-- Lemma `21.30.5` identifies the pullback of `ξ` with a unique `τ'`-class, Lemma `21.30.6`
-- kills that class after a `τ'`-covering, and Lemma `21.30.4` plus the truncation triangle and
-- Lemma `21.20.5` show that `ξ` comes from `τ'`-cohomology. Locality of `τ'`-cohomology then
-- yields the desired `τ'`-local vanishing of `ξ`.
/-- Lemma 21.30.7: in Situation 21.30.1, the local comparison vanishing condition `(V_n)`
implies the next-step condition `(V_{n + 1})`. -/
theorem localizedComparisonLocalVanishingCondition_succ
    (h : cohomology_comparison_situation τ τ' P A')
    (n : ℕ)
    (hVn : localizedComparisonLocalVanishingCondition P A' h n) :
    localizedComparisonLocalVanishingCondition P A' h (n + 1) := sorry

end CategoryTheory.GrothendieckTopology
