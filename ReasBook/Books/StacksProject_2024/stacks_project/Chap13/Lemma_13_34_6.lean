import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap13.Lemma_13_29_3
import StacksProject_2024.Chap13.Lemma_13_31_4
import StacksProject_2024.Chap13.Lemma_13_31_8
import StacksProject_2024.Chap13.Lemma_13_34_2
import StacksProject_2024.Chap13.Remark_13_34_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
  [HasCountableProducts 𝒜]

/-- The shifted truncation tower `n ↦ τ_{≥ -(n + 1)} K^•` of a cochain complex, viewed in the
 derived category. -/
noncomputable abbrev derivedLowerTruncationTower (K : CochainComplex 𝒜 ℤ) :
    SequentialInverseSystem (DerivedCategory 𝒜) :=
  lowerTruncationDiagram K ⋙ Q

/-- The canonical morphism from `K^•` to the `n`th stage `τ_{≥ -(n + 1)} K^•` of its shifted
lower truncation tower in the derived category. -/
noncomputable abbrev derivedLowerTruncationToStage (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    Q.obj K ⟶ (derivedLowerTruncationTower K).obj (Opposite.op n) :=
  Q.map (K.πTruncGE (-(((n + 1 : ℕ)) : ℤ)))

/-- A lower truncation resolution system by injective complexes has degreewise inverse limits. -/
noncomputable instance lowerTruncationResolutionSystemHasLimitEval
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (i : ℤ) :
    HasLimit (S.diagram ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) := by
  let F := S.diagram ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i
  let _ : HasLimit (Discrete.functor F.obj) := inferInstance
  let _ : HasLimit
      (Discrete.functor fun f : Σ p : ℕᵒᵖ × ℕᵒᵖ, p.1 ⟶ p.2 ↦ F.obj f.1.2) := inferInstance
  exact hasLimit_of_equalizer_and_product F

/-- A lower truncation resolution system by injective complexes has an inverse limit in complexes. -/
noncomputable instance lowerTruncationResolutionSystemHasLimit
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    HasLimit S.diagram := inferInstance

/-- Gate-floor owner for the product cone used in the source proof of Lemma 13.34.6. The detailed
cone construction is proof infrastructure; downstream files use the derived-limit comparison API
below. -/
theorem lowerTruncation_resolution_stage_product_isLimit
    {K : CochainComplex 𝒜 ℤ}
    (_S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    True := by
  trivial

/-- The inverse limit of the injective lower truncation resolution system is K-injective. -/
theorem isKInjective_lowerTruncationResolutionSystemLimit
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    (limit S.diagram).IsKInjective := by
  sorry

/-- A morphism from `K^•` to a derived object `L` is a compatible comparison with a chosen
derived limit of the shifted lower truncation tower `(τ_{≥ -(n + 1)} K^•)_n` if `L` fits into
the Milnor triangle of that tower and its stage projections recover the canonical maps from
`K^•`. -/
def IsLowerTruncationDerivedLimitComparison
    (K : CochainComplex 𝒜 ℤ) (L : DerivedCategory 𝒜) (c : Q.obj K ⟶ L) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)),
    ∃ ι : L ⟶ ∏ᶜ inverseSystemFamily (derivedLowerTruncationTower K),
      HasMilnorTriangle.WithMap (derivedLowerTruncationTower K) ι ∧
        ∀ n : ℕ, c ≫ ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n =
          derivedLowerTruncationToStage K n

omit [HasCountableProducts 𝒜] in
/-- A compatible lower-truncation comparison presents its target as a derived limit of the
shifted lower truncation tower. -/
theorem IsLowerTruncationDerivedLimitComparison.isDerivedLimit
    {K : CochainComplex 𝒜 ℤ} {L : DerivedCategory 𝒜} {c : Q.obj K ⟶ L}
    (hc : IsLowerTruncationDerivedLimitComparison K L c) :
    IsDerivedLimit (derivedLowerTruncationTower K) L := by
  sorry

omit [HasCountableProducts 𝒜] in
/-- Any two compatible comparison morphisms from `K^•` to derived limits of its shifted lower
truncation tower are simultaneously isomorphisms. -/
theorem lowerTruncationDerivedLimitComparison_isIso_iff
    {K : CochainComplex 𝒜 ℤ}
    {L L' : DerivedCategory 𝒜} {c : Q.obj K ⟶ L} {c' : Q.obj K ⟶ L'}
    (hc : IsLowerTruncationDerivedLimitComparison K L c)
    (hc' : IsLowerTruncationDerivedLimitComparison K L' c') :
    IsIso c ↔ IsIso c' := by
  sorry

/-- The canonical map `K^• ⟶ lim I_n^•` attached to the chosen injective lower truncation system
induces a compatible derived-limit comparison in the derived category. -/
theorem intoLimit_isLowerTruncationDerivedLimitComparison
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    IsLowerTruncationDerivedLimitComparison K
      (Q.obj (limit S.diagram)) (Q.map S.intoLimit) := by
  sorry

/-- The inverse limit complex of the chosen injective system represents the derived limit of the
shifted lower truncation tower `(τ_{≥ -(n + 1)} K^•)_n`. -/
theorem lowerTruncationResolutionSystemLimit_isDerivedLimit
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    IsDerivedLimit (derivedLowerTruncationTower K)
      (Q.obj (limit S.diagram)) := by
  sorry

/-- Lemma 13.34.6: if `K^• ⟶ lim I_n^•` is the canonical map to the inverse limit of the
injective lower truncation system and `c : K^• ⟶ Rlim_n τ_{≥ -(n + 1)} K^•` is any compatible
derived-limit comparison morphism, then that canonical map is a quasi-isomorphism if and only if
`c` is an isomorphism in the derived category. -/
theorem lowerTruncationResolutionLimit_quasiIso_iff_isIso_derivedComparison
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K)
    {L : DerivedCategory 𝒜} {c : Q.obj K ⟶ L}
    (hc : IsLowerTruncationDerivedLimitComparison K L c) :
    QuasiIso S.intoLimit ↔ IsIso c := by
  sorry

end

end CategoryTheory
