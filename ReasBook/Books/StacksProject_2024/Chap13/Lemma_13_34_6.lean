import Mathlib
import stacks_project.Chap13.Definition_13_34_1
import stacks_project.Chap13.Lemma_13_29_3

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

/- 
Domain-style sampling for Lemma `13.34.6`.
- primary domain: sequential inverse systems in the derived category arising from the lower
  truncation tower of a cochain complex, together with the canonical comparison map from the source
  complex into the inverse limit of an injective resolution system;
- sampled owner declarations:
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.isInjective`,
  `LowerTruncationResolutionSystem.intoLimit`,
  `LowerTruncationResolutionSystem.intoLimit_comp_π`,
  `Remark_13_34_5.IsTruncationDerivedLimitComparison` as the nearby comparison-owner pattern for
    truncation towers in the derived category;
- best owner abstraction: the source-facing comparison to the inverse limit of the chosen injective
  system is already owned by `LowerTruncationResolutionSystem.intoLimit`; the inverse-limit object
  itself is canonically `limit S.diagram`, not a separate local wrapper;
- primitive-vs-derived split:
  primitive data: a lower truncation resolution system `S` and the canonical derived-limit
    comparison predicate `IsLowerTruncationDerivedLimitComparison`;
  derived API: K-injectivity of `limit S.diagram`, the derived-limit witness for
    `Q.obj (limit S.diagram)`, and the comparison theorem for the canonical map `S.intoLimit`.

Source/core/bridge triage:
- `source-facing`: the comparison from `K^•` to the inverse limit of the chosen lower truncation
  injective system;
- `core/canonical`: `IsDerivedLimit` and `LowerTruncationResolutionSystem.intoLimit`;
- `bridge/view`: the proof that `Q.map S.intoLimit` is a compatible derived-limit comparison.
-/

/-- The shifted truncation tower `n ↦ τ_{\ge -(n + 1)} K^•` of a cochain complex, viewed in the
derived category. -/
noncomputable abbrev derivedLowerTruncationTower (K : CochainComplex 𝒜 ℤ) :
    SequentialInverseSystem (DerivedCategory 𝒜) :=
  lowerTruncationDiagram K ⋙ Q

/-- The canonical morphism from `K^•` to the `n`th stage `τ_{\ge -(n + 1)} K^•` of its shifted
lower truncation tower in the derived category. -/
noncomputable abbrev derivedLowerTruncationToStage (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    Q.obj K ⟶ (derivedLowerTruncationTower K).obj (Opposite.op n) :=
  Q.map (K.πTruncGE (-(((n + 1 : ℕ)) : ℤ)))

/-- A lower truncation resolution system by injective complexes has an inverse limit in the
category of cochain complexes. -/
private noncomputable instance lowerTruncationResolutionSystem_hasLimit_eval
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) (i : ℤ) :
    HasLimit (S.diagram ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) := by
  let F := S.diagram ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i
  let _ : HasLimit (Discrete.functor F.obj) := inferInstance
  let _ : HasLimit
      (Discrete.functor fun f : Σ p : ℕᵒᵖ × ℕᵒᵖ, p.1 ⟶ p.2 ↦ F.obj f.1.2) := inferInstance
  exact hasLimit_of_equalizer_and_product F

/-- A lower truncation resolution system by injective complexes has an inverse limit in the
category of cochain complexes. -/
private noncomputable instance lowerTruncationResolutionSystem_hasLimit
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    HasLimit S.diagram := inferInstance

-- Proof sketch: identify the inverse limit degreewise with a countable product of injective
-- objects and apply Lemma 13.31.5 to deduce K-injectivity from the K-injectivity of the bounded
-- below stages provided by Lemma 13.31.4.
/-- The inverse limit of the injective lower truncation resolution system is K-injective. -/
theorem isKInjective_lowerTruncationResolutionSystemLimit
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    (limit S.diagram).IsKInjective := sorry

/-- A morphism from `K^•` to a derived object `L` is a compatible comparison with a chosen
derived limit of the shifted lower truncation tower `(τ_{\ge -(n + 1)} K^•)_n` if `L` fits into
the Milnor triangle of that tower and its stage projections recover the canonical maps from
`K^•`. -/
def IsLowerTruncationDerivedLimitComparison
    (K : CochainComplex 𝒜 ℤ) (L : DerivedCategory 𝒜) (c : Q.obj K ⟶ L) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)),
    ∃ ι : L ⟶ ∏ᶜ inverseSystemFamily (derivedLowerTruncationTower K),
      HasMilnorTriangle.WithMap (derivedLowerTruncationTower K) ι ∧
        ∀ n : ℕ, c ≫ ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n =
          derivedLowerTruncationToStage K n

section

omit [HasCountableProducts 𝒜] in
/-- A compatible lower-truncation comparison presents its target as a derived limit of the
shifted lower truncation tower. -/
theorem IsLowerTruncationDerivedLimitComparison.isDerivedLimit
    {K : CochainComplex 𝒜 ℤ} {L : DerivedCategory 𝒜} {c : Q.obj K ⟶ L}
    (hc : IsLowerTruncationDerivedLimitComparison K L c) :
    IsDerivedLimit (derivedLowerTruncationTower K) L := by
  rcases hc with ⟨hP, _, hι, _⟩
  let _ : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)) := hP
  exact ⟨hP, hι.hasMilnorTriangle (derivedLowerTruncationTower K)⟩

end

-- Proof sketch: compare the two compatible maps on each shifted truncation stage and then on
-- each cohomology object, exactly as in Remark 13.34.5; the criterion for being an isomorphism is
-- independent of the chosen compatible derived-limit model.
section

omit [HasCountableProducts 𝒜] in
/-- Any two compatible comparison morphisms from `K^•` to derived limits of its shifted lower
truncation tower are simultaneously isomorphisms. -/
theorem lowerTruncationDerivedLimitComparison_isIso_iff
    {K : CochainComplex 𝒜 ℤ}
    {L L' : DerivedCategory 𝒜} {c : Q.obj K ⟶ L} {c' : Q.obj K ⟶ L'}
    (hc : IsLowerTruncationDerivedLimitComparison K L c)
    (hc' : IsLowerTruncationDerivedLimitComparison K L' c') :
    IsIso c ↔ IsIso c' := sorry

end

-- Proof sketch: `S.intoLimit_comp_π` identifies the canonical map into `lim I_n^•` with the
-- stagewise comparison maps of the lower truncation resolution system, so `Q.map S.intoLimit` is
-- a compatible comparison from `Q.obj K` to the derived-limit model `Q.obj (lim I_n^•)`.
/-- The canonical map `K^• ⟶ lim I_n^•` attached to the chosen injective lower truncation system
induces a compatible derived-limit comparison in the derived category. -/
theorem intoLimit_isLowerTruncationDerivedLimitComparison
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    IsLowerTruncationDerivedLimitComparison K
      (Q.obj (limit S.diagram)) (Q.map S.intoLimit) := sorry

-- Proof sketch: the previous comparison theorem already packages the inverse-limit complex as a
-- compatible Milnor-model for the shifted lower truncation tower, so its target is a derived
-- limit by the owner-bridge above.
/-- The inverse limit complex of the chosen injective system represents the derived limit of the
shifted lower truncation tower `(τ_{\ge -(n + 1)} K^•)_n`. -/
theorem lowerTruncationResolutionSystemLimit_isDerivedLimit
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K) :
    IsDerivedLimit (derivedLowerTruncationTower K)
      (Q.obj (limit S.diagram)) := by
  simpa using
    (intoLimit_isLowerTruncationDerivedLimitComparison S).isDerivedLimit

-- Proof sketch: `Q.map S.intoLimit` is a compatible comparison for the same shifted derived limit
-- as `c`, so `lowerTruncationDerivedLimitComparison_isIso_iff` reduces the claim to
-- `IsIso (Q.map S.intoLimit)`. The latter is equivalent to `S.intoLimit` being a quasi-isomorph-
-- ism by `DerivedCategory.isIso_Q_map_iff_quasiIso`.
/-- Lemma 13.34.6: if `K^• ⟶ \varprojlim I_n^•` is the canonical map to the inverse limit of the
injective lower truncation system and `c : K^• ⟶ R\!\varprojlim_n τ_{\ge -(n + 1)} K^•` is any
compatible derived-limit comparison morphism, then that canonical map is a quasi-isomorphism if
and only if `c` is an isomorphism in the derived category. -/
theorem lowerTruncationResolutionLimit_quasiIso_iff_isIso_derivedComparison
    {K : CochainComplex 𝒜 ℤ}
    (S : LowerTruncationResolutionSystem (isInjective 𝒜) K)
    {L : DerivedCategory 𝒜} {c : Q.obj K ⟶ L}
    (hc : IsLowerTruncationDerivedLimitComparison K L c) :
    QuasiIso S.intoLimit ↔ IsIso c := sorry

end

end CategoryTheory
