import Mathlib
import stacks_project.Chap12.Definition_12_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomologicalComplex

universe v u

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

/- Source-facing primitive datum for Lemmas 12.14.4–12.14.6: the short complex in degree `n`
obtained by evaluating a short complex of chain complexes. -/
abbrev degreewiseShortComplex (S : ShortComplex (ChainComplex 𝒜 ℤ)) (n : ℤ) :=
  S.map (eval 𝒜 (ComplexShape.down ℤ) n)

noncomputable section

/- Source/core/bridge triage:
- core/canonical owner: `CochainComplex.homOfDegreewiseSplit`
- target item here: a chain-complex bridge/view obtained by transporting that owner construction
  across `cochainComplexEquivalence 𝒜`.
- primitive data: the degreewise split short complex `degreewiseShortComplex S n`.
- derived bridge data: the mapped short complex under `(cochainComplexEquivalence 𝒜).functor`
  and the canonical shift comparison from the pullback-shift owner. -/
/- Internal bridge/view: the chain-level connecting morphism is the preimage, under
`cochainComplexEquivalence 𝒜`, of the owner construction
`CochainComplex.homOfDegreewiseSplit` composed with the canonical shift comparison. -/
/-- Lemma 12.14.4: for a degreewise split short complex of chain complexes, the morphisms
`π_{n-1} ∘ d_{B,n} ∘ s_n` assemble to a chain map `C_• ⟶ A[-1]_•`. -/
def homOfDegreewiseSplit
    (S : ShortComplex (ChainComplex 𝒜 ℤ))
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
    : S.X₃ ⟶ S.X₁⟦(-1 : ℤ)⟧ :=
  let F : ChainComplex 𝒜 ℤ ⥤ PullbackShift (CochainComplex 𝒜 ℤ)
      (negAddMonoidHom : ℤ →+ ℤ) :=
    show ChainComplex 𝒜 ℤ ⥤ PullbackShift (CochainComplex 𝒜 ℤ)
        (negAddMonoidHom : ℤ →+ ℤ) from
      (cochainComplexEquivalence 𝒜).functor
  let T := ((cochainComplexEquivalence 𝒜).functor).mapShortComplex.obj S
  let τ : ∀ m : ℤ, (T.map (eval 𝒜 (up ℤ) m)).Splitting :=
    fun m ↦ show (T.map (eval 𝒜 (up ℤ) m)).Splitting from σ (-m)
  let hEq : (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) =
      (shiftFunctor (PullbackShift (CochainComplex 𝒜 ℤ) (negAddMonoidHom : ℤ →+ ℤ))
        (-1 : ℤ)).obj (F.obj S.X₁) :=
    rfl
  let e :
      (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) ⟶
        (cochainComplexEquivalence 𝒜).functor.obj (S.X₁⟦(-1 : ℤ)⟧) :=
    eqToHom hEq ≫
      ((show shiftFunctor (ChainComplex 𝒜 ℤ) (-1 : ℤ) ⋙ F ≅
          F ⋙
            shiftFunctor (PullbackShift (CochainComplex 𝒜 ℤ)
              (negAddMonoidHom : ℤ →+ ℤ)) (-1 : ℤ)
        from
          F.commShiftIso (-1 : ℤ)).app S.X₁).symm.hom
  ((cochainComplexEquivalence 𝒜).functor).preimage <|
    (show T.X₃ ⟶ (((cochainComplexEquivalence 𝒜).functor.obj S.X₁)⟦(1 : ℤ)⟧) from
      CochainComplex.homOfDegreewiseSplit T τ) ≫ e

-- Proof sketch: transport `CochainComplex.homOfDegreewiseSplit_f` across
-- `ChainComplex.cochainComplexEquivalence`. The auxiliary shift comparison identifies the
-- cochain shift `[1]` with the chain shift `[-1]`.
/-- After identifying `(A⟦-1⟧).X n` with `A.X (n - 1)`, the degree-`n` component of
`homOfDegreewiseSplit` is `π_{n-1} ∘ d_{B,n} ∘ s_n`. -/
@[simp]
theorem homOfDegreewiseSplit_f
    (S : ShortComplex (ChainComplex 𝒜 ℤ))
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
    (n : ℤ) :
    (homOfDegreewiseSplit S σ).f n ≫
        (S.X₁.shiftMinusOneXIso n).hom =
      (σ n).s ≫ S.X₂.d n (n - 1) ≫ (σ (n - 1)).r := by
  sorry

end

end ChainComplex
