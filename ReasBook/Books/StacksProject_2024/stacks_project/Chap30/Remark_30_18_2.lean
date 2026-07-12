import StacksProject_2024.Chap30.Lemma_30_18_1
import StacksProject_2024.Chap29.Definition_29_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` recalled the canonical closed-immersion owner `IsClosedImmersion`. Local
precedent fixes `ChowLemmaModification` for Lemma 30.18.1, `Scheme.IsProjectiveBundle` for the
projective-space presentation, and `schemeTheoreticallyDense` for scheme-theoretically dense opens.
The Stacks tag evidence is consistent: item tag `0201` agrees with the source URL ending in
`/tag/0201`.
-/

/-- Remark 30.18.2 (1): in the situation of Chow's lemma, the morphism
`π : X' ⟶ X` has the concrete H-projective presentation obtained by mapping `X'` as a closed
subscheme of `\mathbf P^n_S ×_S X = \mathbf P^n_X`. -/
@[stacks 0201]
theorem ChowLemmaModification.hProjectivePresentationPi
    {X S : Scheme.{u}} {f : X ⟶ S} (M : ChowLemmaModification f) :
    ∃ _ : Scheme.IsProjectiveBundle (pullback.snd M.p f)
        (SheafOfModules.free.{u} (ULift.{u} (Fin (M.n + 1))) : X.Modules),
      IsClosedImmersion (pullback.lift M.i M.π M.commutes) ∧
        pullback.lift M.i M.π M.commutes ≫ pullback.snd M.p f = M.π := sorry

/-- Remark 30.18.2 (2): after replacing the Chow modification by the scheme-theoretic closure of
the inverse image of the distinguished open `U`, one may choose the modification so that this
inverse image is scheme theoretically dense in `X'`. In the current owner, the open `U` is the
field `M.denseOpen`. -/
@[stacks 0201]
theorem exists_chowLemmaModification_schemeTheoreticallyDense_preimage
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [Scheme.Hom.FiniteType f] :
    ∃ M : ChowLemmaModification f,
      schemeTheoreticallyDense (M.π ⁻¹ᵁ M.denseOpen) := sorry

/-- Remark 30.18.2 (3): if `X` is reduced, the Chow modification can be chosen with reduced source
while retaining the scheme-theoretically dense inverse image of the distinguished open. -/
@[stacks 0201]
theorem exists_chowLemmaModification_schemeTheoreticallyDense_preimage_isReduced
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [Scheme.Hom.FiniteType f] [IsReduced X] :
    ∃ M : ChowLemmaModification f,
      schemeTheoreticallyDense (M.π ⁻¹ᵁ M.denseOpen) ∧ IsReduced M.X' := sorry

end AlgebraicGeometry
