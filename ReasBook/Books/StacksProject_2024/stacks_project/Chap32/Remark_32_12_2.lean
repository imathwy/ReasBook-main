import StacksProject_2024.stacks_project.Chap32.Lemma_32_12_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
`IsClosedImmersion` and `IsProper`. Local precedent for Chow's lemma is
`ChowLemmaQcqsModification`, while finite presentation is represented by
`Scheme.Hom.FinitePresentation`. The Stacks tag evidence is consistent: item tag `0GII` agrees
with the source URL ending in `/tag/0GII`. -/

/-- Remark 32.12.2 (1): in the situation of the qcqs version of Chow's lemma, the modification
map `π : X' ⟶ X` is H-projective: it admits a closed immersion over `X` into a standard
projective bundle `\mathbf P^n_X`. -/
@[stacks 0GII]
theorem ChowLemmaQcqsModification.exists_hProjectivePresentation_pi
    {X S : Scheme.{u}} {f : X ⟶ S} (M : ChowLemmaQcqsModification f) :
    ∃ (n : ℕ) (P : Scheme.{u}) (p : P ⟶ X),
      ∃ _ : Scheme.IsProjectiveBundle p
        (SheafOfModules.free.{u} (ULift.{u} (Fin (n + 1))) : X.Modules),
        ∃ i : M.X' ⟶ P, IsClosedImmersion i ∧ i ≫ p = M.π := sorry

/-- Remark 32.12.2 (2): in the qcqs version of Chow's lemma, the modification can be chosen
with reduced source while retaining the other assertions of the lemma. -/
@[stacks 0GII]
theorem exists_chowLemmaQcqsModification_isReduced
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [Scheme.Hom.FiniteType f] :
    ∃ M : ChowLemmaQcqsModification f, IsReduced M.X' := sorry

/-- Remark 32.12.2 (3): in the qcqs version of Chow's lemma, the modification can be chosen
so that `π : X' ⟶ X` is of finite presentation while retaining the other assertions of the
lemma. This is stated separately from the reduced-source variant, as the source notes that the
two refinements cannot generally be imposed simultaneously. -/
@[stacks 0GII]
theorem exists_chowLemmaQcqsModification_finitePresentation_pi
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [Scheme.Hom.FiniteType f] :
    ∃ M : ChowLemmaQcqsModification f, Scheme.Hom.FinitePresentation M.π := sorry

end AlgebraicGeometry
