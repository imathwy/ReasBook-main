import stacks_project.Chap06.Lemma_6_33_4

open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe v

section

variable {X : TopCat.{v}}

/-
Domain-style sampling for sheaf gluing on a two-open cover:
- primary domain: sheaf descent along an open cover of a topological space;
- sampled declarations:
  `SheafOpenCoverGlueing`,
  `SheafOpenCoverGlueing.ofSheafFunctor`,
  `sheafRestrictionToOpenCover_isEquivalence`,
  `TopologicalSpace.IsOpenCover.of_sets`;
- owner abstraction: the canonical chapter owner is `SheafOpenCoverGlueing 𝒰`, and the bridge from
  global sheaves to that owner is `SheafOpenCoverGlueing.ofSheafFunctor 𝒰 h𝒰`;
- primitive data: the two opens `U`, `T` and the genuine cover hypothesis `U ⊔ T = ⊤`;
- derived API: the `Bool`-indexed cover attached to `U` and `T`, and the specialization of the
  open-cover equivalence theorem to that cover.

Source/core/bridge triage:
- `source-facing`: the sheaf gluing remark for a cover by two opens;
- `core/canonical`: `SheafOpenCoverGlueing 𝒰`;
- `bridge/view`: the `Bool`-indexed two-open cover used to specialize the canonical equivalence.
-/

/-- The two-member open cover with members `U` and `T`. -/
def twoOpenCover (U T : Opens X) : Bool → Opens X
  | false => U
  | true => T

/-- The family `U, T` is an open cover whenever `U ∪ T = X`. -/
theorem twoOpenCover_isOpenCover {U T : Opens X} (hcover : U ⊔ T = ⊤) :
    IsOpenCover (twoOpenCover U T) := by
  refine IsOpenCover.of_sets (fun b ↦ by
    cases b
    · simpa [twoOpenCover] using U.isOpen
    · simpa [twoOpenCover] using T.isOpen) ?_
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hx : x ∈ (U ⊔ T : Opens X) := by simpa [hcover]
    rcases (show x ∈ U ∨ x ∈ T from by simpa using hx) with hU | hT
    · exact Set.mem_iUnion.2 ⟨false, by simpa [twoOpenCover] using hU⟩
    · exact Set.mem_iUnion.2 ⟨true, by simpa [twoOpenCover] using hT⟩

-- Proof sketch: apply the chapter equivalence theorem for sheaves on an open cover to the
-- `Bool`-indexed family `U, T`.
/-- Remark 15.90.21: if `X = U ∪ T`, then restricting a sheaf on `X` to the two members of the
cover yields the canonical open-cover gluing datum on `U` and `T`, and this restriction functor is
an equivalence. This is the two-open-cover specialization of the chapter's sheaf gluing theorem. -/
theorem sheaf_glueing_along_two_open_cover (U T : Opens X) (hcover : U ⊔ T = ⊤) :
    Functor.IsEquivalence
      (SheafOpenCoverGlueing.ofSheafFunctor
        (twoOpenCover U T) (twoOpenCover_isOpenCover hcover)) := by
  simpa using
    sheafRestrictionToOpenCover_isEquivalence
      (twoOpenCover U T) (twoOpenCover_isOpenCover hcover)

end
