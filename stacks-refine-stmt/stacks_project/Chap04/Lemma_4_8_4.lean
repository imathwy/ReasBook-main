import Mathlib.Data.List.TFAE
import stacks_project.Chap04.Definition_4_8_2

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Opposite Limits Functor.relativelyRepresentable
open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] [HasPullbacks C]

/-
Source/core/bridge triage for Lemma 4.8.4:
- domain-style sampling in the presheaf representability layer:
  `Functor.relativelyRepresentable.diag_iff`,
  `yoneda.relativelyRepresentable`,
  `Limits.pullback`,
  `relativelyRepresentable_iff_isRepresentable_pullback_yoneda`,
  `yoneda.obj`;
- source-facing owner: `presheaf_diagonal_representability_tfae`;
- core/canonical owner: `Functor.relativelyRepresentable.diag_iff`;
- bridge/view API: specialize the owner-level diagonal criterion to Yoneda sections
  `ξ : h[U] ⟶ F`, then translate relative representability of each section to representability of
  the associated pullback by Definition 4.8.2.
- primitive data: only the presheaf `F`;
- derived API: relative representability of `diag F`, relative representability of each Yoneda
  section, and representability of the associated Yoneda pullbacks.
-/

/-- Lemma 4.8.4: for a presheaf `F` on a category with binary products and pullbacks, the
relative representability of the diagonal `Δ : F ⟶ F × F`, the relative representability of every
section `h_U ⟶ F`, and the representability of every fibre product `h_U ×[F] h_V` cut out by two
sections are equivalent. -/
theorem presheaf_diagonal_representability_tfae (F : Presheaf.{v} C) :
    [yoneda.relativelyRepresentable (diag F),
      ∀ (U : C) (ξ : h[U] ⟶ F), yoneda.relativelyRepresentable ξ,
      ∀ (U V : C) (ξ : h[U] ⟶ F) (ξ' : h[V] ⟶ F), (pullback ξ ξ').IsRepresentable].TFAE := by
  tfae_have 1 ↔ 2 := by
    have hdiag :
        yoneda.relativelyRepresentable (diag F) ↔
          ∀ ⦃U : C⦄ (ξ : yoneda.obj U ⟶ F), yoneda.relativelyRepresentable ξ := diag_iff
    simpa using hdiag
  tfae_have 2 ↔ 3 := by
    constructor
    · intro h U V ξ ξ'
      exact
        (relativelyRepresentable_iff_isRepresentable_pullback_yoneda ξ).1 (h U ξ) V ξ'
    · intro h U ξ
      exact
        (relativelyRepresentable_iff_isRepresentable_pullback_yoneda ξ).2
        (fun V ξ' ↦ h U V ξ ξ')
  tfae_finish

end CategoryTheory
