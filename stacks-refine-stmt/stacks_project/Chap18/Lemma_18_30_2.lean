import Mathlib
import stacks_project.Chap07.Definition_7_17_1
import stacks_project.Chap18.Lemma_18_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable {I : Type v} {U : C} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U)

-- Proof sketch: use quasi-compactness of `U` to refine the given covering family by a covering
-- whose image in the original index set is finite. Let `S ⊆ I` be that finite image. By Sites,
-- Lemma `7.8.6`, the sheaf condition descends from the refining cover to the restricted family
-- indexed by `S`, which gives exactness of the corresponding Čech section sequence. Lemma
-- `18.30.1` identifies this with the exactness of the displayed extension-by-zero sequence.
/-- Lemma 18.30.2: if `U` is quasi-compact and `\{U_i \to U\}_{i \in I}` is a covering family of a
ringed site `(\mathcal C, \mathcal O)`, then there is a finite subset `S ⊆ I` such that the
restricted Čech sequence on sections over `S` is exact for every `\mathcal O`-module. By Lemma
18.30.1, this is equivalent to exactness of the finite direct-sum sequence
`\bigoplus_{i,i' \in S} j_{U_i \times_U U_{i'}!}\mathcal O_{U_i \times_U U_{i'}} \to
\bigoplus_{i \in S} j_{U_i!}\mathcal O_{U_i} \to j_{U!}\mathcal O_U \to 0`. -/
theorem quasiCompactObject_exists_finite_subfamily_section_cech_exact
    (hU : J.QuasiCompactObject U)
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i))) :
    ∃ S : Set I, S.Finite ∧
      ∀ ℱ : ringedSiteModuleCategory J 𝒪,
        let restriction :=
          ringedSiteCoverSectionRestriction J 𝒪
            (fun i : S ↦ Uᵢ i.1) (fun i ↦ π i.1) ℱ
        let compatibility :=
          ringedSiteCoverSectionCompatibility J 𝒪
            (fun i : S ↦ Uᵢ i.1) (fun i ↦ π i.1) ℱ
        Function.Injective restriction ∧ Function.Exact restriction compatibility := sorry

end
