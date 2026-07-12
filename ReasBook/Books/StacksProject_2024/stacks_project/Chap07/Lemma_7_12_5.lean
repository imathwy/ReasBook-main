import Mathlib
import StacksProject_2024.Chap07.Definition_7_40_2
import StacksProject_2024.Chap25.Definition_25_2_1
import StacksProject_2024.Chap07.Lemma_7_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

open scoped SheafifiedRepresentable

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 7.12.5:
- primary domain: sheafified representables, locally surjective cover maps, and coequalizers in
  the sheaf topos `Sh(C, J)`;
- sampled owner declarations:
  `GrothendieckTopology.sheafifiedRepresentable`,
  `GrothendieckTopology.sheafifiedRepresentableCoverMap_isLocallySurjective`,
  `CategoryTheory.Limits.Cofork.ofπ`,
  `CategoryTheory.Sheaf.isColimitCoforkOfIsLocallySurjective`,
  `GrothendieckTopology.HasEnoughObjectsWithProperty`;
- best owner abstraction: this source-facing existence theorem should expose the actual coequalizer
  diagram `ℱ₁ ⇉ ℱ₀ ⟶ ℱ` and use the canonical owner
  `IsColimit (Cofork.ofπ π hπ)` for its universal property;
- primitive data: covers by objects of `E`, the resulting semi-representable families, the induced
  parallel pair between their coproducts, and the comparison map `ℱ₀ ⟶ ℱ`;
- derived API: existence of the `IsColimit` witness for the resulting canonical cofork.

Source/core/bridge triage:
- `source-facing`: the existence of a coequalizer presentation of a sheaf by coproducts of
  sheafified representables attached to objects of `E`;
- `core/canonical`: `Cofork.ofπ`, `IsColimit`, `J.sheafifiedRepresentable`, and
  `Sheaf.isColimitCoforkOfIsLocallySurjective`;
- `bridge/view`: the chosen semi-representable families and the induced parallel pair between their
  coproducts.

This item should stay `source-facing`: it chooses coproducts of sheafified representables from
`E`, but the coequalizer clause itself should use the canonical cofork owner rather than a broader
parallel-pair colimit wrapper.
-/

-- Proof sketch: choose a coproduct of sheafified representables from `E` mapping epimorphically
-- to `ℱ`, apply the same construction to the kernel pair of that map, and use Lemma 7.11.3 to
-- identify the resulting cofork as a coequalizer. Since `IsColimit` is a structure, the
-- existence theorem records its universal-property witness through `Nonempty`.
/-- Lemma 7.12.5: if every object is covered by objects of `E`, then every sheaf of sets admits a
coequalizer presentation by a parallel pair between coproducts of sheafified representables whose
indexing objects lie in `E`. -/
theorem exists_coequalizer_presentation_by_sheafified_representables
    {E : Set C}
    (hE : J.HasEnoughObjectsWithProperty E)
    (ℱ : Sheaf J (Type (max u v))) :
    ∃ 𝒰₀ : {𝒰 : SemiRepresentableFamily.{max u v, v, u} C // ∀ i : 𝒰.index, 𝒰.obj i ∈ E},
      ∃ 𝒰₁ : {𝒰 : SemiRepresentableFamily.{max u v, v, u} C // ∀ i : 𝒰.index, 𝒰.obj i ∈ E},
        let _ : HasColimitsOfShape (Discrete 𝒰₁.1.index) (Sheaf J (Type (max u v))) :=
          Sheaf.instHasColimitsOfShape
        let _ : HasColimitsOfShape (Discrete 𝒰₀.1.index) (Sheaf J (Type (max u v))) :=
          Sheaf.instHasColimitsOfShape
        ∃ (p q :
            (∐ fun i : 𝒰₁.1.index ↦ h[𝒰₁.1.obj i]^#[J]) ⟶
              (∐ fun i : 𝒰₀.1.index ↦ h[𝒰₀.1.obj i]^#[J]))
          (π :
            (∐ fun i : 𝒰₀.1.index ↦ h[𝒰₀.1.obj i]^#[J]) ⟶ ℱ)
          (hπ : p ≫ π = q ≫ π),
          Nonempty (IsColimit (Cofork.ofπ π hπ)) := sorry

end CategoryTheory.GrothendieckTopology

end
