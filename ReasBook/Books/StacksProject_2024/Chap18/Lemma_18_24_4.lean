import Mathlib
import StacksProject_2024.Chap12.Definition_12_10_1
import StacksProject_2024.Chap18.Definition_18_23_1
import StacksProject_2024.Chap18.Definition_18_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.24.4:
- primary domain: weak LinearRepresentations_Serre_1977 subcategories of module categories on a ringed site, specialized here
  to the chaotic topology and the quasi-coherent owner predicate;
- sampled owner declarations:
  `ObjectProperty.IsWeakSerreClass`,
  `ringedSiteModuleCategory`,
  `SheafOfModules.isQuasicoherent`,
  `SheafOfModules.RingedSite.IsQuasicoherent`;
- best owner abstraction:
  the chapter owner category `ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪` together
  with the ambient object-property owner
  `SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)`;
- primitive data:
  the chaotic-site ring sheaf `𝒪` and the flatness hypothesis on each restriction map
  `𝒪(V) ⟶ 𝒪(U)`;
- derived API:
  the instance-valued predicate `ℱ.IsQuasicoherent` and the resulting weak-LinearRepresentations_Serre_1977 closure theorem.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that quasi-coherent `\mathcal O`-modules form a weak
  LinearRepresentations_Serre_1977 subcategory under the flatness hypothesis;
- `core/canonical`: `ringedSiteModuleCategory`, `ObjectProperty.IsWeakSerreClass`, and
  `SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)`;
- `bridge/view`: the instance form `ℱ.IsQuasicoherent` attached to that owner predicate.

The theorem below therefore keeps the source-facing weak-LinearRepresentations_Serre_1977 statement, but states it over the
canonical object property `SheafOfModules.isQuasicoherent (ringSheaf (⊥ :
GrothendieckTopology C) 𝒪)` instead of an ad hoc lambda. -/

-- Proof sketch: use the five-term exact-sequence criterion for weak LinearRepresentations_Serre_1977 subcategories. For an
-- exact sequence in `Mod(\mathcal O)`, exactness of sections on the chaotic site and flatness of
-- every restriction map make the tensor-comparison rows exact. Applying the tensor criterion for
-- quasi-coherence and then the five lemma shows the middle term is quasi-coherent whenever the
-- outer four terms are.
/-- Lemma 18.24.4: if every restriction map `\mathcal O(V) \to \mathcal O(U)` on the chaotic site
is flat, then quasi-coherent `\mathcal O`-modules form a weak LinearRepresentations_Serre_1977 subcategory of
`\operatorname{Mod}(\mathcal O)`. -/
theorem quasicoherentModuleProperty_isWeakSerreSubcategory
    (hflat : ∀ ⦃U V : C⦄ (f : U ⟶ V), RingHom.Flat ((𝒪.obj.map f.op).hom)) :
    IsWeakSerreClass (isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) :=
  sorry

/-- Under flat restriction maps on the chaotic site, quasi-coherent `\mathcal O`-modules carry
the canonical weak-LinearRepresentations_Serre_1977 structure. -/
instance isQuasicoherent_isWeakSerreClass
    [Fact (∀ ⦃U V : C⦄ (f : U ⟶ V), RingHom.Flat ((𝒪.obj.map f.op).hom))] :
    IsWeakSerreClass (isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) :=
  quasicoherentModuleProperty_isWeakSerreSubcategory 𝒪 Fact.out

end SheafOfModules
