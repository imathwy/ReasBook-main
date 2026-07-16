import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_138_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [Algebra.Smooth A C]

/- Domain triage:
- primary domain: the conormal exact sequence for a surjective map `B → C`, specialized from
  formal smoothness to smoothness of `A → C`;
- sampled owner declarations:
  - `KaehlerDifferential.mapBaseChange`,
  - `KaehlerDifferential.mapBaseChange_surjective`,
  - `kaehlerDifferential_mapBaseChange_has_section_of_formallySmooth`,
  - `Algebra.Smooth.formallySmooth`;
- best owner abstraction: the canonical `C`-linear map
  `KaehlerDifferential.mapBaseChange A B C`, with split exactness recorded by existence of a
  section;
- primitive data: the tower `A → B → C`, the surjectivity of `B → C`, and the smoothness of
  `A → C`;
- derived API: the actual splitting map `Ω[C⁄A] →ₗ[C] C ⊗[B] Ω[B⁄A]`;
- layer triage:
  - `source-facing`: Lemma `10.139.2`, the smooth case of the split conormal sequence;
  - `core/canonical`: `KaehlerDifferential.mapBaseChange A B C`;
  - `bridge/view`: Lemma `10.138.10`, which supplies the same section under the weaker
    `Algebra.FormallySmooth A C` hypothesis.

This file should therefore stay a thin smooth specialization of Lemma `10.138.10`, rather than
introducing any parallel wrapper around the owner map.
-/

-- Proof sketch: smoothness implies formal smoothness by `Algebra.Smooth.formallySmooth`, so this
-- reduces to the split exactness statement of Lemma `10.138.10`. Equivalently, the surjection
-- `KaehlerDifferential.mapBaseChange A B C` from the conormal sequence admits a `C`-linear
-- section.
/-- Lemma 10.139.2: if `A → C` is smooth and `B → C` is surjective with kernel `J`, then the exact
sequence
`0 → J/J² → Ω[B⁄A] ⊗[B] C → Ω[C⁄A] → 0`
of Lemma `10.131.9` is split exact. In canonical library form, the surjection
`KaehlerDifferential.mapBaseChange A B C : C ⊗[B] Ω[B⁄A] →ₗ[C] Ω[C⁄A]`
admits a `C`-linear section. -/
@[stacks 06A8]
theorem kaehlerDifferential_mapBaseChange_has_section_of_smooth
    (hsurj : Function.Surjective (algebraMap B C)) :
    ∃ σ : Ω[C⁄A] →ₗ[C] C ⊗[B] Ω[B⁄A],
      (KaehlerDifferential.mapBaseChange A B C).comp σ = LinearMap.id :=
  kaehlerDifferential_mapBaseChange_has_section_of_formallySmooth hsurj

end
