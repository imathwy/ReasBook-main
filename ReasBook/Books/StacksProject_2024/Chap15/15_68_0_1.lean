import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap19.Remark_19_13_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open DerivedCategory
open scoped DerivedExt
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "ModR" => ModuleCat R
local notation "single₀" => singleFunctor ModR (0 : ℤ)

/- Domain-style sampling for `15.68.0.1`.
- primary domain: the derived-`Ext` cohomology spectral sequence for a bounded-below derived
  object of `ModuleCat.{u} R`;
- sampled owner/canonical declarations in the same domain:
  `DerivedExtCohomologySpectralSequenceData`,
  `derivedExtCohomologySpectralSequence_exists`,
  `derivedExtGroup`,
  `Ext^i(X, Y)`,
  `H^j`;
- best owner abstraction: the Chapter `19` owner
  `DerivedExtCohomologySpectralSequenceData ((single₀).obj M) K.obj`, whose primitive fields are
  exactly the `E₂` spectral sequence, its page-two identification, its chosen abutment objects,
  the abutment comparison, and the boundedness consequence under `D⁻/D⁺` hypotheses;
- primitive data for the source-facing statement below: the owner package
  `DerivedExtCohomologySpectralSequenceData ((single₀).obj M) K.obj`;
- derived API: the owner fields `S.pageTwoIso` and `S.abutmentIso`, together with the boundedness
  consequence for `M[0]` and `K ∈ D⁺(R)`;
- source/core/bridge triage:
  `source-facing`: the existence of the `Ext` cohomology spectral sequence for `M` and `K`;
  `core/canonical`: `DerivedExtCohomologySpectralSequenceData`;
  `bridge/view`: the specialized page-two, abutment, and boundedness companions below, written in
    the Chapter `13` `Ext^i` and `H^j` notation rather than the raw `derivedExtGroup` field
    surface.
-/

variable (M : ModR) (K : D⁺(ModR))

/- Lemma 15.68.0.1: for an `R`-module `M` and a bounded-below derived `R`-complex `K ∈ D^+(R)`,
the Chapter `19` `E₂` owner specialized to `M[0]` and `K` is exactly the canonical spectral
sequence package with `E_2^{i,j} = \operatorname{Ext}^i_R(M, H^j(K))` and abutment
`\operatorname{Ext}^{i + j}_R(M, K)`. -/
recall derivedExtCohomologySpectralSequence_exists :
  Nonempty
    (DerivedExtCohomologySpectralSequenceData
      ((single₀).obj M)
      K.obj)

theorem ext_cohomology_spectral_sequence_bounded
    (M : ModR) (K : D⁺(ModR))
    (S : DerivedExtCohomologySpectralSequenceData ((single₀).obj M) K.obj) :
    CohomologicalSpectralSequence.IsBounded S.spectralSequence := by
  have hM : DerivedCategoryIsBoundedAbove ((single₀).obj M) :=
    ⟨0, fun i hi ↦
      isZero_of_isLE ((single₀).obj M) 0 i hi⟩
  have hK : DerivedCategoryIsBoundedBelow K.obj :=
    (derivedCategory_t_plus_iff K.obj).1 K.property
  exact S.bounded_of_boundedness hM hK

end

end CategoryTheory
