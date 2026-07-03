import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_21_32_1 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u w

attribute [local instance] HasDerivedCategory.standard

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)

variable [Abelian Mod]
variable [CategoryWithHomology Mod]
variable [IsGrothendieckAbelian.{w} Mod]

/- Domain-style sampling for Example 21.32.1:
- primary domain: derived `Ext` spectral sequences in a Grothendieck abelian category, specialized
  to the ringed-site module category `ringedSiteModuleCategory J 𝒪`;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `DerivedExtCohomologySpectralSequenceData`,
  `DerivedExtStupidFiltrationSpectralSequenceData`,
  `derivedExt_cohomology_spectralSequence_exists`,
  `derivedExt_stupidFiltration_spectralSequence_exists`;
- best owner abstraction: the Chapter 19 owners
  `DerivedExtCohomologySpectralSequenceData` and
  `DerivedExtStupidFiltrationSpectralSequenceData`, with this file giving the source-facing
  specialization to `DMod = DerivedCategory Mod`;
- primitive vs derived: the primitive data here are the bounded-above complex `K`,
  the module `ℱ`, and the canonical derived objects `DerivedCategory.Q.obj K` and
  `(single0).obj ℱ`; the convergence witness is derived API supplied by the owner package under
  the boundedness hypotheses.

Source/core/bridge triage:
- `source-facing`: the two ringed-site existence statements matching Example 21.32.1;
- `core/canonical`: the Chapter 19 spectral-sequence owner structures and their existence theorems;
- `bridge/view`: the degree-zero bounded-below lemma and the bounded-above witness extracted from
  `hK`, which feed the source-facing convergence statements into the owner-level
  `converges_of_boundedness` fields.

No extra wrapper owner is introduced here: the file reuses the Chapter 19 owners directly and
records only the ringed-site specialization demanded by the source. -/

private theorem ringedSiteModule_single_isGE_zero (ℱ : Mod) :
    ((single0).obj ℱ).IsGE 0 := by
  infer_instance

-- Proof sketch: specialize Remark `19.13.11` to the derived object `Q.obj K^\bullet` and to the
-- degree-zero derived object attached to `\mathcal F`. The bounded-above hypothesis on
-- `K^\bullet` and the degree-zero concentration of `\mathcal F` supply the convergence witness.
/-- Example 21.32.1 (1): for a ringed site `(\mathcal C, \mathcal O)`, a bounded-above complex
`K^\bullet` of `\mathcal O`-modules, and an `\mathcal O`-module `\mathcal F`, there is a spectral
sequence with `E_2^{i,j} = \operatorname{Ext}^i_{\mathcal O}(H^{-j}(K^\bullet), \mathcal F)`
abutting to `\operatorname{Ext}^{i + j}_{\mathcal O}(K^\bullet, \mathcal F)`. -/
theorem ringedSiteExt_cohomology_spectralSequence_exists
    (K : CochainComplex Mod ℤ) (ℱ : Mod) (hK : cochainComplexIsBoundedAbove K) :
    ∃ S : DerivedExtCohomologySpectralSequenceData
      (DerivedCategory.Q.obj K) ((single0).obj ℱ),
      filteredComplexAssociatedSpectralSequenceConverges
        S.filteredComplex S.spectralSequence := by
  obtain ⟨S⟩ := derivedExt_cohomology_spectralSequence_exists
    (DerivedCategory.Q.obj K) ((single0).obj ℱ)
  rcases hK with ⟨n, hn⟩
  let _ : K.IsStrictlyLE n := hn
  refine ⟨S, ?_⟩
  exact S.converges_of_boundedness
    ⟨n, inferInstance⟩
    ⟨0, ringedSiteModule_single_isGE_zero J 𝒪 ℱ⟩

-- Proof sketch: specialize the stupid-filtration spectral sequence of Remark `19.13.11` to the
-- same degree-zero derived object attached to `\mathcal F`. The bounded-above hypothesis on
-- `K^\bullet` is exactly the convergence input required by the generic statement.
/-- Example 21.32.1 (2): for a ringed site `(\mathcal C, \mathcal O)`, a bounded-above complex
`K^\bullet` of `\mathcal O`-modules, and an `\mathcal O`-module `\mathcal F`, there is a spectral
sequence with `E_1^{i,j} = \operatorname{Ext}^j_{\mathcal O}(K^{-i}, \mathcal F)` abutting to
`\operatorname{Ext}^{i + j}_{\mathcal O}(K^\bullet, \mathcal F)`. -/
theorem ringedSiteExt_termwise_spectralSequence_exists
    (K : CochainComplex Mod ℤ) (ℱ : Mod) (hK : cochainComplexIsBoundedAbove K) :
    ∃ S : DerivedExtStupidFiltrationSpectralSequenceData K ((single0).obj ℱ),
      filteredComplexAssociatedSpectralSequenceConverges
        S.filteredComplex S.spectralSequence := by
  obtain ⟨S⟩ := derivedExt_stupidFiltration_spectralSequence_exists
    K ((single0).obj ℱ)
  refine ⟨S, ?_⟩
  exact S.converges_of_boundedness hK ⟨0, ringedSiteModule_single_isGE_zero J 𝒪 ℱ⟩

end
