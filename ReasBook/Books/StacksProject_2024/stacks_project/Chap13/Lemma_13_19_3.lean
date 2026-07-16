import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped ZeroObject

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughProjectives 𝒜]
variable {K : CochainComplex 𝒜 ℤ}

local instance isProjective_containsZero : (isProjective 𝒜).ContainsZero where
  exists_zero := ⟨(0 : 𝒜), Limits.isZero_zero 𝒜, inferInstance⟩

local instance isProjective_hasEpiCover : HasEpiCover (isProjective 𝒜) where
  exists_epi X := ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩

/- Domain-style sampling:
- primary domain: bounded-above projective resolutions of cochain complexes in an abelian category
  with enough projectives;
- sampled owner declarations:
  `CategoryTheory.HasProjectiveResolutions`,
  `CategoryTheory.ProjectiveResolution.of`,
  `CochainComplex.ProjectiveResolution`,
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- best owner abstraction: `CochainComplex.ProjectiveResolution` is the source-facing owner for a
  chosen projective resolution of a cochain complex, while the bounded-above termwise-epimorphic
  enhancement belongs to the Chapter `13.15` owner
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- primitive data: a resolving cochain complex, the comparison morphism to the target complex, and
  the bounded-above/projective/quasi-isomorphism data already owned by
  `CochainComplex.ProjectiveResolution`;
- derived API: eventual homology vanishing, existence under enough projectives, and the extra
  termwise-epimorphic strengthening in part `(3)`.

Source/core/bridge triage:
- `source-facing`: the two existence statements below for projective resolutions of cochain
  complexes;
- `core/canonical`: the mathlib instance `HasProjectiveResolutions` under enough projectives, the
  chapter owner `CochainComplex.ProjectiveResolution`, and the chapter owner
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- `bridge/view`: the packaging of a Chapter `13.15` replacement into a
  `CochainComplex.ProjectiveResolution`.
-/

/- Lemma 13.19.3 (1): in an abelian category with enough projectives, the canonical owner
`HasProjectiveResolutions 𝒜` is already provided by mathlib. -/
recall HasProjectiveResolutions

-- Proof sketch: apply the canonical bounded-above truncation replacement from Lemma 13.11.5 and
-- then resolve the resulting bounded-above complex degreewise by projectives as in
-- Lemma 13.15.4, packaging the outcome in the chapter owner
-- `CochainComplex.ProjectiveResolution K`.
/-- Lemma 13.19.3 (2): if a cochain complex has vanishing homology in all sufficiently positive
degrees, then it admits a projective resolution. -/
theorem nonempty_projectiveResolution_of_eventually_isZero_homology
    (hK : ∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    Nonempty (CochainComplex.ProjectiveResolution K) := by
  obtain ⟨a, hK⟩ := hK
  obtain ⟨Q, π, hπ⟩ :=
    exists_quasiIso_with_terms_in_of_isZero_homology_above (isProjective 𝒜) a K hK
  exact ⟨{ complex := hπ.toMinusWithTermsIn, π := π, quasiIso := hπ.quasiIso }⟩

-- Proof sketch: start from the bounded-above complex `K`, construct projective presentations
-- degreewise beginning at the top degree, and splice them inductively so that the resulting
-- comparison morphism is termwise epimorphic; then package the resolving complex and its
-- quasi-isomorphism to `K` as a `ProjectiveResolution K`.
/-- Lemma 13.19.3 (3): if `K` is zero in degrees above `a`, then there exists a projective
resolution whose resolving complex is also zero above `a` and whose comparison morphism is
termwise epimorphic. -/
theorem exists_projectiveResolution_strictlyLE_with_termwise_epi
    (a : ℤ) (hK : K.IsStrictlyLE a) :
    ∃ P : CochainComplex.ProjectiveResolution K,
      (P : CochainComplex 𝒜 ℤ).IsStrictlyLE a ∧ ∀ n : ℤ, Epi (P.π.f n) := by
  obtain ⟨Q, π, hπ⟩ :=
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE (isProjective 𝒜) a K hK
  exact ⟨{ complex := hπ.toMinusWithTermsIn, π := π, quasiIso := hπ.quasiIso },
    hπ.strictlyLE, hπ.term_epi⟩

end
