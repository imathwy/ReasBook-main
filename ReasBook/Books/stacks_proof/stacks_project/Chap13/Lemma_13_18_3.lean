import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap13.Definition_13_18_1
import stacks_proof.stacks_project.Chap13.Lemma_13_15_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped ZeroObject

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
variable {K : CochainComplex 𝒜 ℤ}

local instance isInjective_containsZero : (isInjective 𝒜).ContainsZero where
  exists_zero := ⟨0, isZero_zero 𝒜, inferInstance⟩

local instance isInjective_hasMonoEmbedding : HasMonoEmbedding (isInjective 𝒜) where
  exists_mono X := ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩

/- Domain-style sampling:
- primary domain: bounded-below injective resolutions of cochain complexes in an abelian category
  with enough injectives;
- sampled owner declarations:
  `CategoryTheory.InjectiveResolution.of`,
  `CategoryTheory.HasInjectiveResolutions`,
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.PlusWithTermsIn`,
  `IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn`;
- best owner abstraction: `CochainComplex.InjectiveResolution` is the source-facing owner for a
  chosen injective resolution of a cochain complex, while the bounded-below termwise-monomorphic
  enhancement belongs to the Chapter `13.15` owner
  `IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn`, whose target packages canonically through
  `CochainComplex.PlusWithTermsIn`;
- primitive data: a resolving cochain complex, the comparison morphism from `K`, and the
  bounded-below/injective/quasi-isomorphism data already owned by
  `CochainComplex.InjectiveResolution`;
- derived API: eventual homology vanishing, existence under enough injectives, and the extra
  termwise-monomorphic strengthening in part `(3)`.

Source/core/bridge triage:
- `source-facing`: the three existence statements below for injective resolutions of cochain
  complexes;
- `core/canonical`: the mathlib instance `HasInjectiveResolutions` under enough injectives, the
  project owner `CochainComplex.InjectiveResolution`, the bounded-below owner
  `CochainComplex.PlusWithTermsIn`, and the chapter owner
  `IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn`;
- `bridge/view`: the packaging of a Chapter `13.15` replacement into a
  `CochainComplex.InjectiveResolution`.
-/

/- Lemma 13.18.3 (1): in an abelian category with enough injectives, the canonical owner
`HasInjectiveResolutions 𝒜` is already provided by mathlib. -/
recall HasInjectiveResolutions

-- Proof sketch: choose a bound below which the homology of `K` vanishes, apply the bounded-below
-- replacement from Lemma 13.18.2, then use Lemma 13.15.5 with the object property of injective
-- objects and repackage the result as a bounded-below injective resolution.
/-- Lemma 13.18.3 (2): if a cochain complex has vanishing homology in all sufficiently negative
degrees, then it admits a bounded-below injective resolution. -/
@[stacks 013K]
theorem nonempty_injectiveResolution_of_eventually_isZero_homology
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    Nonempty (CochainComplex.InjectiveResolution K) := by
  obtain ⟨a, hK⟩ := hK
  obtain ⟨I, α, h⟩ :=
    exists_quasiIso_with_terms_in_of_isZero_homology_below (isInjective 𝒜) a K hK
  exact ⟨{
    complex := h.toPlusWithTermsIn,
    ι := α,
    quasiIso := h.quasiIso
  }⟩

-- Proof sketch: apply Lemma 13.15.5 to the bounded-below complex `K` with the object property of
-- injective objects. The resulting quasi-isomorphism is termwise monomorphic, its target remains
-- strictly concentrated in degrees `≥ a`, and its terms are injective.
/-- Lemma 13.18.3 (3): if `K` is zero in degrees below `a`, then `K` admits an injective
resolution whose target is also zero below `a` and whose comparison morphism is termwise
monomorphic. -/
@[stacks 013K]
theorem exists_injectiveResolution_strictlyGE_with_termwise_mono
    (a : ℤ) (hK : K.IsStrictlyGE a) :
    ∃ I : CochainComplex.InjectiveResolution K,
      ((I : CochainComplex 𝒜 ℤ).IsStrictlyGE a) ∧ ∀ n : ℤ, Mono (I.ι.f n) := by
  obtain ⟨I, α, h⟩ :=
    exists_termwiseMono_quasiIso_with_terms_in_of_isStrictlyGE (isInjective 𝒜) a K hK
  exact ⟨{ complex := h.toPlusWithTermsIn, ι := α, quasiIso := h.quasiIso },
    h.strictlyGE, h.term_mono⟩

end
