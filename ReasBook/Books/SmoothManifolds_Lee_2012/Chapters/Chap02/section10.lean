import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Algebra

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_10_extra_1 (from Chap02/Sec02_10) -/
/- Definition 2.10-extra-1: a function with the properties of the function `h` from Lemma 2.21 is
usually called a cutoff function. In this project, Lemma 2.21 is stated directly as the existence
theorem `exists_one_zero_smooth_cutoff`, built from the canonical owner `Real.smoothTransition`. -/
#check exists_one_zero_smooth_cutoff

/-! ### Definition_2_10_extra_2 (from Chap02/Sec02_10) -/
/- Definition 2.10-extra-2: The Euclidean cutoff from `Lemma_2.22` is a bundled
`ContDiffBump`, and `SmoothBumpFunction` is the canonical manifold-level generalization used
later in the chapter. -/
recall ContDiffBump

/- The chapter's Euclidean existence theorem is the source-facing bridge to this canonical owner. -/
recall exists_smooth_ball_cutoff

/- `SmoothBumpFunction` is the manifold-level generalization of Euclidean smooth bump functions. -/
recall SmoothBumpFunction

/-! ### Definition_2_10_extra_3 (from Chap02/Sec02_10) -/
/- Definition 2.10-extra-3: the support of a function on a topological space is the topological
support `tsupport f`, i.e. the closure of the set where the function is nonzero, and compact
support is formalized by `HasCompactSupport`. -/
recall tsupport

/- In mathlib and in the surrounding chapter files, “`f` is supported in `U`” is written directly
as `tsupport f ⊆ U`; no separate owner declaration is introduced for this view. -/

-- `HasCompactSupport f` is the canonical mathlib notion that `f` is compactly supported.
recall HasCompactSupport

/- Any function on a compact space is compactly supported; this is
`HasCompactSupport.of_compactSpace`. -/
recall HasCompactSupport.of_compactSpace

/-! ### Definition_2_10_extra_4 (from Chap02/Sec02_10) -/
universe uι uE uH uM

/- Definition 2.10-extra-4 (source-facing, recalling the canonical owner): a partition of unity
subordinate to an indexed open cover is formalized by `PartitionOfUnity.IsSubordinate`. -/
recall PartitionOfUnity.IsSubordinate
  {ι : Type uι} {M : Type uM} [TopologicalSpace M] {s : Set M}
  (f : PartitionOfUnity ι M s) (U : ι → Set M) : Prop

/- The smooth variant is formalized by `SmoothPartitionOfUnity.IsSubordinate`. -/
recall SmoothPartitionOfUnity.IsSubordinate
  {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}
  (f : SmoothPartitionOfUnity ι I M s) (U : ι → Set M) : Prop

/-! ### Problem_2_10 (from Chap02/Sec02_12) -/
universe uM uN uE uH uE' uH'

open scoped Manifold ContDiff

section ContinuousPullback

variable {M : Type uM} [TopologicalSpace M]
variable {N : Type uN} [TopologicalSpace N]

-- Proof sketch: `ContinuousMap.compRightAlgHom ℝ ℝ F` is already an `ℝ`-algebra homomorphism, so
-- its underlying function is automatically `ℝ`-linear.
/-- Problem 2-10 (1): For a continuous map `F : M → N`, pullback along `F` is an `ℝ`-linear map on
continuous real-valued functions. -/
theorem continuous_pullback_isLinearMap (F : C(M, N)) :
    IsLinearMap ℝ ⇑(ContinuousMap.compRightAlgHom ℝ ℝ F) := sorry

end ContinuousPullback

section SmoothPullback

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

-- Proof sketch: If `F` is smooth, compose any bundled smooth function `f : C^∞⟮J, N; ℝ⟯` with
-- `F`. Conversely, apply the hypothesis to enough smooth coordinate functions and use the standard
-- smoothness criterion in charts.
/-- Problem 2-10 (2): A map between smooth manifolds is smooth exactly when pullback along it sends
every smooth real-valued function on the target to a smooth real-valued function on the source. -/
theorem smooth_iff_pullback_preserves_smooth_real_functions {F : M → N} :
    ContMDiff I J ∞ F ↔
      ∀ f : C^∞⟮J, N; ℝ⟯, ContMDiff I 𝓘(ℝ) ∞ (f ∘ F) := sorry

-- Proof sketch: Apply part (2) to the forward map of the homeomorphism.
/-- Problem 2-10 (3): For a homeomorphism `F`, smoothness of the forward map is equivalent to
pullback by `F` preserving smooth real-valued functions. -/
theorem homeomorph_is_diffeomorphism_iff_pullback_preserves_smooth_real_functions_forward
    (F : M ≃ₜ N) :
    ContMDiff I J ∞ F ↔
      ∀ f : C^∞⟮J, N; ℝ⟯, ContMDiff I 𝓘(ℝ) ∞ (f ∘ F) := sorry

-- Proof sketch: Apply part (2) to the inverse homeomorphism `F.symm`.
/-- Problem 2-10 (4): For a homeomorphism `F`, smoothness of the inverse map is equivalent to
pullback by `F.symm` preserving smooth real-valued functions. -/
theorem homeomorph_is_diffeomorphism_iff_pullback_preserves_smooth_real_functions_inverse
    (F : M ≃ₜ N) :
    ContMDiff J I ∞ F.symm ↔
      ∀ g : C^∞⟮I, M; ℝ⟯, ContMDiff J 𝓘(ℝ) ∞ (g ∘ F.symm) := sorry

end SmoothPullback

/-! ### Proposition_2_10 (from Chap02/Sec02_08) -/
open TopologicalSpace
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN uE'' uH'' uP

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type uH'} [TopologicalSpace H']
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type uH''} [TopologicalSpace H'']
  {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P]
  {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E' H'}
  {I'' : ModelWithCorners 𝕜 E'' H''}
  [IsManifold I (∞ : ℕ∞ω) M] [IsManifold I' (∞ : ℕ∞ω) N] [IsManifold I'' (∞ : ℕ∞ω) P]
  {c : N} {U : Opens M} {F : M → N} {G : N → P}

/- Proposition 2.10 (1): every constant map between smooth manifolds is smooth. The canonical
owner theorem is `contMDiff_const`, specialized here to `C^∞`. -/
#check (contMDiff_const : ContMDiff I I' (∞ : ℕ∞ω) (fun _ : M ↦ c))

/- Proposition 2.10 (2): the identity map of a smooth manifold is smooth. The canonical owner
theorem is `contMDiff_id`, specialized here to `C^∞`. -/
#check (contMDiff_id : ContMDiff I I (∞ : ℕ∞ω) (id : M → M))

/- Proposition 2.10 (3): the inclusion of an open submanifold into the ambient manifold is
smooth. The canonical owner theorem is `contMDiff_subtype_val`, specialized here to `C^∞`. -/
#check (contMDiff_subtype_val : ContMDiff I I (∞ : ℕ∞ω) (Subtype.val : U → M))

/- Proposition 2.10 (4): the composite of two smooth maps is smooth. The canonical owner theorem
is `ContMDiff.comp`, specialized here to `C^∞`. -/
#check
  (ContMDiff.comp :
    ContMDiff I' I'' (∞ : ℕ∞ω) G →
      ContMDiff I I' (∞ : ℕ∞ω) F →
        ContMDiff I I'' (∞ : ℕ∞ω) (G ∘ F))
