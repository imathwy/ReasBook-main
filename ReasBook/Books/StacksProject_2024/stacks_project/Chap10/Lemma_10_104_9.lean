import Mathlib
import StacksProject_2024.Chap10.Definition_10_71_2
import StacksProject_2024.Chap10.Lemma_10_71_1
import StacksProject_2024.Chap10.Definition_10_103_8
import StacksProject_2024.Chap10.Definition_10_104_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ChainComplex

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- Domain-style sampling:
* primary domain: finite free resolutions and maximal Cohen-Macaulay syzygies over Noetherian
  local Cohen-Macaulay rings;
* sampled owner declarations:
  `module_exists_finite_free_resolution`,
  `ChainComplex.IsFiniteFreeResolution`,
  `ProjectiveResolution.SyzygyProjective`,
  `Module.MaximalCohenMacaulay`,
  `HasFiniteFreeResolutionLengthLE`,
  `Module.CohenMacaulay`;
* best owner abstraction: a chosen finite free resolution
  `π : F ⟶ moduleSingle[R] M` with `ChainComplex.IsFiniteFreeResolution π`, together with the
  augmented-syzygy indexing pattern already used by
  `ProjectiveResolution.SyzygyProjective`; the source-facing existential theorem should construct
  such a witness using `module_exists_finite_free_resolution`, while the canonical syzygy indexing
  remains: the `0`th syzygy is `M` itself, the `1`st syzygy is `ker (π.f 0).hom`, and the
  `(n + 2)`nd syzygy is `ker (F.d (n + 1) n).hom`;
* source/core/bridge triage:
  `ChainComplex.SyzygyMaximalCohenMacaulay` below is the source-facing owner predicate for the
  textbook syzygy stage of an augmented free resolution;
  the main theorem below is `source-facing`, because it gives the textbook existential exact
  complex through the chapter's canonical finite-free-resolution owner language;
  `ChainComplex.IsFiniteFreeResolution π` and the chapter's projective-resolution owner
  `ProjectiveResolution.SyzygyProjective` are `core/canonical`;
  the chosen-resolution theorem below is the `bridge/view` saying that every finite free
  resolution computes the same maximal Cohen-Macaulay syzygy stage;
  the raw kernels `LinearMap.ker (π.f 0).hom` and `LinearMap.ker (F.d (n + 1) n).hom` are
  `bridge/view` presentations of the same indexed syzygy owner;
* primitive data: a finite free resolution `π : F ⟶ moduleSingle[R] M`;
* derived API: the maximal Cohen-Macaulay property of the textbook `(d - e)`th syzygy, and the
  source-facing existential packaging obtained by choosing such a resolution.

The source lemma is not about assuming a bounded finite free resolution. The bounded owner
`HasFiniteFreeResolutionLengthLE` is still useful elsewhere in the chapter, but making it the main
input here strengthens the semantics beyond the source statement. The public surface should instead
construct a finite free resolution and assert that its `(d - e)`th syzygy is maximal
Cohen-Macaulay.
-/

namespace ChainComplex

/-- The `(n)`th syzygy of an augmentation `π : F ⟶ moduleSingle[R] M` is maximal Cohen-Macaulay,
with the chapter's indexing convention: degree `0` is `M`, degree `1` is the augmentation kernel,
and degree `n + 2` is the kernel of the differential `F.X (n + 1) ⟶ F.X n`. -/
def SyzygyMaximalCohenMacaulay {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) (n : ℕ) : Prop :=
  match n with
  | 0 => Module.MaximalCohenMacaulay R M
  | 1 => Module.MaximalCohenMacaulay R (LinearMap.ker (π.f 0).hom)
  | n + 2 => Module.MaximalCohenMacaulay R (LinearMap.ker (F.d (n + 1) n).hom)

end ChainComplex

-- Proof sketch: start from a finite free resolution of `M` over the Noetherian local ring `R`,
-- and consider the successive syzygies. Apply Lemma `10.104.8` inductively to the short exact
-- sequences coming from the resolution to see that the depth increases by one at each step until
-- it reaches `d`; after `d - e` steps the resulting syzygy is therefore maximal Cohen-Macaulay.
/-- Lemma 10.104.9: if `R` is a local Noetherian Cohen-Macaulay ring of dimension `d` and `M` is
a finite `R`-module of depth `e`, then `M` admits a finite free resolution whose `(d - e)`th
syzygy is maximal Cohen-Macaulay. Equivalently, truncating that resolution after `d - e` steps
gives an exact complex
`0 → K → F_{d - e - 1} → ⋯ → F₀ → M → 0`
with the `Fᵢ` finite free and `K` maximal Cohen-Macaulay. With the chapter's convention, the `0`th
syzygy is `M` itself, the `1`st syzygy is `ker (F₀ ⟶ M)`, and the `(n + 2)`nd syzygy is
`ker (F_{n+1} ⟶ F_n)`. -/
theorem exists_maximalCohenMacaulay_syzygy_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R]M),
      IsFiniteFreeResolution π ∧
      SyzygyMaximalCohenMacaulay π (d - e) := by
  sorry

/-- Companion form of Lemma 10.104.9 for a chosen finite free resolution: every finite free
resolution of `M` has maximal Cohen-Macaulay `(d - e)`th syzygy. -/
theorem maximalCohenMacaulay_syzygy_of_isFiniteFreeResolution_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R]M} (hπ : IsFiniteFreeResolution π) :
    SyzygyMaximalCohenMacaulay π (d - e) := by
  sorry

end
