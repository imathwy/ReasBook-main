import Mathlib
import stacks_project.Chap10.Definition_10_71_2
import stacks_project.Chap10.Lemma_10_71_1
import stacks_project.Chap10.Definition_10_103_8
import stacks_project.Chap10.Definition_10_104_1
import stacks_project.Chap10.Lemma_10_104_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ChainComplex

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- Domain-style sampling:
* primary domain: finite free resolutions and maximal Cohen-Macaulay syzygies over Noetherian
  local Cohen-Macaulay rings;
* sampled owner declarations:
  `module_exists_finite_free_resolution`,
  `ChainComplex.IsFiniteFreeResolution`,
  `Module.MaximalCohenMacaulay`,
  `Module.CohenMacaulay`;
* best owner abstraction: a chosen finite free resolution
  `π : F ⟶ moduleSingle[R] M`, together with the textbook syzygy indexing convention;
* source/core/bridge triage:
  `ChainComplex.SyzygyMaximalCohenMacaulay` is the source-facing owner predicate for the textbook
  `(d - e)`th syzygy of an augmented free resolution;
  `ChainComplex.IsFiniteFreeResolution π` is the canonical owner of the chosen finite free
  resolution data;
  the main theorem is the source-facing existence statement obtained by choosing such a
  resolution and proving the chosen-resolution helper below.
-/

namespace ChainComplex

/-- The `n`th syzygy of an augmentation `π : F ⟶ moduleSingle[R] M` is maximal Cohen-Macaulay,
with the chapter's indexing convention: degree `0` is `M`, degree `1` is the augmentation kernel,
and degree `n + 2` is the kernel of the differential `F.X (n + 1) ⟶ F.X n`. -/
def SyzygyMaximalCohenMacaulay {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) (n : ℕ) : Prop :=
  match n with
  | 0 => Module.MaximalCohenMacaulay R M
  | 1 => Module.MaximalCohenMacaulay R (LinearMap.ker (π.f 0).hom)
  | n + 2 => Module.MaximalCohenMacaulay R (LinearMap.ker (F.d (n + 1) n).hom)

end ChainComplex

/-- Helper for Lemma 10.104.9: every chosen finite free resolution has maximal Cohen-Macaulay
`(d - e)`th syzygy when `moduleDepth R M = e`. -/
private theorem isFiniteFreeResolution_syzygy_maximalCohenMacaulay_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R]M} (hπ : IsFiniteFreeResolution π) :
    ChainComplex.SyzygyMaximalCohenMacaulay π (d - e) :=
  -- TODO: follow the source-faithful route by iterating Lemma 10.104.8 along the short exact
  -- syzygy sequences inside a chosen finite free resolution until the depth reaches `d`.
  sorry

-- Proof sketch: choose any finite free resolution of `M`, then invoke the chosen-resolution
-- helper above to obtain the maximal Cohen-Macaulay syzygy at the source-prescribed stage.
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
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] M),
      IsFiniteFreeResolution π ∧
      SyzygyMaximalCohenMacaulay π (d - e) := by
  -- Choose a finite free resolution and transfer the remaining work to the chosen-resolution
  -- helper.
  rcases module_exists_finite_free_resolution (R := R) (M := M) with ⟨F, π, hπ⟩
  refine ⟨F, π, hπ, ?_⟩
  exact isFiniteFreeResolution_syzygy_maximalCohenMacaulay_of_moduleDepth
    (R := R) (M := M) hCM hdim hdepth hπ

/-- Companion form of Lemma 10.104.9 for a chosen finite free resolution: every finite free
resolution of `M` has maximal Cohen-Macaulay `(d - e)`th syzygy. -/
theorem maximalCohenMacaulay_syzygy_of_isFiniteFreeResolution_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R]M} (hπ : IsFiniteFreeResolution π) :
    SyzygyMaximalCohenMacaulay π (d - e) := by
  -- Reuse the private chosen-resolution helper directly; this is the source-facing fixed
  -- resolution form of the lemma.
  exact isFiniteFreeResolution_syzygy_maximalCohenMacaulay_of_moduleDepth
    (R := R) (M := M) hCM hdim hdepth hπ

end
