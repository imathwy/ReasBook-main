import Mathlib
import stacks_project.Chap10.Definition_10_71_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory ChainComplex Limits

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-
Domain-style sampling:
* primary domain: free resolutions of modules and their boundedness properties;
* sampled owner declarations:
  `ChainComplex.IsFreeResolution`,
  `ChainComplex.IsFiniteFreeResolution`,
  `ChainComplex.IsTermwiseFree`,
  `CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)`;
* best owner abstraction: `ChainComplex.IsFreeResolution π` for an augmentation
  `π : F ⟶ moduleSingle[R] M`;
* layer triage:
  `ChainComplex.IsFreeResolution` is `core/canonical`,
  `HasFreeResolutionLengthLE` and `HasFiniteFreeResolutionLengthLE` below are `source-facing`,
  the final equivalence with `HasProjectiveDimensionLE (ModuleCat.of R M) d` is a `bridge/view`;
* primitive data: a free resolution `π : F ⟶ moduleSingle[R] M`;
* derived API: the length bound, expressed by vanishing of the complex above degree `d`, and the
  extra termwise-finite hypothesis when the source calls the resolution finite free.
-/

/-- `M` admits a free resolution of length at most `d`. For `d = 0` this means that `M`
itself is free; for `d = n + 1` it is an exact sequence
`0 ⟶ P_{n+1} ⟶ P_n ⟶ ⋯ ⟶ P₀ ⟶ M ⟶ 0`
with every `Pᵢ` free. -/
def HasFreeResolutionLengthLE
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (d : ℕ) : Prop :=
  ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] M),
    IsFreeResolution π ∧
      ∀ n : ℕ, d < n → IsZero (F.X n)

-- Proof sketch: if the resolution is supported in degree `0`, then its augmentation identifies
-- `M` with the degree-`0` term of a free resolution, so `M` is free; conversely, a free module is
-- resolved by the degree-`0` chain complex `single₀`.
/-- A free resolution of length at most `0` is exactly freeness of `M`. -/
theorem hasFreeResolutionLengthLE_zero_iff :
    HasFreeResolutionLengthLE R M 0 ↔ Module.Free R M :=
  sorry

/-- `M` admits a finite free resolution of length at most `d`. For `d = 0` this means that `M`
itself is finite free; for `d = n + 1` it is an exact sequence
`0 ⟶ P_{n+1} ⟶ P_n ⟶ ⋯ ⟶ P₀ ⟶ M ⟶ 0`
with every `Pᵢ` finite free. -/
def HasFiniteFreeResolutionLengthLE
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (d : ℕ) : Prop :=
  ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] M),
    IsFiniteFreeResolution π ∧
      ∀ n : ℕ, d < n → IsZero (F.X n)

/-- A finite free resolution of length at most `0` is exactly finite freeness of `M`. -/
theorem hasFiniteFreeResolutionLengthLE_zero_iff :
    HasFiniteFreeResolutionLengthLE R M 0 ↔ Module.Free R M ∧ Module.Finite R M :=
  sorry

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: combine Lemma `10.109.4`, which identifies `HasProjectiveDimensionLE` with the
-- existence of a finite projective resolution of length at most `d`, with Theorem `10.85.4`,
-- which says that projective modules over a local ring are free.
/-- Lemma 10.109.5: for a module over a local ring, having projective dimension at most `d` is
equivalent to admitting a free resolution of length at most `d`. Combined with Lemma `10.109.4`,
this says that the four equivalent conditions there are also equivalent to the existence of such a
free resolution. -/
theorem hasProjectiveDimensionLE_iff_hasFreeResolutionLengthLE (d : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d ↔
      HasFreeResolutionLengthLE R M d := sorry

end
