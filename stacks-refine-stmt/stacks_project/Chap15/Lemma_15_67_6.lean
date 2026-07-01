import Mathlib
import stacks_project.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

section

variable {R : Type u} [CommRing R]

namespace ModuleCat

variable (M : ModuleCat R)

/- Domain-style sampling:
- primary domain: tor dimension of modules over a commutative ring and its source-facing
  description by finite flat resolutions;
- sampled owner declarations:
  `CategoryTheory.ModuleHasTorDimensionLE`,
  `CategoryTheory.hasTorAmplitudeIn_iff_exists_flat_representative`,
  `ModuleCat.HasFiniteProjectiveResolutionLengthLE`,
  `CochainComplex.IsTermwiseFlat`;
- best owner abstraction: the chapter-level core owner remains
  `CategoryTheory.ModuleHasTorDimensionLE`, while the source-facing finite-resolution notion in
  this file should live alongside the analogous projective-resolution owner
  `ModuleCat.HasFiniteProjectiveResolutionLengthLE` rather than as a parallel global predicate;
- primitive vs. derived:
  primitive data are the flat modules `F i`, the differentials `δ`, the augmentation `π`, and the
  exactness/surjectivity/injectivity conditions expressing a finite flat resolution of `M`;
  derived API are the zero-length characterization and the equivalence with tor dimension at most
  `d`.

Source/core/bridge triage:
- `source-facing`: `ModuleCat.HasFiniteFlatResolutionLengthLE`;
- `core/canonical`: `CategoryTheory.ModuleHasTorDimensionLE`;
- `bridge/view`: the bounded flat representative criterion from Lemma `15.67.3`, which explains
  why the source-facing resolution predicate is equivalent to the tor-dimension owner.
-/

/-- A finite flat resolution of an `R`-module `M` of length at most `d`. For `d = 0` this is
just flatness of `M`; for `d = n + 1` it is an exact sequence
`0 ⟶ F_{n + 1} ⟶ F_n ⟶ ⋯ ⟶ F₀ ⟶ M ⟶ 0`
whose terms `Fᵢ` are flat. -/
def HasFiniteFlatResolutionLengthLE (d : ℕ) : Prop :=
  match d with
  | 0 => Module.Flat R M
  | n + 1 =>
      ∃ (F : Fin (n + 2) → ModuleCat R),
        (∀ i, Module.Flat R (F i)) ∧
          ∃ (δ : (i : Fin (n + 1)) → F i.succ ⟶ F i.castSucc)
            (π : F 0 ⟶ M),
            Function.Surjective π ∧
              Function.Exact (δ 0) π ∧
              (∀ i : Fin n, Function.Exact (δ i.succ) (δ i.castSucc)) ∧
              Function.Injective (δ (Fin.last n))

-- Proof sketch: unfold `HasFiniteFlatResolutionLengthLE`; the `d = 0` branch is defined to be
-- flatness of `M`.
/-- A finite flat resolution of length at most `0` is exactly flatness. -/
theorem hasFiniteFlatResolutionLengthLE_zero_iff :
    HasFiniteFlatResolutionLengthLE M 0 ↔ Module.Flat R M :=
  Iff.rfl

-- Proof sketch: the forward implication rewrites tor dimension `≤ d` as tor-amplitude in
-- `[-d, 0]` for `M[0]` and then applies Lemma `15.67.3` to obtain a flat representative
-- supported in that range, which is exactly a flat resolution of length at most `d`. For the
-- reverse implication, such a flat resolution gives a flat representative of `M[0]` in the same
-- range, so Lemma `15.67.3` yields tor-amplitude in `[-d, 0]`.
/-- Lemma 15.67.6: an `R`-module `M` has tor dimension at most `d` if and only if it admits a
finite flat resolution of length at most `d`. -/
theorem hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE (d : ℕ) :
    ModuleHasTorDimensionLE M d ↔ HasFiniteFlatResolutionLengthLE M d := sorry

/-- A module of tor dimension at most `d` admits a finite flat resolution of length at most
`d`. -/
theorem ModuleHasTorDimensionLE.hasFiniteFlatResolutionLengthLE {d : ℕ}
    (hM : ModuleHasTorDimensionLE M d) :
    HasFiniteFlatResolutionLengthLE M d :=
  (hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE M d).1 hM

/-- A finite flat resolution of length at most `d` gives tor dimension at most `d`. -/
theorem HasFiniteFlatResolutionLengthLE.hasTorDimensionLE {d : ℕ}
    (hM : HasFiniteFlatResolutionLengthLE M d) :
    ModuleHasTorDimensionLE M d :=
  (hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE M d).2 hM

-- Proof sketch: specialize `hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE` to
-- `d = 0` and use `hasFiniteFlatResolutionLengthLE_zero_iff`.
/-- An `R`-module has tor dimension at most `0` exactly when it is flat. -/
theorem hasTorDimensionLE_zero_iff_flat :
    ModuleHasTorDimensionLE M 0 ↔ Module.Flat R M :=
  (hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE M 0).trans
    (hasFiniteFlatResolutionLengthLE_zero_iff M)

end ModuleCat

end
