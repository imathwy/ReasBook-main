import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

section

variable {R : Type u} [Ring R]

/-
Domain-style sampling:
* primary domain: projective dimension in `ModuleCat R`, together with projective resolutions and
  source-facing bounded exact sequences.
* inspected owner declarations:
  `CategoryTheory.ProjectiveResolution`,
  `CategoryTheory.projectiveResolution`,
  `CategoryTheory.HasProjectiveDimensionLE`,
  `CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero`,
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`.
* best owner abstraction: `P : ProjectiveResolution M` for `M : ModuleCat R`.
* layer triage:
  `ProjectiveResolution.SyzygyProjective` is `core/canonical`,
  `HasFiniteProjectiveResolutionLengthLE` is `source-facing`,
  the TFAE below is a `bridge/view` between them and `HasProjectiveDimensionLE`.
* primitive data: the owner object `P : ProjectiveResolution M`.
* derived API: projectivity of the `d`th syzygy and the bounded finite-sequence reformulation of
  `HasProjectiveDimensionLE`.
-/

namespace CategoryTheory.ProjectiveResolution

variable {M : ModuleCat.{v} R}

/-- The textbook syzygy condition attached to a projective resolution in degree `d`. For `d = 0`
this says that `M` is projective, for `d = 1` it says that `ker(P₀ ⟶ M)` is projective, and for
`d ≥ 2` it says that `ker(P_{d-1} ⟶ P_{d-2})` is projective. -/
def SyzygyProjective (P : ProjectiveResolution M) (d : ℕ) : Prop :=
  match d with
  | 0 => Projective M
  | 1 => Projective (ModuleCat.of R (LinearMap.ker (P.π.f 0).hom))
  | n + 2 => Projective (ModuleCat.of R (LinearMap.ker (P.complex.d (n + 1) n).hom))

-- Proof sketch: unfold `SyzygyProjective` and read off the `d = 0` branch.
/-- In degree `0`, the syzygy-projective condition is exactly projectivity of `M`. -/
theorem syzygyProjective_zero_iff (P : ProjectiveResolution M) :
    P.SyzygyProjective 0 ↔ Projective M :=
  Iff.rfl

end CategoryTheory.ProjectiveResolution

variable (M : ModuleCat.{v} R)

/-- `M` admits a finite projective resolution of length at most `d`. For `d = 0` this means that
`M` itself is projective; for `d = n + 1` it is an exact sequence
`0 ⟶ P_{n+1} ⟶ P_n ⟶ ⋯ ⟶ P₀ ⟶ M ⟶ 0`
with every `Pᵢ` projective. -/
def HasFiniteProjectiveResolutionLengthLE (d : ℕ) : Prop :=
  match d with
  | 0 => Projective M
  | n + 1 =>
      ∃ (P : Fin (n + 2) → ModuleCat.{v} R),
        (∀ i, Projective (P i)) ∧
          ∃ (δ : (i : Fin (n + 1)) → P i.succ ⟶ P i.castSucc)
            (π : P 0 ⟶ M),
            Function.Surjective π ∧
              Function.Exact (δ 0) π ∧
              (∀ i : Fin n, Function.Exact (δ i.succ) (δ i.castSucc)) ∧
              Function.Injective (δ (Fin.last n))

-- Proof sketch: unfold `HasFiniteProjectiveResolutionLengthLE`; the `d = 0` branch is defined to
-- be projectivity of `M`.
/-- A finite projective resolution of length at most `0` is exactly projectivity of `M`. -/
theorem hasFiniteProjectiveResolutionLengthLE_zero_iff :
    HasFiniteProjectiveResolutionLengthLE M 0 ↔ Projective M :=
  Iff.rfl

/-- Lemma 10.109.4: the condition that `M` has projective dimension at most `d` is equivalent to
the existence of a finite projective resolution of length at most `d`, to the existence of some
projective resolution whose `d`th syzygy is projective, and to the assertion that every projective
resolution has projective `d`th syzygy. -/
-- Proof sketch: `(1) ↔ (2)` is the textbook definition of projective dimension. `(2) → (4)` is
-- the syzygy-projectivity criterion of Lemma `10.109.3`, `(4) → (3)` is immediate, and `(3) → (2)`
-- follows by truncating a projective resolution once the `d`th syzygy is projective.
theorem projectiveDimensionLE_tfae_resolution_conditions (d : ℕ) :
    List.TFAE
      [ HasProjectiveDimensionLE M d,
        HasFiniteProjectiveResolutionLengthLE M d,
        ∃ P : ProjectiveResolution M, P.SyzygyProjective d,
        ∀ P : ProjectiveResolution M, P.SyzygyProjective d ] := sorry

end
