import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiffMap

-- Declarations for this item will be appended below by the statement pipeline.
open scoped Manifold ContDiff
open TopologicalSpace

universe uK uE uH uM uE2 uH2 uN

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE2} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH2} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}

namespace Function

/-- Definition 2.11-extra-2: A map defined on a subset of a smooth manifold is smooth if every
point of the subset has an open neighborhood on which the map extends to an ambient smooth map.
The primitive owner data is the unbundled local extension property stated with `ContMDiffOn`; the
bundled `C^∞⟮I, U; I', N⟯` view is a derived bridge. -/
def IsSmoothOn {A : Set M} (f : A → N) (I : ModelWithCorners 𝕜 E H)
    (I' : ModelWithCorners 𝕜 E' H') : Prop :=
  ∀ p : A,
    ∃ U : Set M,
      IsOpen U ∧
        (p : M) ∈ U ∧
          ∃ Fext : M → N,
            ContMDiffOn I I' (∞ : ℕ∞ω) Fext U ∧
              ∀ q : A, (q : M) ∈ U → Fext q = f q

/-- `Function.IsSmoothOn` is equivalent to the unbundled local-extension formulation. -/
theorem isSmoothOn_iff_exists_local_extension {A : Set M} {f : A → N} :
    f.IsSmoothOn I I' ↔
      ∀ p : A,
        ∃ U : Set M,
          IsOpen U ∧
            (p : M) ∈ U ∧
              ∃ Fext : M → N,
                ContMDiffOn I I' (∞ : ℕ∞ω) Fext U ∧
                  ∀ q : A, (q : M) ∈ U → Fext q = f q :=
  Iff.rfl

/-- The source-facing owner `Function.IsSmoothOn` can be repackaged through the canonical bundled
owner `C^∞⟮I, U; I', N⟯` on an open ambient neighborhood `U : Opens M`. -/
theorem isSmoothOn_iff_exists_contMDiffMap_local_extension {A : Set M} {f : A → N} :
    f.IsSmoothOn I I' ↔
      ∀ p : A,
        ∃ U : Opens M,
          (p : M) ∈ U ∧
            ∃ Fext : C^∞⟮I, U; I', N⟯,
              ∀ q : A, (hq : (q : M) ∈ U) → Fext ⟨q, hq⟩ = f q := by
  sorry

end Function
