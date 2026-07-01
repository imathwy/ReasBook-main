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
point of the subset has an open neighborhood on which the map extends to a smooth map. We express
the local extension through the canonical owner `C^∞⟮I, U; I', N⟯` for smooth maps on the open set
`U : Opens M`. -/
def IsSmoothOn {A : Set M} (f : A → N) (I : ModelWithCorners 𝕜 E H)
    (I' : ModelWithCorners 𝕜 E' H') : Prop :=
  ∀ p : A,
    ∃ U : Opens M,
      (p : M) ∈ U ∧
        ∃ Fext : C^∞⟮I, U; I', N⟯,
          ∀ q : A, (hq : (q : M) ∈ U) → Fext ⟨q, hq⟩ = f q

/-- `Function.IsSmoothOn` is equivalent to the unbundled local-extension formulation. -/
theorem isSmoothOn_iff_exists_local_extension {A : Set M} {f : A → N} :
    f.IsSmoothOn I I' ↔
      ∀ p : A,
        ∃ U : Set M,
          IsOpen U ∧
            (p : M) ∈ U ∧
              ∃ Fext : M → N,
                ContMDiffOn I I' (∞ : ℕ∞ω) Fext U ∧
                  ∀ q : A, (q : M) ∈ U → Fext q = f q := by
  classical
  constructor
  · intro hf p
    rcases hf p with ⟨U, hpU, Fext, hFext⟩
    refine ⟨U, U.isOpen, hpU, ?_⟩
    let G : M → N := fun x ↦ if hx : x ∈ U then Fext ⟨x, hx⟩ else Fext ⟨p, hpU⟩
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      have hG_subtype : ContMDiffAt I I' (∞ : ℕ∞ω) (fun y : U ↦ G y) ⟨x, hx⟩ := by
        have hEq : (fun y : U ↦ G y) = Fext := by
          funext y
          change G y = Fext y
          simp [G]
        rw [hEq]
        exact Fext.contMDiff ⟨x, hx⟩
      exact (contMDiffAt_subtype_iff.1 hG_subtype).contMDiffWithinAt
    · intro q hq
      unfold G
      split_ifs with h
      · simpa using hFext q h
      · exact (h hq).elim
  · intro hf p
    rcases hf p with ⟨U, hU, hpU, Fext, hFext, hEq⟩
    let Uo : Opens M := ⟨U, hU⟩
    refine ⟨Uo, hpU, ?_⟩
    refine ⟨⟨fun x : Uo ↦ Fext x, ?_⟩, ?_⟩
    · intro x
      exact contMDiffAt_subtype_iff.2 <|
        (hFext x x.property).contMDiffAt <|
          hU.mem_nhds x.property
    · intro q hq
      exact hEq q hq

end Function
