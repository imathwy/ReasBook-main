import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Length

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Length

open Order Submodule

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: `Submodule.localized'gi` is the canonical Galois insertion between submodules of
-- `M` and submodules of `LocalizedModule S M`. Its upper adjoint is strictly monotone, so the
-- coheight of `⊥` in the localized submodule lattice is bounded by the coheight of its inverse
-- image in `Submodule R M`, which is in turn bounded by the coheight of `⊥`.
/-- Lemma 10.52.7: localizing an `R`-module at a multiplicative subset does not increase its
length. -/
theorem length_localizedModule_le :
    Module.length (Localization S) (LocalizedModule S M) ≤ Module.length R M := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  let u : Submodule (Localization S) (LocalizedModule S M) → Submodule R M :=
    comap (LocalizedModule.mkLinearMap S M) ∘ restrictScalars R
  have hu : StrictMono u := by
    simpa [u] using
      (localized'gi (Localization S) S (LocalizedModule.mkLinearMap S M)).strictMono_u
  calc
    coheight (⊥ : Submodule (Localization S) (LocalizedModule S M)) ≤ coheight (u ⊥) := by
      simpa [u] using
        coheight_le_coheight_apply_of_strictMono u hu
          (⊥ : Submodule (Localization S) (LocalizedModule S M))
    _ ≤ coheight (⊥ : Submodule R M) := coheight_anti bot_le

end Length
