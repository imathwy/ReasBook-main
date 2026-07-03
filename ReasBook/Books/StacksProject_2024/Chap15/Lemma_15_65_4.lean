import Mathlib
import StacksProject_2024.Chap10.Definition_10_71_2
import StacksProject_2024.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v w

namespace Module

/- Domain-style sampling for Lemma 15.65.4:
- primary domain: pseudo-coherence of modules concentrated in degree `0`, finite generation,
  finite presentation, and recursive finite free resolutions by syzygies;
- sampled owner declarations:
  `Module.Finite`,
  `Module.FinitePresentation`,
  `Module.Finite.iff_exists_surjective_free`,
  `ChainComplex.IsFiniteFreeResolution`;
- best owner abstraction: the source-facing recursive owner
  `Module.HasLengthFiniteFreeResolution`;
- primitive vs. derived:
  primitive data are finite generation in length `0` and, in the successor step, a surjective map
  from some finite free `R`-module onto `M`;
  derived API is the successor unpacking theorem and the pseudo-coherence characterizations below.

The local cover wrapper added no mathematical content beyond the canonical finite-generation owner
and the raw finite-free-surjection data needed for the recursive step, so it should be deleted
rather than preserved as a parallel public API.
-/

/-- `M` has a length-`n` finite free resolution if one can recursively resolve the kernel of a
surjection from a finite free module onto `M` for `n` steps. For `n = 0`, this is just finite
generation of `M`. -/
def HasLengthFiniteFreeResolution
    (R : Type u) [Ring R] (M : Type w) [AddCommGroup M] [Module R M] : ℕ → Prop
  | 0 => Module.Finite R M
  | n + 1 =>
      ∃ (F : Type w) (_ : AddCommGroup F) (_ : Module R F),
        Module.Free R F ∧ Module.Finite R F ∧
        ∃ f : F →ₗ[R] M, Function.Surjective f ∧
        HasLengthFiniteFreeResolution R (LinearMap.ker f) n

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]

-- Proof sketch: unfold the recursive definition of `HasLengthFiniteFreeResolution` at `n + 1`.
/-- A successor-length finite free resolution is obtained by first taking a finite free cover and
then resolving its kernel for one fewer step. -/
theorem hasLengthFiniteFreeResolution_succ_iff (n : ℕ) :
    HasLengthFiniteFreeResolution R M (n + 1) ↔
      ∃ (F : Type v) (_ : AddCommGroup F) (_ : Module R F),
        Module.Free R F ∧ Module.Finite R F ∧
        ∃ f : F →ₗ[R] M, Function.Surjective f ∧
        HasLengthFiniteFreeResolution R (LinearMap.ker f) n := by
  rfl

end Module

section

variable {R : Type u} [Ring R]

-- Proof sketch: use Lemma `15.65.3` with `m = 0` and the vanishing of the higher cohomology of
-- `M[0]` for the forward implication; for the reverse implication, a surjection from a finite free
-- module onto `M` gives the required bounded finite free approximation concentrated in degree `0`.
/-- Lemma 15.65.4 (1): an `R`-module is `0`-pseudo-coherent exactly when it is finite. -/
theorem moduleCat_isZeroPseudoCoherent_iff_finite
    (M : ModuleCat R) :
    M.IsMPseudoCoherent 0 ↔ Module.Finite R M := sorry

-- Proof sketch: if `M` is `(-1)`-pseudo-coherent, combine part `(1)` with Lemma `15.65.2` for the
-- kernel of a finite free cover to prove finite presentation; conversely, a finite presentation is
-- a length-one finite free resolution and hence a `(-1)`-pseudo-coherent approximation.
/-- Lemma 15.65.4 (2): an `R`-module is `(-1)`-pseudo-coherent exactly when it is finitely
presented. -/
theorem moduleCat_isMinusOnePseudoCoherent_iff_finitePresentation
    (M : ModuleCat R) :
    M.IsMPseudoCoherent (-1) ↔ Module.FinitePresentation R M := sorry

-- Proof sketch: argue by induction on `d`. The cases `d = 0` and `d = 1` are parts `(1)` and
-- `(2)`. For the inductive step, peel off a finite free cover of `M`, apply Lemma `15.65.2` to the
-- kernel, and translate the recursive kernel condition using `Module.HasLengthFiniteFreeResolution`.
/-- Lemma 15.65.4 (3): for `d : ℕ`, an `R`-module is `(-d)`-pseudo-coherent exactly when it admits
a length-`d` finite free resolution. -/
theorem moduleCat_isNegPseudoCoherent_iff_hasFiniteFreeResolutionLength
    (M : ModuleCat R) (d : ℕ) :
    M.IsMPseudoCoherent (-(d : ℤ)) ↔ Module.HasLengthFiniteFreeResolution R M d := sorry

-- Proof sketch: an infinite finite free resolution gives `(-d)`-pseudo-coherence for every `d` by
-- truncation. Conversely, recursively choose the finite free covers supplied by part `(3)` for all
-- lengths to assemble an exact infinite resolution by finite free modules.
/-- Lemma 15.65.4 (4): an `R`-module is pseudo-coherent exactly when it admits an infinite
resolution by finite free `R`-modules. -/
theorem moduleCat_isPseudoCoherent_iff_exists_infiniteFiniteFreeResolution
    (M : ModuleCat R) :
    M.IsPseudoCoherent ↔
      ∃ (F : ChainComplex (ModuleCat R) ℕ)
        (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M),
        ChainComplex.IsFiniteFreeResolution π := sorry

end
