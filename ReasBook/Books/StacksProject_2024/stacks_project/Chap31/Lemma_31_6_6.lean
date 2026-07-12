import Mathlib
import StacksProject_2024.Chap30.Definition_30_11_1
import StacksProject_2024.Chap31.Lemma_31_3_1
import StacksProject_2024.Chap31.Lemma_31_5_8
import StacksProject_2024.Chap31.Lemma_31_5_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}
variable (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` pointed to `RingTheory.Sequence.IsRegular`,
-- `RingTheory.Sequence.isRegular_cons_iff`, `IsSMulRegular`, and `QuotSMulTop` for the
-- nonzerodivisor and quotient clauses. Local Chapter 31 precedent fixes the sheaf-side owners as
-- `Scheme.Modules.pushforward`, `weakAss`, `associatedPoints`, `flatOver`, and
-- stalkwise `moduleDepth`.

/-- Lemma 31.6.6 (1): let `f : X → S` be quasi-compact and quasi-separated, let `ℱ` be a
quasi-coherent `𝒪_X`-module, and let `s : S`. If `s` is not in the image of `f`, then `s` is not
weakly associated to `f_*ℱ`. -/
@[stacks 0EY0]
theorem not_mem_weakAss_pushforward_of_not_mem_image
    (s : S) (hs : s ∉ Set.range f.base) :
    s ∉ ((Scheme.Modules.pushforward f).obj ℱ).weakAss := sorry

/-- Lemma 31.6.6 (2): under the same hypotheses, if `s` is not in the image of `f` and the local
ring `𝒪_{S,s}` is Noetherian, then `s` is not associated to `f_*ℱ`. -/
@[stacks 0EY0]
theorem not_mem_associatedPoints_pushforward_of_not_mem_range_of_isNoetherian_stalk
    (s : S) [IsNoetherianRing (S.presheaf.stalk s)]
    (hs : s ∉ Set.range f.base) :
    s ∉ associatedPoints ((Scheme.Modules.pushforward f).obj ℱ) := sorry

/-- Lemma 31.6.6 (3): if `s` is not in the image of `f`, the stalk `(f_*ℱ)_s` is finite over
`𝒪_{S,s}`, and `𝒪_{S,s}` is Noetherian, then `(f_*ℱ)_s` has depth at least `2`. -/
@[stacks 0EY0]
theorem moduleDepth_stalk_pushforward_ge_two_of_not_mem_range_of_finite_of_isNoetherian_stalk
    (s : S) [IsNoetherianRing (S.presheaf.stalk s)]
    [Module.Finite (S.presheaf.stalk s)
      ↑(RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s)]
    (hs : s ∉ Set.range f.base) :
    (2 : ℕ∞) ≤ moduleDepth (S.presheaf.stalk s)
      ↑(RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s) := sorry

/-- Lemma 31.6.6 (4): if `ℱ` is flat over `S` and `a ∈ 𝔪_s` is a nonzerodivisor on
`𝒪_{S,s}`, then `a` is a nonzerodivisor on `(f_*ℱ)_s`. -/
@[stacks 0EY0]
theorem isSMulRegular_stalk_pushforward_of_flat_of_mem_maximalIdeal_of_isSMulRegular
    (hflat : flatOver ℱ f)
    (s : S) (a : S.presheaf.stalk s)
    (ha_mem : a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (ha : IsSMulRegular (S.presheaf.stalk s) a) :
    IsSMulRegular
      ↑(RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s) a := sorry

/-- Lemma 31.6.6 (5): if `ℱ` is flat over `S` and `a, b ∈ 𝔪_s` form a regular sequence in
`𝒪_{S,s}`, then `a` is a nonzerodivisor on `(f_*ℱ)_s`. -/
@[stacks 0EY0]
theorem isSMulRegular_stalk_pushforward_first_of_flat_of_regularSequence_pair
    (hflat : flatOver ℱ f)
    (s : S) (a b : S.presheaf.stalk s)
    (ha_mem : a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (hb_mem : b ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (hab : RingTheory.Sequence.IsRegular (S.presheaf.stalk s) [a, b]) :
    IsSMulRegular
      ↑(RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s) a := sorry

/-- Lemma 31.6.6 (6): if `ℱ` is flat over `S` and `a, b ∈ 𝔪_s` form a regular sequence in
`𝒪_{S,s}`, then `b` is a nonzerodivisor on `(f_*ℱ)_s / a(f_*ℱ)_s`. -/
@[stacks 0EY0]
theorem isSMulRegular_quotSMulTop_stalk_pushforward_second_of_flat_of_regularSequence_pair
    (hflat : flatOver ℱ f)
    (s : S) (a b : S.presheaf.stalk s)
    (ha_mem : a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (hb_mem : b ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (hab : RingTheory.Sequence.IsRegular (S.presheaf.stalk s) [a, b]) :
    IsSMulRegular
      (QuotSMulTop a
        ↑(RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s)) b := sorry

/-- Lemma 31.6.6 (7): if `ℱ` is flat over `S` and `(f_*ℱ)_s` is finite over `𝒪_{S,s}`, then the
depth of `(f_*ℱ)_s` is at least `min (2, depth(𝒪_{S,s}))`. -/
@[stacks 0EY0]
theorem moduleDepth_stalk_pushforward_ge_min_two_ringDepth_of_flat_of_finite
    (hflat : flatOver ℱ f)
    (s : S)
    [Module.Finite (S.presheaf.stalk s)
      ↑(RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s)] :
    min (2 : ℕ∞) (moduleDepth (S.presheaf.stalk s) (S.presheaf.stalk s)) ≤
      moduleDepth (S.presheaf.stalk s)
        ↑(RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) s) := sorry

end AlgebraicGeometry.Scheme.Modules
