import Mathlib
import StacksProject_2024.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open PowerSeries
open IsLocalRing
open scoped RatFunc

universe u

section

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [ExpChar K p] [PerfectRing K p]
variable [Algebra (RatFunc (ZMod p)) K]
variable [IsPerfectClosure (algebraMap (RatFunc (ZMod p)) K) p]

/- Domain-style sampling for Example 15.40.2:
- primary domain: adic formal smoothness of coefficient maps into one-variable power series rings
  over perfect closures in characteristic `p`;
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`,
  * `RingHom.formally_smooth_for_adic_baseChange`,
  * `regularLocalRing_formallySmooth_for_maximalIdeal_adic_tfae_by_characteristic`,
  * `zmod_to_mvPowerSeries_formally_smooth_for_madic`;
- best owner abstraction: the source-facing datum is still the specific ring homomorphism
  `f : RatFunc (ZMod p) →+* PowerSeries K` together with the condition on `f RatFunc.X`, but the
  topology owner on `PowerSeries K` should be the canonical local-ring ideal
  `maximalIdeal (PowerSeries K)` rather than the ad hoc presentation `Ideal.span {X}`;
- primitive data: the perfect-closure field `K`, the ring map `f`, and the equation
  `f RatFunc.X = C(t) + X`;
- derived API: adic formal smoothness of `f` for the one-variable power series target.

Source/core/bridge triage:
- `source-facing`: the Stacks example for the map sending `s` to `t + x`;
- `core/canonical`: `RingHom.formally_smooth_for_adic` and `maximalIdeal (PowerSeries K)`;
- `bridge/view`: the characteristic-`p` formal-smoothness criterion from Theorem `15.40.1`,
  specialized to this explicit map.
-/

-- Proof sketch: apply condition (5) of Theorem `15.40.1` through the differential criterion
-- described in the example. The source field `RatFunc (ZMod p)` has `Ω` free on `dX`, the chosen
-- map sends `X` to `t + x`, and hence `dX` maps to `dx`. Since `Ω[K[[x]]/𝔽_p]` is free on `dx`,
-- the induced map on differentials is injective, giving formal smoothness for the `(x)`-adic
-- topology.
/-- Example 15.40.2: let `k = RatFunc (ZMod p) = 𝔽_p(s)` and let `K` be a perfect closure of `k`,
modeling `𝔽_p(t)^{perf}`. If `f : k →+* K[[x]]`, formalized as
`f : RatFunc (ZMod p) →+* PowerSeries K`, sends the transcendental generator `s = RatFunc.X` to
`t + x`, where `t` is the image of `s` in `K`, then `f` is formally smooth for the `(x)`-adic
topology on `K[[x]]`; since `K` is a field, this is equivalently the
`maximalIdeal (PowerSeries K)`-adic topology. -/
theorem ratFunc_to_powerSeries_shift_formally_smooth_for_xadic
    (f : RatFunc (ZMod p) →+* PowerSeries K)
    (hfX :
      f RatFunc.X = C (algebraMap (RatFunc (ZMod p)) K RatFunc.X) + X) :
    f.formally_smooth_for_adic (maximalIdeal (PowerSeries K)) := sorry

end
