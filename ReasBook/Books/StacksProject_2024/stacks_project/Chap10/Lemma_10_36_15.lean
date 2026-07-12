import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.36.15 (1): let `A → B → C` be ring maps. If `A → C` is integral, then so is `B → C`.
This is exactly the canonical mathlib theorem `RingHom.IsIntegral.tower_top`. -/
recall RingHom.IsIntegral.tower_top

/- Lemma 10.36.15 (2): let `A → B → C` be ring maps. If `A → C` is finite, then so is `B → C`.
This is exactly the canonical mathlib theorem `RingHom.Finite.of_comp_finite`. -/
recall RingHom.Finite.of_comp_finite
