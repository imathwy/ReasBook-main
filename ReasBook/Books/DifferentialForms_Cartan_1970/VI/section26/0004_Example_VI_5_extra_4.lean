import Mathlib
import Mathlib.Tactic.Recall
import cartan.II.section05.«0024_Example_II_1_extra_14»

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this file lies in the topology of covering maps and simple connectedness. The
-- owner abstractions are `IsCoveringMapOn`, `IsConnected`, `IsSimplyConnected`, and
-- `SimplyConnectedSpace`. Item (1) is a direct `core/canonical` recall of mathlib's covering-map
-- theorem for `Complex.exp`, item (3) is a direct reuse of the earlier project theorem for the
-- punctured plane, while items (2) and (4) are derived from the canonical connectedness and
-- contractibility owners rather than from any local wrapper.

/- Example VI.5-extra-4 (1): the exponential map is a covering map on the punctured complex
plane. -/
recall Complex.isCoveringMapOn_exp

/-- Example VI.5-extra-4 (2): the punctured complex plane is connected. -/
example : IsConnected ({0}ᶜ : Set ℂ) := by
  simpa using isConnected_compl_singleton_of_one_lt_rank
    (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) (0 : ℂ)

/- Example VI.5-extra-4 (3): the punctured complex plane is not simply connected. -/
recall punctured_complex_plane_not_isSimplyConnected

/-- Example VI.5-extra-4 (4): the complex plane is simply connected. -/
example : SimplyConnectedSpace ℂ := inferInstance
