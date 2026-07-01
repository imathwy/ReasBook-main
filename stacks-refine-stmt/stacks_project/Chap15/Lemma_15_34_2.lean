import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

noncomputable section

universe u

namespace Algebra

section

variable {K L M : Type u}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/- Domain triage:
* primary domain: the Jacobi-Zariski sequence for a tower of field extensions `K → L → M`;
* sampled owner declarations:
  - `Algebra.H1Cotangent.exact_map_δ`,
  - `Algebra.H1Cotangent.exact_δ_mapBaseChange`,
  - `KaehlerDifferential.exact_mapBaseChange_map`,
  - `KaehlerDifferential.map_surjective`;
* best owner abstraction: the source-facing sequence is already organized by the canonical owner
  maps `H1Cotangent.map`, `H1Cotangent.δ`, `KaehlerDifferential.mapBaseChange`, and
  `KaehlerDifferential.map`, so the middle exactness and terminal surjectivity belong directly to
  those owners rather than to a new local wrapper;
* primitive data vs. derived API:
  - primitive data: the tower of fields `K → L → M`;
  - derived API: the Jacobi-Zariski exactness/surjectivity on the owner maps, plus the extra
    left-injectivity that is special to the field case;
* layer triage:
  - `source-facing`: Lemma `15.34.2`, namely the same Jacobi-Zariski sequence with zero terms
    adjoined on the left and right;
  - `core/canonical`: the four owner exactness/surjectivity theorems listed above;
  - `bridge/view`: no extra bridge is needed beyond the left-injectivity theorem below.

The old `FieldJacobiZariskiExactSequenceWithZeroEnds` structure duplicated owner declarations
without adding new mathematical data, so this file is refined to direct recall/use of the
canonical owners and one theorem for the genuinely new left edge.
-/

/- Lemma 15.34.2: the middle part
`H₁(L_{M/K}) → H₁(L_{M/L}) → M ⊗[L] Ω[L⁄K]`
is exactly `Algebra.H1Cotangent.exact_map_δ` specialized to the tower `K → L → M`. -/
recall Algebra.H1Cotangent.exact_map_δ

/- Lemma 15.34.2: the next part
`H₁(L_{M/L}) → M ⊗[L] Ω[L⁄K] → Ω[M⁄K]`
is exactly `Algebra.H1Cotangent.exact_δ_mapBaseChange`. -/
recall Algebra.H1Cotangent.exact_δ_mapBaseChange

/- Lemma 15.34.2: the Kähler-differential tail
`M ⊗[L] Ω[L⁄K] → Ω[M⁄K] → Ω[M⁄L]`
is exactly `KaehlerDifferential.exact_mapBaseChange_map`. -/
recall KaehlerDifferential.exact_mapBaseChange_map

/- Lemma 15.34.2: the terminal map `Ω[M⁄K] → Ω[M⁄L]` is the canonical surjective map
`KaehlerDifferential.map_surjective`. -/
recall KaehlerDifferential.map_surjective

-- Proof sketch: combine the left-extended Jacobi-Zariski exact sequence for filtered colimits of
-- local complete intersections with the Stacks result that a field extension is a filtered colimit
-- of global complete intersections. Over a field extension, tensoring with `M` is exact, so the
-- leftmost base-changed map is injective and the whole displayed sequence is exact.
/-- Lemma 15.34.2: for field extensions `M/L/K`, the leftmost map
`H₁(L_{L/K}) ⊗[L] M → H₁(L_{M/K})`
in the Jacobi-Zariski sequence is injective. Together with the recalled canonical exactness and
surjectivity results above, this is the source-facing exact sequence
`0 → H₁(L_{L/K}) ⊗[L] M → H₁(L_{M/K}) → H₁(L_{M/L}) → Ω[L⁄K] ⊗[L] M → Ω[M⁄K] → Ω[M⁄L] → 0`. -/
theorem field_jacobi_zariski_left_injective :
    Function.Injective (LinearMap.liftBaseChange M (H1Cotangent.map K K L M)) := sorry

end

end Algebra
