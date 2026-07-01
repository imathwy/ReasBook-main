import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct

noncomputable section

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain triage:
- primary domain: the Jacobi-Zariski exact sequence for composable maps of commutative rings;
- sampled owner declarations:
  - `Algebra.H1Cotangent.exact_map_δ`,
  - `Algebra.H1Cotangent.exact_δ_mapBaseChange`,
  - `KaehlerDifferential.exact_mapBaseChange_map`,
  - `KaehlerDifferential.map_surjective`;
- best owner abstraction: the sequence is already organized upstream around the canonical maps
  `H1Cotangent.map`, `H1Cotangent.δ`, `KaehlerDifferential.mapBaseChange`, and
  `KaehlerDifferential.map`, together with the four owner exactness/surjectivity theorems above;
- primitive data: a tower of commutative rings `A → B → C`;
- derived API: the exactness and terminal surjectivity statements for the owner maps;
- layer triage:
  - `source-facing`: the textbook Jacobi-Zariski sequence
    `H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`;
  - `core/canonical`: the four owner theorems recalled below;
  - `bridge/view`: none is needed here, since the source statement adds no extra data beyond the
    canonical owner exactness results.

The local `JacobiZariskiExactSequence` wrapper duplicated this owner API without adding new
mathematics, so the file is refined to direct recall/use of the canonical declarations.
-/

/- Lemma 10.134.4: the first two maps in the Jacobi-Zariski sequence
`H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A]`
are handled upstream by `Algebra.H1Cotangent.exact_map_δ`. -/
recall Algebra.H1Cotangent.exact_map_δ

/- Lemma 10.134.4: the next two maps
`H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A] → Ω[C⁄A]`
are handled upstream by `Algebra.H1Cotangent.exact_δ_mapBaseChange`. -/
recall Algebra.H1Cotangent.exact_δ_mapBaseChange

/- Lemma 10.134.4: the Kähler-differential tail
`C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B]`
is handled upstream by `KaehlerDifferential.exact_mapBaseChange_map`. -/
recall KaehlerDifferential.exact_mapBaseChange_map

/- Lemma 10.134.4: the terminal map `Ω[C⁄A] → Ω[C⁄B]` is the canonical surjective map
`KaehlerDifferential.map_surjective`. -/
recall KaehlerDifferential.map_surjective

end
