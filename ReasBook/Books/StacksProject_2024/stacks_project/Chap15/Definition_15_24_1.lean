import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {M : Type v} [CommSemiring A] [AddCommMonoid M] [Module A M]

/- Domain triage:
- primary domain: commutative semiring algebra of ideals acting on modules, organized by least
  ideals in the ideal lattice;
- sampled owner declarations of the same kind:
  `IsLeast`,
  `Submodule.mem_smul_top_iff`,
  `Ideal.FG`,
  `Ideal.span`;
- best owner abstraction: the source-facing predicate `IsContentIdeal x I`, defined as the
  `IsLeast` witness for ideals `J` with `x ∈ J • ⊤`;
- primitive data: the element `x : M` and the ideal `I : Ideal A`;
- derived API: the generic `IsLeast` reformulation and the expanded minimality criterion used by
  the direct downstream 15.24 lemmas.

Layering:
- `source-facing`: the textbook notion “`I` is the content ideal of `x`”;
- `core/canonical`: `IsLeast` on the ideal lattice;
- no separate `bridge/view` owner is needed here.
-/

/-- Definition 15.24.1: an ideal `I` is a content ideal of `x` if it is the smallest ideal of `A`
whose product with `M` contains `x`. -/
def IsContentIdeal (x : M) (I : Ideal A) : Prop :=
  IsLeast { J : Ideal A | x ∈ J • (⊤ : Submodule A M) } I

namespace IsContentIdeal

/-- If `I` is a content ideal of `x`, then `x ∈ IM`. -/
theorem mem_smul_top {x : M} {I : Ideal A} (hI : IsContentIdeal x I) :
    x ∈ I • (⊤ : Submodule A M) :=
  hI.1

/-- If `I` is a content ideal of `x`, then every ideal `J` with `x ∈ JM` contains `I`. -/
theorem le {x : M} {I J : Ideal A} (hI : IsContentIdeal x I)
    (hx : x ∈ J • (⊤ : Submodule A M)) : I ≤ J :=
  hI.2 hx

end IsContentIdeal

end
