import StacksProject_2024.stacks_project.Chap29.Lemma_29_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the scheme-side owner `IsLocallyNoetherian`;
- local Chapter 29 supplies `UniversallyCatenary` and its open-locality bridge in Lemma 29.17.2;
- local Chapter 10 supplies the ring-level owner `UniversallyCatenaryRing`.
-/

variable (S : Scheme.{u})

/-- Lemma 29.17.3: a scheme is universally catenary if and only if every local ring
`\mathcal O_{S, s}` is universally catenary. -/
@[stacks 02JA]
theorem universallyCatenary_iff_forall_stalk_universallyCatenaryRing :
    UniversallyCatenary S ↔ ∀ s : S, UniversallyCatenaryRing (S.presheaf.stalk s) := sorry

/-- On a universally catenary scheme, every stalk is a universally catenary ring. -/
theorem UniversallyCatenary.stalk_universallyCatenaryRing
    (hS : UniversallyCatenary S) (s : S) :
    UniversallyCatenaryRing (S.presheaf.stalk s) :=
  (universallyCatenary_iff_forall_stalk_universallyCatenaryRing S).1 hS s

/-- If every stalk of a scheme is a universally catenary ring, then the scheme is universally
catenary. -/
theorem universallyCatenary_of_forall_stalk_universallyCatenaryRing
    (hS : ∀ s : S, UniversallyCatenaryRing (S.presheaf.stalk s)) :
    UniversallyCatenary S :=
  (universallyCatenary_iff_forall_stalk_universallyCatenaryRing S).2 hS

end AlgebraicGeometry
