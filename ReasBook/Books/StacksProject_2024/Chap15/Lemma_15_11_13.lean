import Mathlib.Algebra.Colimit.Ring
import StacksProject_2024.Chap15.Definition_15_11_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Ring.DirectLimit

variable {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
variable (A : J → Type u) [∀ j, CommRing (A j)]
variable (I : ∀ j, Ideal (A j))
variable (f : ∀ j k, j ≤ k → A j →+* A k)

variable [DirectedSystem A (f · · ·)]

/- Domain-style sampling for filtered colimits of henselian pairs:
- primary domain: commutative algebra of henselian pairs under filtered colimits
- inspected same-domain owners/constructions:
  `Ring.DirectLimit`, `Ring.DirectLimit.of`, `HenselianRing`,
  `Ideal.le_ring_jacobson_of_henselianRing`
- best owner abstraction: the ambient colimit pair is expressed directly by the canonical owner
  `HenselianRing (Ring.DirectLimit A (f · · ·)) (⨆ j, Ideal.map (of A (f · · ·) j) (I j))`;
  there is no separate source-facing wrapper here

Source/core/bridge triage:
- `source-facing`: closure of henselian pairs under filtered colimits
- `core/canonical`: the owner class `HenselianRing`
- `bridge/view`: the direct-limit ring together with the supremum ideal coming from the compatible
  stage ideals

Primitive data is the directed system of rings and ideals together with the compatibility maps
`hI`. Since that compatibility is not inferable from the colimit ring and ideal, it belongs as an
explicit input of the public instance header. The henselian structure on the colimit pair is then
derived from that data, so the file should expose the canonical owner instance directly rather than
introducing any presentation wrapper.
-/

local notation "A∞" => Ring.DirectLimit A (f · · ·)
local notation "I∞" => ⨆ j, Ideal.map (of A (f · · ·) j) (I j)

-- Proof sketch: first show that every element of `1 + I∞` comes from some stage and is therefore
-- a unit by the Jacobson-radical condition there, giving the chapter-level containment
-- `I∞ ≤ Ring.jacobson A∞`. Then descend a monic polynomial over `A∞` and a coprime factorization
-- of its reduction modulo `I∞` to a common stage, apply the henselian lifting property in that
-- stage, and map the lifted factorization to the direct limit.
/-- Lemma 15.11.13: filtered colimits of henselian pairs are henselian. More precisely, if the
stage ideals form a directed system of henselian pairs over a directed set, then the supremum of
their images in the ring direct limit is a henselian ideal of the direct limit ring. -/
instance directedSystem_directLimit_henselianRing
    (hI : ∀ ⦃j k⦄ (h : j ≤ k), Ideal.map (f j k h) (I j) ≤ I k)
    [∀ j, HenselianRing (A j) (I j)] :
    HenselianRing A∞ I∞ :=
  sorry

end
