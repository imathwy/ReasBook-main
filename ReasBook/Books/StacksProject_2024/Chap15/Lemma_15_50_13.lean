import Mathlib
import stacks_project.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A]

variable [HenselianLocalRing A]

/- Domain-style sampling:
- primary domain: henselian local rings, `G`-rings, and filtered direct limits in commutative
  algebra;
- sampled owner declarations:
  `HenselianLocalRing`,
  `IsGRing`,
  `Ring.DirectLimit`,
  `directedSystem_directLimit_henselianLocalRing`;
- best owner abstraction: the stagewise notions are already owned canonically by
  `HenselianLocalRing`, `IsGRing`, `IsLocalHom`, and `Ring.DirectLimit`; there is no reusable
  chapter owner for the full filtered-colimit presentation, so the source-facing item should be
  the explicit existential theorem rather than a one-off wrapper `Prop`;
- primitive data: the filtered index type, stage rings, transition maps, their local-hom
  property, and the direct-limit comparison isomorphism to `A`;
- derived API: henselianity of the direct limit is already owned upstream by
  `directedSystem_directLimit_henselianLocalRing`.

Source/core/bridge triage:
- `source-facing`: `exists_filtered_colimit_of_henselian_local_grings`;
- `core/canonical`: `HenselianLocalRing`, `IsGRing`, `IsLocalHom`, and `Ring.DirectLimit`;
- `bridge/view`: the chosen filtered diagram and comparison isomorphism presenting `A` as that
  direct limit.
-/

-- Proof sketch: write `A` as a filtered colimit of finite type `ℤ`-algebras, localize each stage
-- at the prime lying under the maximal ideal of `A`, and use Proposition `15.50.12` to make those
-- localized stages into local `G`-rings. Lemma `15.12.5` identifies the henselization of `A` with
-- the filtered colimit of the henselizations of the stages, and Lemma `15.50.8` shows those
-- henselizations are again `G`-rings.
/-- Lemma 15.50.13: a henselian local ring is a filtered colimit of a directed system of henselian
local `G`-rings with local transition maps. -/
theorem exists_filtered_colimit_of_henselian_local_grings :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirectedOrder ι)
      (stage : ι → Type u) (_ : ∀ i : ι, CommRing (stage i))
      (_ : ∀ i : ι, HenselianLocalRing (stage i))
      (_ : ∀ i : ι, IsGRing (stage i))
      (map : ∀ i j : ι, i ≤ j → stage i →+* stage j)
      (_ : DirectedSystem stage (fun i j hij ↦ map i j hij))
      (e : Ring.DirectLimit stage (fun i j hij ↦ map i j hij) ≃+* A),
      ∀ i j (hij : i ≤ j), IsLocalHom (map i j hij) := by
  sorry

end
