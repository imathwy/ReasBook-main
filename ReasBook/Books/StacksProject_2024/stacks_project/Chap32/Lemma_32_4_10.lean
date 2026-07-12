import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)

-- Semantic recall: `lean_leansearch` surfaced `Topology.IsLocallyConstructible` and the scheme
-- finite-presentation image lemmas. Local Chapter 32 precedent fixes Situation `32.4.5` as a
-- directed inverse system `D : OrderDual I ⥤ Scheme` with affine transition morphisms and a limit
-- cone `c`; Lemma `32.4.9` supplies the matching eventual-emptiness mechanism used by the source.

/-- Lemma 32.4.10: in Situation `32.4.5`, let `E ⊆ S_i` be a locally constructible subset of a
stage such that the image of the limit projection `f_i : S ⟶ S_i` is contained in `E`. Then, after
passing to a sufficiently large stage `i₀ ≥ i`, every later transition image
`f_{i',i}(S_{i'})` is contained in `E`. -/
@[stacks 05F4]
theorem exists_eventually_transition_mapsTo_of_isLocallyConstructible
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : OrderDual I} (f : j ⟶ j'), IsAffineHom (D.map f)]
    (hc : IsLimit c) (i : I) (E : Set ↥(D.obj i))
    (hE : IsLocallyConstructible E)
    (hlimit : Set.MapsTo (c.π.app i) Set.univ E) :
    ∃ (i₀ : I) (hii₀ : i ≤ i₀), ∀ ⦃i' : I⦄, (hi₀i' : i₀ ≤ i') →
      Set.MapsTo
        (D.map (homOfLE (show OrderDual.toDual i' ≤ OrderDual.toDual i from
          (show i ≤ i' from le_trans hii₀ hi₀i'))))
        Set.univ E := sorry

end

end AlgebraicGeometry
