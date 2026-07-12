import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/- Domain-style sampling:
- primary domain: directed colimits in commutative local algebra;
- sampled owner declarations:
  `Ring.DirectLimit.of`,
  `Ring.DirectLimit.of_f`,
  `Ring.DirectLimit.exists_of`,
  `IsRegularLocalRing`;
- owner decision:
  `source-facing`: the Stacks Project statement that the directed colimit ring is local, and is
  regular local once it is Noetherian;
  `core/canonical`: `Ring.DirectLimit` as the owner of the colimit ring and its canonical maps;
  `bridge/view`: the stagewise maps `Ring.DirectLimit.of`.

Primitive data are the directed system `(R, φ)` and the stagewise local/regular-local hypotheses.
The direct-limit local-ring structure and the locality of the canonical maps are derived API on
`Ring.DirectLimit`, so this file should expose them on that owner surface rather than through
parallel free-standing wrappers.
-/
variable {I : Type v} [Preorder I]
variable (R : I → Type u) [∀ i, CommRing (R i)]
variable (φ : ∀ i j, i ≤ j → R i →+* R j)

local notation "ρ" => fun i j h ↦ φ i j h
local notation "R∞" => Ring.DirectLimit R ρ

namespace Ring.DirectLimit

section Local

variable [Nonempty I] [IsDirectedOrder I] [DirectedSystem R (φ · · ·)]
variable [∀ i, IsLocalRing (R i)] [∀ i j hij, IsLocalHom (φ i j hij)]

-- Proof sketch: every element of the direct limit comes from some stage. If two elements of the
-- direct limit sum to a unit, represent them in a common stage using directedness; the transition
-- maps are local, so the corresponding sum in that local stage is a unit, forcing one summand to
-- be a unit there and hence in the colimit.
/-- A directed colimit of local rings along local ring maps is again a local ring. -/
theorem isLocalRing : IsLocalRing R∞ := by
  sorry

instance : IsLocalRing R∞ :=
  isLocalRing R φ

-- Proof sketch: if the image of `x : R i` is a unit in the direct limit, represent its inverse in
-- some stage `j`, enlarge to a common upper bound `k`, and check there that the image of `x`
-- becomes a unit. Since `R i → R k` is local, `x` was already a unit in `R i`.
/-- The canonical map from any stage of a directed system of local rings to the direct limit is a
local ring homomorphism. -/
theorem of_isLocalHom (i : I) : IsLocalHom (Ring.DirectLimit.of R ρ i) := by
  sorry

instance (i : I) : IsLocalHom (Ring.DirectLimit.of R ρ i) :=
  of_isLocalHom R φ i

end Local

section Regular

variable [Nonempty I] [IsDirectedOrder I] [DirectedSystem R (φ · · ·)]
variable [∀ i, IsRegularLocalRing (R i)] [∀ i j hij, IsLocalHom (φ i j hij)]
variable [IsNoetherianRing (Ring.DirectLimit R ρ)]

-- Proof sketch: equip the direct limit with the local-ring structure from the previous instance.
-- The regular-local criterion can then be proved by induction on the embedding dimension of the
-- colimit, following the Stacks Project argument: kill an element outside `𝔪²`, use the quotient
-- regularity criterion on sufficiently large stages, and conclude from the nonzerodivisor
-- criterion for regular local rings.
/-- Lemma 10.106.8: if `(R i, φ i j)` is a directed system of regular local rings whose transition
maps are local ring maps, and if the direct limit ring `R∞` is Noetherian, then `R∞` is a regular
local ring. -/
theorem isRegularLocalRing : IsRegularLocalRing (Ring.DirectLimit R ρ) := by
  sorry

instance : IsRegularLocalRing (Ring.DirectLimit R ρ) :=
  isRegularLocalRing R φ

end Regular

end Ring.DirectLimit

end
