import LinearRepresentations_Serre_1977.Serre.Chap04.Definition_4_43

-- Theorem 4-44 keeps the textbook coinduced function model as its source-facing predicate,
-- and adds the finite-index bridge to the canonical owner `Representation.ind H.subtype θ`.

noncomputable section

universe u v

namespace Representation

section

variable {G : Type u} [Group G]
variable (H : Subgroup G)
variable {W : Type (max u v)} [AddCommGroup W] [Module ℂ W]
variable (θ : Representation ℂ H W)
variable {V : Type (max u v)} [AddCommGroup V] [Module ℂ V]

/-- A `G`-representation is induced from `(W, θ)` when it is `G`-equivalent to the textbook
function model from Definition 4-43. -/
def IsInducedFrom (ρ : Representation ℂ G V) (H : Subgroup G)
    (θ : Representation ℂ H W) : Prop :=
  Nonempty (ρ.Equiv (Representation.coind H.subtype θ))

/-- The source-facing inducedness predicate is equivalence to the Definition 4-43 function model
`Representation.coind H.subtype θ`. -/
theorem isInducedFrom_iff (ρ : Representation ℂ G V) :
    ρ.IsInducedFrom H θ ↔ Nonempty (ρ.Equiv (Representation.coind H.subtype θ)) :=
  Iff.rfl

/-- For finite index, the Chapter 4 inducedness predicate can be checked against the canonical
owner `Representation.ind H.subtype θ` instead of the coinduced function model. -/
theorem isInducedFrom_iff_nonempty_equiv_ind [H.FiniteIndex] (ρ : Representation ℂ G V) :
    ρ.IsInducedFrom H θ ↔ Nonempty (ρ.Equiv (Representation.ind H.subtype θ)) := by
  classical
  let eIndCoind :
      (Representation.ind H.subtype θ).Equiv (Representation.coind H.subtype θ) :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of θ))
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans eIndCoind.symm⟩
  · rintro ⟨e⟩
    exact ⟨e.trans eIndCoind⟩

/-- The canonical induced representation already satisfies the source-facing inducedness predicate.
-/
theorem isInducedFrom_ind [H.FiniteIndex] :
    (Representation.ind H.subtype θ).IsInducedFrom H θ := by
  exact
    (isInducedFrom_iff_nonempty_equiv_ind H θ (Representation.ind H.subtype θ)).2
      ⟨Representation.Equiv.refl _⟩

/-- Theorem 4-44 (1): for a finite-index subgroup `H ≤ G`, the canonical induced representation
`Representation.ind H.subtype θ` is induced from `(W, θ)` in the sense of Definition 4-43. -/
theorem inducedRepresentation_exists [H.FiniteIndex] :
    (Representation.ind H.subtype θ).IsInducedFrom H θ :=
  isInducedFrom_ind H θ

/-- Theorem 4-44 (2): any `G`-representation induced from `(W, θ)` is `G`-isomorphic to the
canonical induced representation `Representation.ind H.subtype θ`. Hence `Ind_H^G(W, θ)` is
well-defined up to `G`-isomorphism. -/
theorem inducedRepresentation_unique [H.FiniteIndex] (ρ : Representation ℂ G V)
    (hρ : ρ.IsInducedFrom H θ) :
    Nonempty (ρ.Equiv (Representation.ind H.subtype θ)) :=
  (isInducedFrom_iff_nonempty_equiv_ind H θ ρ).mp hρ

end

end Representation
