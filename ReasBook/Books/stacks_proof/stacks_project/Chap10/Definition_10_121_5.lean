import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Ring.KrullDimLE 1 R]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/- Domain-style sampling:
- primary domain: lattices in a fraction-field vector space over a one-dimensional Noetherian local
  domain and their finite-colength quotients;
- sampled owner declarations: `Submodule.IsLattice`, `Submodule.submoduleOf`, `Module.length`, and
  `Module.length_ne_top_iff`;
- core/canonical owner: latticehood is already owned by `Submodule.IsLattice K`, while the new
  source-facing object here is the integer-valued distance attached to a pair of lattices;
- primitive data: the two submodules `M` and `M'`;
- derived API: the two quotient lengths from the common intersection are derived from those
  submodules, but they are only source-faithful integers in the ambient finite-length regime
  provided by the one-dimensional local-domain hypotheses already used in `10.121.x`.
-/

namespace Submodule

variable (M M' : Submodule R V)
variable [IsLattice K M] [IsLattice K M']

/-- Definition 10.121.5 defines the distance between two lattices `M` and `M'` in a
`K`-vector space `V` as the difference between the colength of `M ∩ M'` in `M` and the
colength of `M ∩ M'` in `M'`, in the one-dimensional Noetherian local-domain fraction-field
setting where these colengths are finite. -/
noncomputable def latticeDistance : ℤ :=
  ((Module.length R (M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
    ((Module.length R (M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ)

omit [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Ring.KrullDimLE 1 R] in
/-- Chap10 Definition 10 121 5: the lattice distance is the difference of the two quotient
colengths from the common intersection. -/
@[stacks 02MG]
lemma latticeDistance_def :
    latticeDistance M M' =
      ((Module.length R (M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
        ((Module.length R (M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ) := by
  -- The definition of `latticeDistance` is exactly the displayed integer difference.
  rfl

end Submodule

end
