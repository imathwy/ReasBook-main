import Mathlib
import Serre.Chap14.Corollary_14_14_4_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open Rep

namespace Representation

namespace FiniteProjectiveGroupAlgebraModule

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-
Domain-style sampling:
* Primary domain: finite-dimensional `k[G]`-representations and finite projective `k[G]`-modules.
* Relevant owner declarations sampled in this domain:
  `FiniteProjectiveGroupAlgebraModule.toFiniteRep`,
  `Rep.homLinearEquiv`,
  `FDRep.forget₂HomLinearEquiv`,
  and Chapter `18`'s pairing theorem
  `intertwining_finrank_eq_projectiveLiftCharacter_pairing`.
* Best owner abstraction: the categorical `FDRep` Hom-space `P.toFiniteRep ⟶ M`.
* Source/core/bridge triage:
  source-facing: Serre's invariant `b[SwG](M)`;
  core/canonical: `Module.finrank k (P.toFiniteRep ⟶ M)`;
  bridge/view: the canonical linear equivalence between that Hom-space and the representation-level
    intertwining space `P.toRep.ρ.IntertwiningMap (FDRep.ρ M)`.
* Primitive data: the objects `P.toFiniteRep` and `M` of `FDRep k G`.
* Derived API: the intertwining-space comparison theorem and the notation `b[SwG](M)`.
-/

/-- Definition 19-19.3-1: the core/canonical owner for Serre's invariant is the multiplicity of a
finite-dimensional `k[G]`-module `M` in a finite projective `k[G]`-module `P`, measured by the
`k`-dimension of the equivariant Hom-space `Hom^G(P, M)`. -/
abbrev intertwiningMultiplicity
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) : ℕ :=
  Module.finrank k (P.toFiniteRep ⟶ M)

/-- Helper for Definition 19-19.3-1: intertwining maps of the underlying representations are
canonically the same as morphisms in `FDRep`. -/
private noncomputable abbrev intertwiningMap_linearEquiv_hom
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    P.toRep.ρ.IntertwiningMap (FDRep.ρ M) ≃ₗ[k] (P.toFiniteRep ⟶ M) :=
  ((homLinearEquiv
      ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep)
      ((forget₂ (FDRep k G) (Rep k G)).obj M)).symm).trans
    (FDRep.forget₂HomLinearEquiv P.toFiniteRep M)

/-- Helper for Definition 19-19.3-1: the `FDRep` Hom-space and the representation-level
intertwining space have the same `k`-dimension. This is the form used by Chapter `18`'s
character-pairing formulas. -/
private theorem hom_finrank_eq_finrank_intertwiningMap
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    Module.finrank k (P.toFiniteRep ⟶ M) =
      Module.finrank k (P.toRep.ρ.IntertwiningMap (FDRep.ρ M)) := by
  -- Transport the dimension across the canonical comparison equivalence.
  simpa using (intertwiningMap_linearEquiv_hom (P := P) (M := M)).finrank_eq.symm

/-- Helper for Definition 19-19.3-1: the `FDRep` Hom-space and the representation-level
intertwining space have the same `k`-dimension. This is the form used by Chapter `18`'s
character-pairing formulas. -/
theorem intertwiningMultiplicity_eq_finrank_intertwiningMap
    (P : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    P.intertwiningMultiplicity M =
      Module.finrank k (P.toRep.ρ.IntertwiningMap (FDRep.ρ M)) := by
  -- Route correction: factor the API conversion through a dedicated bridge equivalence so the
  -- dimension transport is a single stable step.
  -- Unfold the owner definition and reuse the finrank comparison lemma.
  simpa [intertwiningMultiplicity] using
    hom_finrank_eq_finrank_intertwiningMap (P := P) (M := M)

scoped[Representation] notation:max "b[" SwG "](" M ")" =>
  FiniteProjectiveGroupAlgebraModule.intertwiningMultiplicity SwG M

open scoped Representation

/-- Helper for Definition 19-19.3-1: the source-facing invariant `b(M)` is the `k`-dimension of
the equivariant Hom-space from the chosen Swan module `SwG` to `M`. -/
theorem swanMultiplicity_eq_finrank_hom
    (SwG : FiniteProjectiveGroupAlgebraModule k G) (M : FDRep k G) :
    b[SwG](M) = Module.finrank k (SwG.toFiniteRep ⟶ M) :=
  rfl

end

end FiniteProjectiveGroupAlgebraModule

end Representation
