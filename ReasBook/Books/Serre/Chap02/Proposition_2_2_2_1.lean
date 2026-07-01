import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

section

variable {k : Type*} [Field k]
variable {G : Type u} [Monoid G]
variable {V1 : Type v} [AddCommGroup V1] [Module k V1]
variable {V2 : Type w} [AddCommGroup V2] [Module k V2]
variable (ρ1 : Representation k G V1) (ρ2 : Representation k G V2)
variable [ρ1.IsIrreducible] [ρ2.IsIrreducible]

-- Source/core/bridge triage:
-- * source-facing: Schur's lemma as Serre states it, namely zero/nonzero and scalar-identity
--   consequences for equivariant maps.
-- * core/canonical: the owner abstraction is `Representation.IntertwiningMap` together with the
--   `Representation.IsIrreducible` API in mathlib.
-- * bridge/view: this file keeps only the thin source-facing consequences of the canonical owner
--   facts, rather than re-packaging irreducibility data locally.

omit [ρ1.IsIrreducible] [ρ2.IsIrreducible] in
/-- Helper for Proposition 2-2.2-1: a bijective intertwining map between two representations
produces an isomorphism of representations. -/
theorem nonempty_equiv_of_bijective_intertwiningMap
    (f : ρ1.IntertwiningMap ρ2) (hf : Function.Bijective f) :
    Nonempty (ρ1.Equiv ρ2) := by
  -- Package the bijective equivariant linear map into the canonical representation equivalence.
  exact ⟨f.ofBijective hf⟩

-- Proof sketch: `Representation.IsIrreducible.bijective_or_eq_zero` says a nonzero intertwiner
-- between irreducibles is bijective, hence an equivalence of representations; the nonisomorphism
-- hypothesis rules out that case.
/-- Proposition 2-2.2-1 (1): an equivariant linear map between two nonisomorphic irreducible
representations over a field is zero. -/
theorem intertwiningMap_eq_zero_of_not_isomorphic
    (f : ρ1.IntertwiningMap ρ2) (hρ : ¬ Nonempty (ρ1.Equiv ρ2)) :
    f = 0 := by
  -- Exclude the bijective branch by converting it into a forbidden representation equivalence.
  simpa using
    (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_left
      (fun hf ↦ hρ <| nonempty_equiv_of_bijective_intertwiningMap (ρ1 := ρ1) (ρ2 := ρ2) f hf)

variable {V : Type v} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)
variable [ρ.IsIrreducible] [FiniteDimensional k V] [IsAlgClosed k]

omit [ρ.IsIrreducible] [FiniteDimensional k V] [IsAlgClosed k] in
/-- Helper for Proposition 2-2.2-1: the scalar coming from the endomorphism-ring `algebraMap`
acts as the same scalar multiple of the identity intertwining map. -/
lemma algebraMap_eq_smul_id (c : k) :
    algebraMap k (ρ.IntertwiningMap ρ) c = c • 1 := by
  -- Identify scalar endomorphisms pointwise with the corresponding homothety.
  simp

-- Proof sketch: use the owner theorem
-- `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`, then rewrite
-- the resulting scalar endomorphism using `Representation.algebraMap_apply`.
/-- Proposition 2-2.2-1 (2): every equivariant endomorphism of an irreducible finite-dimensional
representation over an algebraically closed field is a scalar multiple of the identity
intertwining map. -/
theorem intertwiningMap_eq_smul_id
    (f : ρ.IntertwiningMap ρ) :
    ∃ c : k, f = c • 1 := by
  -- Pull the endomorphism back through the scalar algebra map supplied by Schur's lemma.
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  refine ⟨c, ?_⟩
  -- Rewrite the abstract scalar endomorphism into Serre's source-facing homothety form.
  calc
    f = algebraMap k (ρ.IntertwiningMap ρ) c := hc.symm
    _ = c • 1 := algebraMap_eq_smul_id (ρ := ρ) c

end

end Representation
