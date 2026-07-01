import Mathlib
import stacks_project.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open CategoryTheory.Abelian
open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

/- Domain triage:
* primary domain: local commutative algebra of module depth and residue-field Ext groups;
* sampled owner declarations of the same kind: `Ideal.depth`, the chapter-local bridge
  `moduleDepth`, and `Abelian.Ext` on `ModuleCat`;
* best owner abstraction: `Ideal.depth`, with `moduleDepth R M` as the canonical local bridge for
  the main theorem surface, while `Abelian.Ext` is the owner of the residue-field `Ext` groups
  whose first nonvanishing degree is the source-facing content here;
* layer: `moduleDepth` remains the owner-facing bridge reused downstream, while the least
  nonvanishing residue-field `Ext` degree is source-facing derived data in this file.
* primitive vs derived split: the primitive data here are the groups `Ext^i_R(k, M)` themselves;
  nonvanishing in degree `i` and the first such degree are derived API and should be built from
  that owner rather than encoded by repeated raw existential statements.
-/

/-- The residue-field `Ext` group `Ext^i_R(ResidueField R, M)`. -/
abbrev residueFieldExt (i : ℕ) :=
  Abelian.Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R M) i

/-- Degree `i` is the first kind of datum used in this file: `Ext^i_R(ResidueField R, M)` is
nonzero. -/
def residueFieldExtNonzero (i : ℕ) : Prop :=
  ∃ e : residueFieldExt R M i, e ≠ 0

/-- Some residue-field Ext group of a nonzero finite module over a Noetherian local ring is
nonzero. -/
-- Proof sketch: argue by induction on `moduleDepth M`. In depth `0`, use the characterization by
-- the maximal ideal being associated to `M`, which identifies `Hom_R(ResidueField R, M)` as
-- nonzero. For positive depth, choose a nonzerodivisor `x ∈ maximalIdeal R`, compare the long
-- exact Ext sequence for `0 → M --x→ M → M / xM → 0`, and use that multiplication by `x` acts by
-- zero on these Ext groups to shift the first nonvanishing degree down by one.
theorem exists_nonzero_residueFieldExt :
    ∃ i : ℕ, residueFieldExtNonzero R M i :=
  sorry

/-- The least index for which `Ext^i_R(ResidueField R, M)` is nonzero. -/
noncomputable def firstNonzeroResidueFieldExtIndex : ℕ :=
  let _ : DecidablePred (residueFieldExtNonzero R M) := Classical.decPred _
  Nat.find <| exists_nonzero_residueFieldExt R M

/-- The first nonvanishing residue-field Ext group of `M` is nonzero in the defining degree. -/
-- Proof sketch: this is the defining property of `Nat.find` applied to
-- `exists_nonzero_residueFieldExt`.
theorem firstNonzeroResidueFieldExtIndex_spec :
    residueFieldExtNonzero R M (firstNonzeroResidueFieldExtIndex R M) := sorry

-- Proof sketch: let `i(M)` be `firstNonzeroResidueFieldExtIndex M`. When `moduleDepth M = 0`, the
-- zeroth Ext group is `Hom_R(ResidueField R, M)`, and its nonvanishing is equivalent to
-- `maximalIdeal R ∈ associatedPrimes R M`. For positive depth, choose a nonzerodivisor
-- `x ∈ maximalIdeal R`, apply the long exact Ext sequence for `0 → M --x→ M → M / xM → 0`, use
-- that `x` acts trivially on residue-field Ext groups, deduce `i(M / xM) = i(M) - 1`, and combine
-- this with the depth drop `moduleDepth (M / xM) = moduleDepth M - 1`.
/-- Lemma 10.72.5: for a nonzero finite module `M` over a Noetherian local ring `R`, the depth of
`M` is the least integer `i` such that `Ext^i_R(ResidueField R, M)` is nonzero. -/
theorem moduleDepth_eq_firstNonzeroResidueFieldExtIndex :
    moduleDepth R M = (firstNonzeroResidueFieldExtIndex R M : WithTop ℕ) := sorry

end
