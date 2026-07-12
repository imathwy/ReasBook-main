import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
variable [AddCommGroup M] [Module R M]

/-- An `R`-module is finite projective if it is both finite and projective. -/
def Module.FiniteProjective (R : Type u) (M : Type w) [CommRing R] [AddCommMonoid M] [Module R M] :
    Prop :=
  Module.Finite R M ∧ Module.Projective R M

-- Proof sketch: the forward implication uses base change for finite and projective modules, namely
-- `Module.Finite.base_change` and the canonical owner instance `Projective.tensorProduct`. For the
-- converse, a flat local homomorphism is faithfully flat by
-- `Module.FaithfullyFlat.of_flat_of_isLocalHom`, and the canonical descent theorems recover
-- finiteness and flatness of `M` from the base change `S ⊗[R] M`. Over the local ring `R`,
-- finite flat modules are free, hence projective.
omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S] in
/-- Helper for Lemma 10.78.6: finite projective modules remain finite projective after base
change. -/
lemma finite_projective_tensorProduct (hM : Module.FiniteProjective R M) :
    Module.FiniteProjective S (S ⊗[R] M) := by
  rcases hM with ⟨hfinite, hprojective⟩
  let _ : Module.Finite R M := hfinite
  let _ : Module.Projective R M := hprojective
  -- Base change preserves both finite generation and projectivity.
  exact ⟨Module.Finite.base_change (R := R) (A := S) (M := M), inferInstance⟩

/-- Helper for Lemma 10.78.6: if the base change is finite projective over `S`, then faithful
flat descent recovers finiteness and flatness over `R`. -/
lemma finite_and_flat_of_finite_projective_tensor_of_flat_localHom
    (hM : Module.FiniteProjective S (S ⊗[R] M)) :
    Module.Finite R M ∧ Module.Flat R M := by
  let _ : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rcases hM with ⟨hfinite, hprojective⟩
  let _ : Module.Finite S (S ⊗[R] M) := hfinite
  let _ : Module.Projective S (S ⊗[R] M) := hprojective
  let _ : Module.Flat S (S ⊗[R] M) := Module.Flat.of_projective
  -- Descend finiteness and flatness separately along the faithfully flat local map.
  exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S,
    Module.Flat.of_flat_tensorProduct (R := R) (M := M) S⟩

/-- Helper for Lemma 10.78.6: over a local ring, a finite flat module is finite projective. -/
lemma finite_projective_of_finite_flat_local (hfinite : Module.Finite R M) (hflat : Module.Flat R M) :
    Module.FiniteProjective R M := by
  let _ : Module.Finite R M := hfinite
  let _ : Module.Flat R M := hflat
  let _ : Module.Free R M := Module.free_of_flat_of_isLocalRing
  -- Over a local ring, finite flat modules are free, so projectivity follows from freeness.
  exact ⟨hfinite, Module.Projective.of_free⟩

/-- Lemma 10.78.6: for a flat local homomorphism `R → S` of local rings and an `R`-module `M`,
`M` is finite projective over `R` if and only if the base-change `S ⊗[R] M` is finite projective
over `S`. -/
@[stacks 00O1]
theorem finite_projective_iff_finite_projective_tensor_of_flat_localHom :
    Module.FiniteProjective R M ↔ Module.FiniteProjective S (S ⊗[R] M) := by
  constructor
  · intro hM
    -- The easy direction is base change of a finite projective module.
    exact finite_projective_tensorProduct (R := R) (S := S) (M := M) hM
  · intro hMS
    -- First descend finiteness and flatness, then use the local criterion for finite projectives.
    rcases
        finite_and_flat_of_finite_projective_tensor_of_flat_localHom
          (R := R) (S := S) (M := M) hMS with
      ⟨hfinite, hflat⟩
    exact finite_projective_of_finite_flat_local (R := R) (M := M) hfinite hflat

end
