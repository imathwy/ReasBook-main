import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Ideal
open Ideal.Quotient

section

variable {R : Type u} [CommRing R] (I : Ideal R)

-- Proof sketch: an element of the kernel maps to `0` in `R ⧸ I`, so for every `y` the image of
-- `x * y + 1` is `1`; clause (1) then lifts this unit back to the completion, which is exactly the
-- Jacobson-radical criterion `Ideal.mem_jacobson_bot`.
/-- Lemma 10.96.6 (5): the kernel of the canonical projection `R^∧ → R ⧸ I` is contained in the
Jacobson radical of the `I`-adic completion. -/
theorem ker_evalOneₐ_le_jacobson :
    RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom ≤
      Ideal.jacobson (⊥ : Ideal (AdicCompletion I R)) := sorry

private theorem evalOneₐ_isLocalHom :
    IsLocalHom (AdicCompletion.evalOneₐ I).toRingHom := by
  let e := (Ideal.quotientKerAlgEquivOfSurjective
    (AdicCompletion.evalOneₐ_surjective I)).toRingEquiv
  have hmk : IsLocalHom (Ideal.Quotient.mk (RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom)) :=
    isLocalHom_of_le_jacobson_bot _ (ker_evalOneₐ_le_jacobson I)
  have he : IsLocalHom e.toRingHom :=
    isLocalHom_of_leftInverse e.symm.toRingHom e.left_inv
  have hcomp :
      e.toRingHom.comp (Ideal.Quotient.mk (RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom)) =
        (AdicCompletion.evalOneₐ I).toRingHom := by
    ext x
    exact
      Ideal.quotientKerAlgEquivOfSurjective_mk (AdicCompletion.evalOneₐ_surjective I) x
  have hlocal :
      IsLocalHom
        (e.toRingHom.comp (Ideal.Quotient.mk (RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom))) := by
    refine ⟨fun a ha ↦ ?_⟩
    exact hmk.map_nonunit a
      (he.map_nonunit
        ((Ideal.Quotient.mk (RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom)) a) ha)
  exact hcomp ▸ hlocal

-- Proof sketch: identify `R^∧` with the canonical `I`-adic completion `AdicCompletion I R`. If the
-- image of `x` in `R ⧸ I` is a unit, then the projection `R^∧ → R ⧸ I` is a local hom because its
-- kernel lies in the Jacobson radical; units therefore lift back to units in the completion.
/-- Lemma 10.96.6 (1): an element of the `I`-adic completion whose image in `R ⧸ I` is a unit is
already a unit in the completion. -/
theorem isUnit_of_isUnit_evalOneₐ (x : AdicCompletion I R)
    (hx : IsUnit (AdicCompletion.evalOneₐ I x)) : IsUnit x := by
  let φ : AdicCompletion I R →+* R ⧸ I := (AdicCompletion.evalOneₐ I).toRingHom
  let _ : IsLocalHom φ := evalOneₐ_isLocalHom I
  change IsUnit (φ x) at hx
  exact IsLocalHom.map_nonunit x hx

-- Proof sketch: the image of `I` in the completion is sent to `0` by `R^∧ → R ⧸ I`, so it is
-- contained in the kernel; clause (5) then places it in the Jacobson radical.
/-- Lemma 10.96.6 (4): the extended ideal `I R^∧` is contained in the Jacobson radical of the
`I`-adic completion. -/
theorem completion_ideal_le_jacobson :
    Ideal.map (algebraMap R (AdicCompletion I R)) I ≤
      Ideal.jacobson (⊥ : Ideal (AdicCompletion I R)) := by
  refine le_trans ?_ (ker_evalOneₐ_le_jacobson I)
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change algebraMap R (AdicCompletion I R) x ∈ RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom
  rw [RingHom.mem_ker]
  simpa using (eq_zero_iff_mem.mpr hx)

-- Proof sketch: if `x - 1` lies in the extended ideal `I R^∧`, then clause (4) puts that
-- difference in the Jacobson radical of the completion, and `1 +` an element of the Jacobson
-- radical is invertible.
/-- Lemma 10.96.6 (3): every element of the `I`-adic completion congruent to `1` modulo the
extended ideal `I R^∧` is a unit. -/
theorem isUnit_of_sub_one_mem_completion_ideal (x : AdicCompletion I R)
    (hx : x - 1 ∈ Ideal.map (algebraMap R (AdicCompletion I R)) I) : IsUnit x := by
  exact Ideal.isUnit_of_sub_one_mem_jacobson_bot x ((completion_ideal_le_jacobson I) hx)

-- Proof sketch: if `x - 1 ∈ I`, then its image in the completion differs from `1` by an element
-- of the extended ideal `I R^∧`; apply the Jacobson-radical containment from clauses (4) and (5)
-- together with `Ideal.isUnit_of_sub_one_mem_jacobson_bot`.
/-- Lemma 10.96.6 (2): an element of `R` congruent to `1` modulo `I` maps to a unit in the
`I`-adic completion. -/
theorem isUnit_algebraMap_of_sub_one_mem (x : R) (hx : x - 1 ∈ I) :
    IsUnit (algebraMap R (AdicCompletion I R) x) := by
  refine isUnit_of_sub_one_mem_completion_ideal I (algebraMap R (AdicCompletion I R) x) ?_
  simpa [map_sub, map_one] using
    Ideal.mem_map_of_mem (algebraMap R (AdicCompletion I R)) hx

end
