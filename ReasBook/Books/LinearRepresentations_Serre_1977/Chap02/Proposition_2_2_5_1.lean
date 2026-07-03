import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Remark_2_2_1_2
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra

noncomputable section

universe u v

namespace Representation

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance fintypeGProp2251 : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: the class-function operator attached to `f`, written in the source as the sum
--   `∑ t, f t · ρ_t`.
-- * core/canonical: the chapter owner `classFunctionSubmodule k G` and the group-algebra action
--   `ρ.asAlgebraHom`.
-- * bridge/view: the canonical group-algebra element `Finsupp.equivFunOnFinite.symm f`, whose
--   expansion by `Finsupp.equivFunOnFinite_symm_eq_sum` recovers the source-facing sum.
--
-- Proof sketch: the class-function hypothesis implies that
-- `ρ.asAlgebraHom (∑ t, f t • MonoidAlgebra.of k G t)` commutes with every `ρ s`, so it is an
-- intertwining endomorphism of the irreducible representation `ρ`. Apply Schur's lemma to
-- conclude that it is scalar, then compare traces to identify the scalar as the normalized
-- character sum.
omit [IsAlgClosed k] in
/-- Helper for Proposition 2-2.5-1: applying the class-function group-algebra element through
`ρ.asAlgebraHom` expands to the source-facing finite sum `∑ t, f t • ρ t`. -/
private theorem asAlgebraHom_classFunction_sum_apply
    (ρ : Representation k G V) (f : classFunctionSubmodule k G) (v : V) :
    (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) v =
      ∑ t : G, f t • ρ t v := by
  -- Expand the group-algebra action term-by-term so later arguments can stay in source notation.
  simp

omit [IsAlgClosed k] in
/-- Helper for Proposition 2-2.5-1: the class-function weighted operator commutes with the
representation action, so it defines an equivariant endomorphism. -/
private theorem asAlgebraHom_classFunction_sum_isIntertwining
    (ρ : Representation k G V) (f : classFunctionSubmodule k G) :
    ρ.IsIntertwiningMap ρ (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) := by
  let hf : IsClassFunction (f : G → k) := (mem_classFunctionSubmodule_iff k _).1 f.2
  rw [isIntertwiningMap_iff]
  intro s v
  -- Rewrite both sides as sums over the same family of operators `ρ t`.
  calc
    (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) (ρ s v)
        = ∑ t : G, f (t * s⁻¹) • ρ t v := by
            calc
              (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) (ρ s v)
                  = ∑ t : G, f t • ρ (t * s) v := by simp [map_mul]
              _ = ∑ t : G, f (t * s⁻¹) • ρ t v := by
                    rw [← Function.Bijective.sum_comp (Group.mulRight_bijective s⁻¹)
                      (fun t : G ↦ f t • ρ (t * s) v)]
                    apply Finset.sum_congr rfl
                    intro t ht
                    simp [mul_assoc]
    _ = ∑ t : G, f (s⁻¹ * t) • ρ t v := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hf.map_mul_comm t s⁻¹]
    _ = ρ s ((ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) v) := by
          symm
          calc
            ρ s ((ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) v)
                = ∑ t : G, f (s⁻¹ * t) • ρ t v := by
                    calc
                      ρ s ((ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) v)
                          = ∑ t : G, f t • ρ (s * t) v := by simp [map_mul]
                      _ = ∑ t : G, f (s⁻¹ * t) • ρ t v := by
                            rw [← Function.Bijective.sum_comp (Group.mulLeft_bijective s⁻¹)
                              (fun t : G ↦ f t • ρ (s * t) v)]
                            apply Finset.sum_congr rfl
                            intro t ht
                            simp

omit [IsAlgClosed k] in
/-- Helper for Proposition 2-2.5-1: the trace of the class-function weighted operator is the
character-weighted coefficient sum. -/
private theorem trace_asAlgebraHom_classFunction_sum
    (ρ : Representation k G V) [FiniteDimensional k V] (f : classFunctionSubmodule k G) :
    LinearMap.trace k V (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)) =
      ∑ t : G, f t * ρ.character t := by
  -- Replace the packaged group-algebra action by the explicit sum of representation maps.
  calc
    LinearMap.trace k V (ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t))
        = LinearMap.trace k V (∑ t : G, f t • ρ t) := by
            congr 1
            simp
    _ = ∑ t : G, f t * ρ.character t := by
          simp [Representation.character, smul_eq_mul]

/-- Proposition 2-2.5-1: if `f` is constant on conjugacy classes and `ρ` is an irreducible
representation of a finite group over an algebraically closed field, and if the scalar
`(dim V : k)` is nonzero, then the source-facing finite sum
`∑ t, f t • MonoidAlgebra.of k G t` acts by the homothety whose ratio is
`(dim V)⁻¹ * ∑ t, f t * ρ.character t`. Finite-dimensionality is derived internally from
irreducibility. -/
theorem asAlgebraHom_classFunction_sum_eq_character_sum_smul_id
    (ρ : Representation k G V) [ρ.IsIrreducible] (f : classFunctionSubmodule k G)
    (hfinrank : (Module.finrank k V : k) ≠ 0) :
    letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
    ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t) =
      ((Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t) • LinearMap.id := by
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
  let T : Module.End k V := ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t)
  let Tinter : ρ.IntertwiningMap ρ :=
    T.intertwiningMap_of_isIntertwiningMap ρ ρ
      (asAlgebraHom_classFunction_sum_isIntertwining (ρ := ρ) f).isIntertwining
  -- Apply Schur's lemma to the equivariant endomorphism coming from the class function.
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective Tinter
  have hscalar :
      T = c • LinearMap.id := by
    -- Convert the scalar intertwining-map identity back to an equality of endomorphisms.
    simpa [T, Tinter, IntertwiningMap.algebraMap_apply] using
      (congrArg IntertwiningMap.toLinearMap hc).symm
  have htrace :
      c * (Module.finrank k V : k) = ∑ t : G, f t * ρ.character t := by
    -- Identify the scalar by comparing the trace of the scalar map with the trace of `T`.
    calc
      c * (Module.finrank k V : k) = LinearMap.trace k V (c • (LinearMap.id : V →ₗ[k] V)) := by
        simp [LinearMap.trace_id, smul_eq_mul]
      _ = LinearMap.trace k V T := by rw [← hscalar]
      _ = ∑ t : G, f t * ρ.character t := by
            simpa [T] using trace_asAlgebraHom_classFunction_sum (ρ := ρ) f
  have hc_eq :
      c = (Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t := by
    -- Cancel the nonzero dimension scalar on the right to solve for `c`.
    apply mul_right_cancel₀ hfinrank
    calc
      c * (Module.finrank k V : k) = ∑ t : G, f t * ρ.character t := htrace
      _ = (((Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t) *
            (Module.finrank k V : k)) := by
              symm
              rw [mul_assoc, mul_comm (∑ t : G, f t * ρ.character t) (Module.finrank k V : k),
                ← mul_assoc, inv_mul_cancel₀ hfinrank, one_mul]
  -- Substitute the trace-computed scalar back into the scalar-endomorphism identity.
  calc
    ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t) = T := rfl
    _ = c • LinearMap.id := hscalar
    _ = ((Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t) • LinearMap.id := by
          rw [hc_eq]

/-- Bridge form of Proposition 2-2.5-1: the canonical group-algebra element
`Finsupp.equivFunOnFinite.symm f` acts by the same homothety, obtained by packaging the
source-facing finite sum. -/
theorem asAlgebraHom_classFunction_eq_character_sum_smul_id
    (ρ : Representation k G V) [ρ.IsIrreducible] (f : classFunctionSubmodule k G)
    (hfinrank : (Module.finrank k V : k) ≠ 0) :
    letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
    ρ.asAlgebraHom (Finsupp.equivFunOnFinite.symm f) =
      ((Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t) • LinearMap.id := by
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
  have hcoeff :
      Finsupp.equivFunOnFinite.symm f = ∑ t : G, f t • MonoidAlgebra.of k G t := by
    simpa [MonoidAlgebra.of] using Finsupp.equivFunOnFinite_symm_eq_sum f
  calc
    ρ.asAlgebraHom (Finsupp.equivFunOnFinite.symm f)
        = ρ.asAlgebraHom (∑ t : G, f t • MonoidAlgebra.of k G t) := by rw [hcoeff]
    _ = ((Module.finrank k V : k)⁻¹ * ∑ t : G, f t * ρ.character t) • LinearMap.id :=
      asAlgebraHom_classFunction_sum_eq_character_sum_smul_id ρ f hfinrank

end

end Representation
