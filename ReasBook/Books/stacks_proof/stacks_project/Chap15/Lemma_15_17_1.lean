import Mathlib.Order.Minimal
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 15.17.1: the quotient module `M / JM` carries the natural scalar action of
`R ⧸ J`. -/
instance quotient_smul_top_module (J : Ideal R) :
    Module (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))) where
  smul c m :=
    Quotient.liftOn₂' c m (fun r x ↦ Submodule.Quotient.mk (r • x)) <| by
      intro r₁ x₁ r₂ x₂ hr hx
      rw [Submodule.quotientRel_def] at hr hx
      have hleft : (r₁ - r₂) • x₁ ∈ J • (⊤ : Submodule R M) := by
        exact Submodule.smul_mem_smul hr (by simp)
      have hright : r₂ • (x₁ - x₂) ∈ J • (⊤ : Submodule R M) := by
        exact Submodule.smul_mem (J • (⊤ : Submodule R M)) _ hx
      have hmem : r₁ • x₁ - r₂ • x₂ ∈ J • (⊤ : Submodule R M) := by
        have hEq :
            r₁ • x₁ - r₂ • x₂ = (r₁ - r₂) • x₁ + r₂ • (x₁ - x₂) := by
          calc
            r₁ • x₁ - r₂ • x₂ = (r₁ • x₁ - r₂ • x₁) + (r₂ • x₁ - r₂ • x₂) := by
              abel
            _ = (r₁ - r₂) • x₁ + r₂ • (x₁ - x₂) := by
              rw [sub_smul, smul_sub]
        rw [hEq]
        exact Submodule.add_mem (J • (⊤ : Submodule R M)) hleft hright
      exact (Submodule.Quotient.eq _).2 hmem
  one_smul := by
    rintro ⟨x⟩
    change Submodule.Quotient.mk ((1 : R) • x) = Submodule.Quotient.mk x
    simpa using congrArg (Submodule.Quotient.mk) (one_smul R x)
  mul_smul := by
    rintro ⟨r⟩ ⟨s⟩ ⟨x⟩
    change Submodule.Quotient.mk ((r * s) • x) = Submodule.Quotient.mk (r • (s • x))
    simpa [mul_smul]
  smul_add := by
    rintro ⟨r⟩ ⟨x⟩ ⟨y⟩
    change Submodule.Quotient.mk (r • (x + y)) = Submodule.Quotient.mk (r • x + r • y)
    simpa [smul_add]
  smul_zero := by
    rintro ⟨r⟩
    change Submodule.Quotient.mk (r • (0 : M)) = Submodule.Quotient.mk (0 : M)
    simpa [smul_zero]
  add_smul := by
    rintro ⟨r⟩ ⟨s⟩ ⟨x⟩
    change Submodule.Quotient.mk ((r + s) • x) = Submodule.Quotient.mk (r • x + s • x)
    simpa [add_smul]
  zero_smul := by
    rintro ⟨x⟩
    change Submodule.Quotient.mk ((0 : R) • x) = Submodule.Quotient.mk (0 : M)
    simpa [zero_smul]

/-- Helper for Lemma 15.17.1: an ideal `J` has flat quotient for `M` when `M / JM` is flat over
`R ⧸ J`. -/
abbrev IsFlatQuotient (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Module.Flat (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))

section

variable {I J : Ideal R}

/-- Helper for Lemma 15.17.1: quotient-flat ideals are closed under binary intersections. -/
theorem IsFlatQuotient.inf
    (hI : I.IsFlatQuotient M)
    (hJ : J.IsFlatQuotient M) :
    (I ⊓ J).IsFlatQuotient M := by
  sorry

end

end Ideal

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: commutative algebra of quotient-flatness over quotient rings in the Artinian
  ideal lattice;
- sampled owner declarations of the same kind:
  `Ideal.IsFlatQuotient`,
  `Module.Flat`,
  `Ideal.IsFlatQuotient.inf`,
  `exists_minimal_of_wellFoundedLT`;
- best owner abstraction: the ideal-level predicate recording that `M / JM` is flat over `R / J`;
- primitive data: the ring `R`, the module `M`, and an ideal `J : Ideal R`;
- derived API: the canonical `sInf` least ideal and the source-facing existence corollary.

Layering:
- `source-facing`: the existence of a smallest ideal cutting out a flat quotient of `M`;
- `core/canonical`: `Ideal.IsFlatQuotient` with `Module.Flat` on the canonical quotient ring and
  quotient module, together with the lattice infimum `sInf`;
- `bridge/view`: the existence theorem derived from the canonical `sInf` leastness statement.
-/

/-- Helper for Lemma 15.17.1: the top ideal gives a flat quotient because both quotients are
zero objects. -/
lemma top_isFlatQuotient :
    (⊤ : Ideal R).IsFlatQuotient M := by
  -- At the top ideal, the quotient module is the zero quotient, hence flat by subsingletonity.
  rw [Ideal.IsFlatQuotient]
  let _ : Subsingleton (M ⧸ ((⊤ : Ideal R) • (⊤ : Submodule R M))) :=
    Submodule.Quotient.subsingleton_iff.mpr (Submodule.top_smul (R := R) (N := (⊤ : Submodule R M)))
  infer_instance

/-- Helper for Lemma 15.17.1: the Artinian ideal lattice contains a minimal flat-quotient ideal. -/
lemma exists_minimal_flat_quotient_ideal [IsArtinianRing R] :
    ∃ I : Ideal R, Minimal (fun J : Ideal R ↦ J.IsFlatQuotient M) I := by
  let _ : WellFoundedLT (Ideal R) := inferInstance
  -- The candidate set is nonempty because the top ideal always belongs to it.
  exact exists_minimal_of_wellFoundedLT
    (fun J : Ideal R ↦ J.IsFlatQuotient M) ⟨⊤, top_isFlatQuotient (R := R) (M := M)⟩

/-- Helper for Lemma 15.17.1: minimality upgrades to leastness because flat-quotient ideals are
closed under binary infima. -/
lemma minimal_flat_quotient_ideal_isLeast {I : Ideal R}
    (hI : Minimal (fun J : Ideal R ↦ J.IsFlatQuotient M) I) :
    IsLeast {J : Ideal R | J.IsFlatQuotient M} I := by
  refine ⟨hI.prop, ?_⟩
  intro J hJ
  -- Intersect the minimal witness with any other flat-quotient ideal and use minimality.
  have hInf : (I ⊓ J).IsFlatQuotient M := Ideal.IsFlatQuotient.inf hI.prop hJ
  have hEq : I = I ⊓ J := hI.eq_of_ge hInf inf_le_left
  exact inf_eq_left.mp hEq.symm

variable [IsArtinianRing R]

-- Proof sketch: consider the set of ideals `J` such that `M / JM` is flat over `R ⧸ J`. By
-- Lemma `15.16.1`, this set is closed under finite intersections, and since `R` is Artinian every
-- nonempty collection of ideals has a minimal element. Taking the intersection of all such ideals
-- then gives the smallest one.
/-- The infimum of all flat-quotient ideals is itself the smallest flat-quotient ideal. -/
theorem isLeast_sInf_flat_quotient_ideal :
    IsLeast
      {J : Ideal R | J.IsFlatQuotient M}
      (sInf {J : Ideal R | J.IsFlatQuotient M}) := by
  let S : Set (Ideal R) := {J : Ideal R | J.IsFlatQuotient M}
  change IsLeast S (sInf S)
  -- First choose a minimal flat-quotient ideal using the Artinian descending condition.
  obtain ⟨I, hI⟩ := exists_minimal_flat_quotient_ideal (R := R) (M := M)
  have hLeast : IsLeast S I := minimal_flat_quotient_ideal_isLeast (M := M) hI
  -- Then identify that least witness with the canonical infimum.
  have hsInf : sInf S = I := by
    apply le_antisymm
    · exact sInf_le hLeast.1
    · exact le_sInf hLeast.2
  rw [hsInf]
  exact hLeast

/-- Lemma 15.17.1: over an Artinian ring `R`, there exists a smallest ideal `I` such that
`M / IM` is flat over `R ⧸ I`. -/
@[stacks 0524]
theorem exists_isLeast_flat_quotient_ideal :
    ∃ I : Ideal R,
      IsLeast {J : Ideal R | J.IsFlatQuotient M} I :=
  ⟨_, isLeast_sInf_flat_quotient_ideal⟩

end
