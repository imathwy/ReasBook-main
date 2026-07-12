import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/- Domain triage:
* primary domain: valuation subrings of fields and algebraic field extensions;
* core/canonical owners: `ValuationSubring.comap`, `ValuationSubring.mem_comap`,
  `Algebra.IsIntegral.of_injective`, and `isField_of_isIntegral_of_isField'`;
* sampled owner-side declarations: the previous item `Lemma 10.50.7` already recalls
  `ValuationSubring.comap`, while mathlib provides the field criterion
  `isField_of_isIntegral_of_isField'` and the transport lemma
  `Algebra.IsIntegral.of_injective`;
* layer: `source-facing`, since the statement is the Stacks-project consequence for the contracted
  valuation subring, proved by composing those owner abstractions.

Primitive-vs-derived split:
* primitive data: the valuation subring `B : ValuationSubring L` and the algebraic extension
  hypothesis `[Algebra.IsAlgebraic K L]`;
* derived API: the contracted valuation subring `B.comap (algebraMap K L)`, the induced
  `K`-algebra structure on `B` once the contraction is all of `K`, and the resulting integrality
  of `B` over `K`.
-/

-- Proof sketch: if the contraction `B.comap (algebraMap K L)` were a field, then the valuation
-- condition plus inverse-closure would force it to contain all of `K`. Thus `B` becomes a
-- `K`-algebra, algebraic hence integral over `K`, so the domain `B` is itself a field.
/-- Lemma 10.50.8: if `L / K` is algebraic and `B` is a valuation subring of `L` that is not a
field, then the canonical pullback valuation subring `B.comap (algebraMap K L)` of `K`, i.e. the
intersection `K ∩ B`, is not a field. -/
@[stacks 0AAV]
theorem not_isField_comap_algebraMap_of_isAlgebraic [Algebra.IsAlgebraic K L]
    (B : ValuationSubring L) (hB : ¬ IsField B) :
    ¬ IsField (B.comap (algebraMap K L)) := by
  intro hcomap
  let A : ValuationSubring K := B.comap (algebraMap K L)
  have hA : IsField A := by simpa [A] using hcomap
  have hA_mem : ∀ k : K, k ∈ A := by
    intro k
    rcases A.mem_or_inv_mem k with hk | hk
    · exact hk
    · letI := hA.toField
      have hk' : (k⁻¹)⁻¹ ∈ A := by
        have hcoe : (((⟨k⁻¹, hk⟩ : A)⁻¹ : A) : K) = (k⁻¹)⁻¹ := by
          change A.subtype ((⟨k⁻¹, hk⟩ : A)⁻¹) = (A.subtype ⟨k⁻¹, hk⟩)⁻¹
          exact map_inv₀ A.subtype (⟨k⁻¹, hk⟩ : A)
        exact hcoe ▸ ((⟨k⁻¹, hk⟩ : A)⁻¹).2
      simpa using hk'
  letI : Algebra K B :=
    (RingHom.codRestrict (algebraMap K L) B fun k ↦
      show algebraMap K L k ∈ B from hA_mem k).toAlgebra
  haveI : Algebra.IsIntegral K L := ⟨fun x ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩
  let g : B →ₐ[K] L :=
    { toRingHom := B.subtype
      commutes' := fun _ ↦ rfl }
  haveI : Algebra.IsIntegral K B := Algebra.IsIntegral.of_injective g B.subtype_injective
  exact hB <| isField_of_isIntegral_of_isField' (Field.toIsField K)

end
