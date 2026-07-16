import LinearRepresentations_Serre_1977.Serre.Chap12.Infra_12_7_CyclicDescent

open scoped Representation SubgroupInduction

noncomputable section

universe u v w

namespace Representation

open CategoryTheory

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [IsDomain A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L)
variable [Algebra A K] [IsFractionRing A K]
/- Faithfulness sync (§12.7, cf. Lemma 16 = Lemma_12_12_7_4): Serre's `A = ℤ[μ_m]` is integrally
closed; Lemma 15's cyclic-induction decomposition realizes `K`-valued data inside `A ⊗ R_K(C)`,
which requires `A` integrally closed. -/
variable [IsIntegrallyClosed A]

local notation "ΓK" => Γ[K](G)
local notation "CycSub" => { H : Subgroup G // IsCyclic H }

private local instance : DecidableEq CycSub := Classical.decEq _

/-- Lemma 12-12.7-3: let `Γ_K = Γ[K](G)` be the arithmetic subgroup attached to the intermediate
field `K ⊆ L`. If an `A`-valued function on `G` is constant on `Γ_K`-classes and all of its
values lie in `|G|A`, then its image in `K` is a finite sum of inductions from cyclic subgroups,
with each cyclic summand belonging to `A ⊗ R_K(C)`.

The source text writes this ideal as `gA`, where `g` denotes the order of `G`; it is not an
arbitrary element of `A`. -/
theorem exists_cyclicSubgroup_induction_decomposition
    (f : G → A)
    (hf : IsConstantOnGaloisPowerClasses ΓK f)
    (hfg : ∀ s : G, f s ∈ Ideal.span ({(Nat.card G : A)} : Set A)) :
    (algebraMap A K) ∘ f ∈
      LinearMap.range ((A ⊗R[K](G)).subtype.comp
        (DFinsupp.lsum A fun H : CycSub ↦
          H.1.characterRingOverFieldAlgebraScalarExtensionInduction)) := by
  -- Route correction: this item-level file should reuse the packaged cyclic-descent theorem
  -- rather than rebuilding the cyclic-component decomposition locally.
  -- The Chapter 12 cyclic-descent infrastructure already packages Serre's denominator-clearing
  -- argument with the same hypotheses and target owner map.
  simpa using
    cyclicSubgroupInduction_descent_of_principal_values
      (K := K) (A := A) (L := L) f hf hfg

end

end Representation
