import stacks_proof.stacks_project.Chap10.Definition_10_153_1
import stacks_proof.stacks_project.Chap15.Definition_15_14_1
import stacks_proof.stacks_project.Chap15.Lemma_15_14_3
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open Polynomial

universe u

section

variable {A : Type u} [CommRing A]

section

variable [IsLocalRing A] [IsAbsolutelyIntegrallyClosed A]

/-
Domain-style sampling for Lemma 15.14.7:
- primary domain: local commutative algebra of absolutely integrally closed rings, residue fields,
  and the canonical owners `HenselianLocalRing` and `StrictHenselianLocalRing`;
- sampled owner-level declarations:
  `HenselianLocalRing.TFAE`,
  `StrictHenselianLocalRing`,
  `IsAbsolutelyIntegrallyClosed.exists_root`,
  `Polynomial.Splits.roots_map_of_ne_zero`,
  `Polynomial.mem_roots`,
  `IsAbsolutelyIntegrallyClosed (A ⧸ I)`;
- best owner abstraction: the canonical local owner is `HenselianLocalRing`, upgraded to
  `StrictHenselianLocalRing` by the residue-field separable-closure clause; the source-facing
  localization statement is then derived by the existing absolute-integral-closed localization
  instance together with the local strict henselian owner instance below;
- primitive data: `HenselianLocalRing A` and `IsSepClosed (ResidueField A)`;
- derived API: strict henselianity of localizations at prime ideals.

Source/core/bridge triage:
- `source-facing`: the `#synth` entry for Lemma 15.14.7;
- `core/canonical`: `StrictHenselianLocalRing`, `HenselianLocalRing`, `IsSepClosed`;
- `bridge/view`: the local instance from absolute integral closedness together with the
  quotient/localization preservation instances for `IsAbsolutelyIntegrallyClosed`.
-/
/-- Helper for Lemma 15.14.7: a residue-field root of a monic polynomial lifts to an actual root
of the original polynomial over a local absolutely integrally closed ring. -/
private theorem exists_isRoot_of_residueField_isRoot
    (f : A[X]) (hf : f.Monic)
    {a₀ : ResidueField A} (ha₀ : aeval a₀ f = 0) :
    ∃ a : A, f.IsRoot a ∧ residue A a = a₀ := by
  classical
  -- Split the monic polynomial in `A[X]` so the residue-field root can be read off from a linear
  -- factor after mapping the factorization to the residue field.
  have hf_split : f.Splits := IsAbsolutelyIntegrallyClosed.splits f hf
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf_split
  -- Reinterpret the `aeval` hypothesis as an ordinary evaluation statement on the mapped
  -- polynomial over the residue field.
  have ha₀_eval : eval a₀ (f.map (residue A)) = 0 := by
    simpa [aeval_def, ResidueField.algebraMap_eq, eval_map] using ha₀
  -- The mapped factorization vanishes at `a₀`, so one linear factor must evaluate to zero.
  have hzero : 0 ∈ m.map (fun a ↦ a₀ + residue A a) := by
    rw [← Multiset.prod_eq_zero_iff]
    rw [hm, hf.leadingCoeff, Polynomial.map_mul, eval_mul, Polynomial.map_multiset_prod,
      eval_multiset_prod] at ha₀_eval
    simpa using ha₀_eval
  rw [Multiset.mem_map] at hzero
  obtain ⟨a, ha, ha_zero⟩ := hzero
  -- The zero factor gives the lifted root `-a`, and the same vanishing identity identifies its
  -- residue with the chosen residue-field root.
  refine ⟨-a, ?_, ?_⟩
  · rw [IsRoot, hm, hf.leadingCoeff, eval_mul, eval_C, one_mul, eval_multiset_prod]
    refine Multiset.prod_eq_zero ?_
    have hmem :
        eval (-a) (X + C a) ∈ Multiset.map (eval (-a)) (Multiset.map (fun x ↦ X + C x) m) :=
      Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ ha)
    simpa using hmem
  · calc
      residue A (-a) = -residue A a := by simp
      _ = a₀ := (eq_neg_of_add_eq_zero_left ha_zero).symm

/-- Helper for Lemma 15.14.7: the residue field of a local absolutely integrally closed ring is
absolutely integrally closed because it is the quotient by the maximal ideal. -/
private theorem residue_field_absolutely_integrally_closed :
    IsAbsolutelyIntegrallyClosed (ResidueField A) := by
  -- Pass to the quotient presentation of the residue field and reuse Lemma `15.14.3`.
  simpa [IsLocalRing.ResidueField] using
    (inferInstance : IsAbsolutelyIntegrallyClosed (A ⧸ maximalIdeal A))

-- Proof sketch: use absolute integral closedness to split every monic polynomial, then any
-- residue-field root of its reduction must come from the image of an actual root by the canonical
-- factorization over the residue field must come from one linear factor already present in the
-- split factorization over `A`. This gives the simple-root lifting clause in
-- `HenselianLocalRing.TFAE`. The residue field is a
-- quotient of an absolutely integrally closed ring, hence algebraically closed and therefore
-- separably closed.
/-- A local absolutely integrally closed ring is strictly henselian. -/
instance strictHenselian_of_local_absolutelyIntegrallyClosed : StrictHenselianLocalRing A := by
  refine
    { toHenselianLocalRing := ?_
      toIsSepClosed := ?_ }
  -- The source route uses the simple-root lifting clause in `HenselianLocalRing.TFAE`.
  · refine ((HenselianLocalRing.TFAE A).out 1 0).mp ?_
    intro f hf a₀ ha₀ _
    exact exists_isRoot_of_residueField_isRoot f hf ha₀
  · -- The residue field is a quotient of an absolutely integrally closed ring, hence algebraically
    -- closed and therefore separably closed.
    letI : IsAbsolutelyIntegrallyClosed (ResidueField A) :=
      residue_field_absolutely_integrally_closed (A := A)
    letI : IsAlgClosed (ResidueField A) := IsAbsolutelyIntegrallyClosed.isAlgClosed
    exact inferInstance

end

-- Proof sketch: apply Lemma `15.14.3` to the localization `Localization.AtPrime p` to keep
-- absolute integral closedness, note that this localization is local, and then invoke the local
-- case to obtain the strict henselian structure.
variable (p : Ideal A) [p.IsPrime] [IsAbsolutelyIntegrallyClosed A]

/-- Lemma 15.14.7: the localization of an absolutely integrally closed ring at a prime ideal is
strictly henselian. -/
@[stacks 0DCS]
instance instStrictHenselianLocalRingLocalizationAtPrime :
    StrictHenselianLocalRing (Localization.AtPrime p) :=
  strictHenselian_of_local_absolutelyIntegrallyClosed (A := Localization.AtPrime p)

/- Lemma 15.14.7: if `A` is absolutely integrally closed and `p` is a prime ideal of `A`, then
the local ring `Localization.AtPrime p` is strictly henselian. -/
#synth StrictHenselianLocalRing (Localization.AtPrime p)

end
