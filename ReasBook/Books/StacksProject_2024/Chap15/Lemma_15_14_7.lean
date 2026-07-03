import StacksProject_2024.Chap10.Definition_10_153_1
import StacksProject_2024.Chap15.Definition_15_14_1
import StacksProject_2024.Chap15.Lemma_15_14_3
import Mathlib.RingTheory.Localization.AtPrime.Basic

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

private theorem exists_isRoot_of_residueField_isRoot
    (f : A[X]) (hf : f.Monic)
    {a₀ : ResidueField A} (ha₀ : aeval a₀ f = 0) :
    ∃ a : A, f.IsRoot a ∧ residue A a = a₀ := by
  classical
  have hf_split : f.Splits := IsAbsolutelyIntegrallyClosed.splits f hf
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf_split
  have ha₀_eval : eval a₀ (f.map (residue A)) = 0 := by
    simpa [aeval_def, ResidueField.algebraMap_eq, eval_map] using ha₀
  have hzero : 0 ∈ m.map (fun a ↦ a₀ + residue A a) := by
    rw [← Multiset.prod_eq_zero_iff]
    rw [hm, hf.leadingCoeff, Polynomial.map_mul, eval_mul, Polynomial.map_multiset_prod,
      eval_multiset_prod] at ha₀_eval
    simpa using ha₀_eval
  rw [Multiset.mem_map] at hzero
  obtain ⟨a, ha, ha_zero⟩ := hzero
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

-- Proof sketch: use absolute integral closedness to split every monic polynomial, then any
-- residue-field root of its reduction must come from the image of an actual root by the canonical
-- factorization over the residue field must come from one linear factor already present in the
-- split factorization over `A`. This gives the simple-root lifting clause in
-- `HenselianLocalRing.TFAE`. The residue field is a
-- quotient of an absolutely integrally closed ring, hence algebraically closed and therefore
-- separably closed.
/-- A local absolutely integrally closed ring is strictly henselian. -/
instance : StrictHenselianLocalRing A := by
  refine
    { toHenselianLocalRing := ?_
      toIsSepClosed := ?_ }
  · refine ((HenselianLocalRing.TFAE A).out 1 0).mp ?_
    intro f hf a₀ ha₀ _
    exact exists_isRoot_of_residueField_isRoot f hf ha₀
  · letI : IsAbsolutelyIntegrallyClosed (ResidueField A) := by
      simpa [IsLocalRing.ResidueField] using
        (inferInstance : IsAbsolutelyIntegrallyClosed (A ⧸ maximalIdeal A))
    letI : IsAlgClosed (ResidueField A) := IsAbsolutelyIntegrallyClosed.isAlgClosed
    exact inferInstance

end

-- Proof sketch: apply Lemma `15.14.3` to the localization `Localization.AtPrime p` to keep
-- absolute integral closedness, note that this localization is local, and then invoke the local
-- case to obtain the strict henselian structure.
variable (p : Ideal A) [p.IsPrime] [IsAbsolutelyIntegrallyClosed A]

/- Lemma 15.14.7: if `A` is absolutely integrally closed and `p` is a prime ideal of `A`, then
the local ring `Localization.AtPrime p` is strictly henselian. -/
#synth StrictHenselianLocalRing (Localization.AtPrime p)

end
