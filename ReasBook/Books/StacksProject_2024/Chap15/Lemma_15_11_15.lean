import StacksProject_2024.Chap15.Lemma_15_11_10
import StacksProject_2024.Chap15.Lemma_15_11_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: closure of henselian ideals in the complete lattice `Ideal A`;
- sampled same-domain owner declarations:
  `HenselianRing`,
  `ideal_add_henselianRing`,
  `directedSystem_directLimit_henselianRing`,
  `Ideal.sSup_eq_iSup`;
- best owner abstraction: the public core object is the canonical supremum ideal
  `sSup {I : Ideal A | HenselianRing A I}`; henselianity and maximality are derived theorems about
  that ideal, not primitive data of a wrapper package.

Source/core/bridge triage:
- `source-facing`: the existence of a largest henselian ideal of `A`;
- `core/canonical`: the owner predicate `HenselianRing A I` on the complete lattice `Ideal A`;
- `bridge/view`: the supremum ideal of all henselian ideals together with its universal upper-bound
  property.

Primitive data is only the ambient ring `A` and the set of ideals carrying the owner predicate
`HenselianRing A`. The largest henselian ideal is therefore a canonical lattice construction, so
the file should expose that ideal directly and keep the existential statement only as a thin
source-facing consequence.
-/

/-- The supremum of all henselian ideals of `A`. -/
def largestHenselianIdeal : Ideal A :=
  sSup {I : Ideal A | HenselianRing A I}

-- Proof sketch: henselian ideals are closed under finite sums by Lemma `15.11.10`, so the set of
-- henselian ideals is directed under inclusion after replacing any pair by their sum. Apply Lemma
-- `15.11.13` to the constant directed system indexed by henselian ideals with identity transition
-- maps. The resulting direct-limit ideal is exactly the supremum of all henselian ideals.
/-- The supremum of all henselian ideals of `A` is henselian. -/
instance largestHenselianIdeal_henselianRing :
    HenselianRing A largestHenselianIdeal := by
  sorry

/-- Every henselian ideal of `A` is contained in the largest henselian ideal. -/
theorem le_largestHenselianIdeal (I : Ideal A) [HenselianRing A I] :
    I ≤ largestHenselianIdeal := by
  exact le_sSup (show HenselianRing A I from inferInstance)

/-- The largest henselian ideal is the greatest henselian ideal of `A`. -/
theorem isGreatest_largestHenselianIdeal :
    IsGreatest {I : Ideal A | HenselianRing A I} largestHenselianIdeal := by
  refine ⟨show HenselianRing A largestHenselianIdeal from inferInstance, ?_⟩
  intro I hI
  let _ : HenselianRing A I := hI
  exact le_largestHenselianIdeal I

/-- Lemma 15.11.15: in a commutative ring `A`, there exists a henselian ideal containing every
henselian ideal of `A`; equivalently, there is a largest ideal `I` such that `(A, I)` is a
henselian pair. -/
theorem exists_largest_henselianIdeal :
    ∃ I : Ideal A, HenselianRing A I ∧ ∀ J : Ideal A, HenselianRing A J → J ≤ I := by
  refine ⟨largestHenselianIdeal, inferInstance, ?_⟩
  intro J hJ
  let _ : HenselianRing A J := hJ
  exact le_largestHenselianIdeal J

end
