import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

/- Definition 10.153.1: the Stacks notion of a henselian local ring is the canonical mathlib
class `HenselianLocalRing`, characterized by Hensel lifting for simple roots in the residue
field. -/
#check HenselianLocalRing

variable (R : Type u) [CommRing R]

/-- A local ring is strictly henselian if it is henselian and its
residue field is separably algebraically closed. -/
class StrictHenselianLocalRing : Prop extends HenselianLocalRing R, IsSepClosed (ResidueField R)

variable (K : Type u) [Field K] [IsSepClosed K]

-- Proof sketch: a separably closed field is henselian by the canonical field instance, and its
-- residue field identifies with the field itself, so the strict henselian structure is the
-- expected one.
/-- A separably closed field is strictly henselian. -/
instance : StrictHenselianLocalRing K := by
  let e : ResidueField K ≃+* K :=
    (Ideal.quotEquivOfEq ((maximalIdeal K).eq_bot_of_prime)).trans (RingEquiv.quotientBot K)
  refine { toHenselianLocalRing := inferInstance, toIsSepClosed := ?_ }
  refine ⟨fun p hp ↦ ?_⟩
  refine Polynomial.Splits.of_splits_map e.toRingHom ?_ ?_
  · exact IsSepClosed.splits_of_separable (p.map e.toRingHom) hp.map
  · intro a ha
    exact ⟨e.symm a, by simp⟩

end
