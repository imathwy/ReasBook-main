import Mathlib
import stacks_project.Chap10.Lemma_10_39_9
import stacks_project.Chap10.Lemma_10_126_2
import stacks_project.Chap10.Lemma_10_135_11
import stacks_project.Chap10.Lemma_10_136_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

namespace RingHom

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling:
- primary domain: faithfully flat descent and base change for syntomic ring maps in commutative
  algebra;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `flat_iff_flat_baseChange_of_faithfullyFlat`,
  `finitePresentation_iff_finitePresentation_baseChange_of_faithfullyFlat`,
  `isLocalCompleteIntersection_iff_of_tensorProduct_fieldExtension`;
- best owner abstraction: the public statement belongs on the ring-hom owner
  `RingHom.Syntomic`, with flatness, finite presentation, and local-complete-intersection fibers
  kept as derived component API rather than repackaged local data;
- primitive vs. derived:
  the primitive inputs are only the rings, algebra structures, and the faithfully flat base change
  `R → R'`;
  the forward base-change theorem `syntomic_baseChange`, the flat/finitely-presented descent
  theorems, the choice of a prime `p'` over `p`, and the fiber comparison over residue fields are
  all canonical derived API.

Source/core/bridge triage:
* `source-facing`: the textbook `iff` for syntomicity under faithfully flat base change;
* `core/canonical`: `RingHom.Syntomic`;
* `bridge/view`: `syntomic_baseChange`, the component descent theorems, and the prime-lifting step
  along `PrimeSpectrum.comap`.
-/

-- Proof sketch: unpack `RingHom.Syntomic` into flatness, finite presentation, and local complete
-- intersection fibers. The first two conditions descend and ascend along faithfully flat base
-- change by Lemmas `10.39.9` and `10.126.2`. Since `Spec R' → Spec R` is surjective by Lemma
-- `10.39.16`, the fiberwise condition reduces to comparing `S ⊗[R] κ(p)` with
-- `(R' ⊗[R] S) ⊗[R'] κ(p')`, and Lemma `10.135.11` identifies local complete intersections across
-- that residue-field extension.
/-- Lemma 10.136.2: for a faithfully flat base change `R → R'`, the ring map `R → S` is syntomic
if and only if the base-changed map `R' → R' ⊗[R] S` is syntomic. -/
theorem syntomic_iff_syntomic_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    (algebraMap R S).Syntomic ↔ (algebraMap R' (R' ⊗[R] S)).Syntomic := by
  constructor
  · intro h
    simpa using h.baseChange
  · intro hbase
    letI : Module.FaithfullyFlat R R' :=
      (RingHom.faithfullyFlat_algebraMap_iff : (algebraMap R R').FaithfullyFlat ↔
        Module.FaithfullyFlat R R').mp hff
    letI : Module.Flat R R' := (RingHom.flat_algebraMap_iff).mp hff.flat
    refine ⟨?_, ?_, ?_⟩
    · rw [RingHom.flat_algebraMap_iff]
      letI : Module.Flat R' (R' ⊗[R] S) := (RingHom.flat_algebraMap_iff).mp hbase.flat
      have hflatBase : Module.Flat R (R' ⊗[R] S) := Module.Flat.trans R R' (R' ⊗[R] S)
      exact (flat_iff_flat_baseChange_of_faithfullyFlat).mpr hflatBase
    · have hfpBase : Algebra.FinitePresentation R' (R' ⊗[R] S) := by
        simpa [RingHom.finitePresentation_algebraMap] using hbase.finitePresentation
      rw [RingHom.finitePresentation_algebraMap]
      exact
        (finitePresentation_iff_finitePresentation_baseChange_of_faithfullyFlat hff).mpr hfpBase
    · intro p
      have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R R')) :=
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
      obtain ⟨p', hp'⟩ := hsurj p
      letI : p'.asIdeal.LiesOver p.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hp').symm⟩
      -- The remaining step is the canonical fiber identification
      -- `p'.asIdeal.Fiber (R' ⊗[R] S) ≃ κ(p') ⊗[κ(p)] p.asIdeal.Fiber S`, after which
      -- Lemma `10.135.11` gives the desired descent of the local-complete-intersection fiber
      -- condition.
      sorry

end RingHom

end
