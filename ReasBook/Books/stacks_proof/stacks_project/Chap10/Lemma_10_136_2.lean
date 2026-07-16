import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_39_9
import stacks_proof.stacks_project.Chap10.Lemma_10_46_8
import stacks_proof.stacks_project.Chap10.Lemma_10_126_2
import stacks_proof.stacks_project.Chap10.Lemma_10_135_11
import stacks_proof.stacks_project.Chap10.Definition_10_136_1_Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

/-- Helper for Chap10 Lemma 10 136 2: local complete intersections are invariant under algebra
equivalence over the base field. -/
private theorem isLocalCompleteIntersection_of_algEquiv
    {k : Type u} [Field k]
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (hA : IsLocalCompleteIntersection k A) (e : A ≃ₐ[k] B) :
    IsLocalCompleteIntersection k B := by
  classical
  rcases hA.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  refine ⟨s.image e, ?_, ?_⟩
  · -- Transport the principal-open cover through the algebra equivalence.
    calc
      Ideal.span ((s.image e : Finset B) : Set B)
          = Ideal.map (e : A →+* B) (Ideal.span (s : Set A)) := by
              simp [Finset.coe_image, Ideal.map_span]
      _ = Ideal.map (e : A →+* B) ⊤ := by rw [hs]
      _ = ⊤ := Ideal.map_top _
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    -- The corresponding away localizations are algebra equivalent.
    exact IsGlobalCompleteIntersection.of_algEquiv (hglobal a ha) <|
      IsLocalization.algEquivOfAlgEquiv
        (A := k)
        (S := Localization.Away a)
        (Q := Localization.Away (e a))
        e
        (Submonoid.map_powers e a)

namespace RingHom

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

omit S [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 136 2: faithfully flatness of the algebra map supplies the
module-theoretic faithfully-flat instance used for descent. -/
private theorem moduleFaithfullyFlat_of_algebraMap_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    Module.FaithfullyFlat R R' := by
  -- Proof comment: switch from the ring-hom predicate to the module instance expected by the
  -- faithfully-flat descent lemmas and prime-surjectivity API.
  exact
    (RingHom.faithfullyFlat_algebraMap_iff : (algebraMap R R').FaithfullyFlat ↔
      Module.FaithfullyFlat R R').mp hff

omit S [CommRing S] [Algebra R S] in
/-- Helper for Chap10 Lemma 10 136 2: faithfully flatness of the algebra map gives the flat
module instance needed to view the base change as a flat transitive extension. -/
private theorem moduleFlat_of_algebraMap_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    Module.Flat R R' := by
  -- Proof comment: forget the faithful part and translate the flat ring-map predicate into the
  -- module-flat instance used by `Module.Flat.trans`.
  exact (RingHom.flat_algebraMap_iff).mp hff.flat

/-- Helper for Chap10 Lemma 10 136 2: after identifying the upstairs fiber with the residue-field
base change of the downstairs fiber, the local-complete-intersection condition is equivalent on
the two fibers. -/
private theorem baseChangeFiber_isLocalCompleteIntersection_iff
    (p' : PrimeSpectrum R') :
    let p := PrimeSpectrum.comap (algebraMap R R') p'
    IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S) ↔
      IsLocalCompleteIntersection p'.asIdeal.ResidueField
        (p'.asIdeal.Fiber (R' ⊗[R] S)) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  let e :=
    baseChange_fiber_algEquiv (R := R) (S := S) p'
  constructor
  · intro hfiber
    -- Proof comment: first pass the downstairs fiber to the residue-field extension, then
    -- transport that result across the canonical fiber equivalence.
    have htensor :
        IsLocalCompleteIntersection p'.asIdeal.ResidueField
          (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S) :=
      (isLocalCompleteIntersection_iff_of_tensorProduct_fieldExtension
        (k := p.asIdeal.ResidueField) (K := p'.asIdeal.ResidueField)
        (S := p.asIdeal.Fiber S)).mp hfiber
    exact isLocalCompleteIntersection_of_algEquiv htensor e.symm
  · intro hfiber
    -- Proof comment: rewrite the upstairs fiber as a residue-field base change, then descend the
    -- local-complete-intersection property along the field extension.
    have htensor :
        IsLocalCompleteIntersection p'.asIdeal.ResidueField
          (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S) :=
      isLocalCompleteIntersection_of_algEquiv hfiber e
    exact
      (isLocalCompleteIntersection_iff_of_tensorProduct_fieldExtension
        (k := p.asIdeal.ResidueField) (K := p'.asIdeal.ResidueField)
        (S := p.asIdeal.Fiber S)).mpr htensor

/-- Helper for Chap10 Lemma 10 136 2: local-complete-intersection fibers are preserved by
tensor-product base change. -/
private theorem hasLocalCompleteIntersectionFibers_baseChange
    (h : (algebraMap R S).HasLocalCompleteIntersectionFibers) :
    (algebraMap R' (R' ⊗[R] S)).HasLocalCompleteIntersectionFibers := by
  -- Proof comment: test the upstairs condition at a prime of `R'`, then compare its fiber with
  -- the residue-field base change of the downstairs fiber over the contracted prime.
  rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap] at h ⊢
  intro p'
  exact
    (baseChangeFiber_isLocalCompleteIntersection_iff
      (R := R) (S := S) (R' := R') p').mp
      (h (PrimeSpectrum.comap (algebraMap R R') p'))

/-- Helper for Chap10 Lemma 10 136 2: under a faithfully flat base change, the
local-complete-intersection fiber condition is equivalent before and after tensor-product base
change. -/
private theorem hasLocalCompleteIntersectionFibers_iff_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    (algebraMap R S).HasLocalCompleteIntersectionFibers ↔
      (algebraMap R' (R' ⊗[R] S)).HasLocalCompleteIntersectionFibers := by
  constructor
  · intro h
    -- Proof comment: the forward implication is the primewise base-change helper already proved.
    exact hasLocalCompleteIntersectionFibers_baseChange h
  · intro hbase
    -- Proof comment: for descent, lift each downstairs prime along the faithfully-flat map and
    -- transport the upstairs fiber condition back through the canonical residue-field comparison.
    letI : Module.FaithfullyFlat R R' := moduleFaithfullyFlat_of_algebraMap_faithfullyFlat hff
    rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap] at hbase ⊢
    intro p
    have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R R')) :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat
    obtain ⟨p', rfl⟩ := hsurj p
    simpa using
      (baseChangeFiber_isLocalCompleteIntersection_iff
        (R := R) (S := S) (R' := R') p').mpr (hbase p')

/-- Helper for Chap10 Lemma 10 136 2: syntomicity is preserved by tensor-product base change. -/
private theorem syntomic_baseChange_of_syntomic
    (h : (algebraMap R S).Syntomic) :
    (algebraMap R' (R' ⊗[R] S)).Syntomic := by
  -- Proof comment: prove the three defining syntomic components separately, using canonical
  -- base-change stability for flatness and finite presentation and the fiber helper above.
  refine ⟨?_, ?_, ?_⟩
  · rw [RingHom.flat_algebraMap_iff]
    letI : Module.Flat R S := (RingHom.flat_algebraMap_iff).mp h.flat
    exact Module.Flat.baseChange (R := R) (S := R') (M := S)
  · rw [RingHom.finitePresentation_algebraMap]
    letI : Algebra.FinitePresentation R S :=
      (RingHom.finitePresentation_algebraMap).mp h.finitePresentation
    infer_instance
  · exact hasLocalCompleteIntersectionFibers_baseChange h.hasLocalCompleteIntersectionFibers

/-- Helper for Chap10 Lemma 10 136 2: syntomicity descends from a faithfully flat tensor-product
base change. -/
private theorem syntomic_of_syntomic_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat)
    (hbase : (algebraMap R' (R' ⊗[R] S)).Syntomic) :
    (algebraMap R S).Syntomic := by
  -- Proof comment: cache the module faithfully-flat instance needed by the descent lemmas and by
  -- surjectivity of the prime-spectrum map.
  letI : Module.FaithfullyFlat R R' := moduleFaithfullyFlat_of_algebraMap_faithfullyFlat hff
  letI : Module.Flat R R' := moduleFlat_of_algebraMap_faithfullyFlat hff
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
  · -- Route correction: descend the fiber condition through the named faithfully-flat fiber iff,
    -- which packages the prime-lifting and residue-field comparison in one reusable step.
    exact
      (hasLocalCompleteIntersectionFibers_iff_baseChange_of_faithfullyFlat
        (R := R) (S := S) (R' := R') hff).mpr hbase.hasLocalCompleteIntersectionFibers

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
@[stacks 00SM]
theorem syntomic_iff_syntomic_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    (algebraMap R S).Syntomic ↔ (algebraMap R' (R' ⊗[R] S)).Syntomic := by
  constructor
  · intro h
    -- Proof comment: the forward implication is local base-change stability of the three
    -- syntomic components, proved above without importing the later base-change theorem.
    exact syntomic_baseChange_of_syntomic h
  · intro hbase
    -- Proof comment: the reverse implication is the faithfully-flat descent helper above.
    exact syntomic_of_syntomic_baseChange_of_faithfullyFlat hff hbase

end RingHom

end
