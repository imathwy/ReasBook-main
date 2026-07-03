import stacks_project.Chap11.Definition_11_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

/- Domain-style sampling for Lemma 11.5.3:
- primary domain: Brauer equivalence classes of finite-dimensional central simple algebras over an
  algebraically closed field;
- sampled owner declarations:
  `CSA.brauerEquivalent_baseField`,
  `CSA.unit`,
  `BrauerGroup.one_def`,
  `Br`,
  `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`,
  `ULift.algEquiv`;
- best owner abstraction: the source-facing quotient-level statement belongs on the public owner
  `Br(k)`, using the canonical neutral class from `Definition_11_5_2`; the representative-level
  bridge is `CSA.brauerEquivalent_unit`;
- primitive data: a representative `A : CSA k`, the owner relation `IsBrauerEquivalent`, and the
  canonical neutral representative `CSA.unit`;
- derived API: the explicit quotient theorem `BrauerGroup.eq_one_of_isAlgClosed`, together with
  the quotient-level subsingleton instance obtained from that theorem.

Source/core/bridge triage:
- `source-facing`: every Brauer class over an algebraically closed field equals the unit class;
- `core/canonical`: `BrauerGroup k`, presented on the public surface as `Br(k)`;
- `bridge/view`: `CSA.brauerEquivalent_unit`, obtained from the source-facing base-field bridge
  plus the canonical comparison from `k` to `CSA.unit k`. -/

open Matrix

namespace CSA

section

variable (k : Type u) [Field k] [IsAlgClosed k]

private theorem brauerEquivalent_baseField_small (A : CSA.{u, u} k) :
    IsBrauerEquivalent A (CSA.mk (AlgCat.of k k)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k A
  refine ⟨1, n, one_ne_zero, hn.ne, ?_⟩
  exact ⟨((reindexAlgEquiv k A finOneEquiv).trans uniqueAlgEquiv).trans e⟩

omit [IsAlgClosed k] in
private theorem smallCarrierOfCSA (A : CSA.{u, v} k) : Small.{u} (↑A.toAlgCat) :=
  Small.mk' (Module.finBasis k A).equivFun.toEquiv

omit [IsAlgClosed k] in
private def shrinkCSA (A : CSA.{u, v} k) : CSA.{u, u} k :=
  letI := smallCarrierOfCSA k A
  { toAlgCat := AlgCat.of k (Shrink.{u} (↑A.toAlgCat))
    isCentral := by
      let e : Shrink.{u} (↑A.toAlgCat) ≃ₐ[k] ↑A.toAlgCat := Shrink.algEquiv k (↑A.toAlgCat)
      refine ⟨fun x hx ↦ ?_⟩
      have hx' : e x ∈ Subalgebra.center k (↑A.toAlgCat) := by
        rw [Subalgebra.mem_center_iff] at hx ⊢
        intro b
        have hcomm : e.symm b * x = x * e.symm b := hx (e.symm b)
        exact by simpa using congrArg e hcomm
      obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hx'
      rw [Algebra.mem_bot]
      refine ⟨a, ?_⟩
      have hxe : e x = e (algebraMap k (Shrink.{u} (↑A.toAlgCat)) a) := by
        simpa using ha
      exact e.injective hxe.symm
    isSimple := IsSimpleRing.of_ringEquiv (Shrink.ringEquiv (↑A.toAlgCat)).symm inferInstance
    fin_dim := (Shrink.algEquiv k (↑A.toAlgCat)).symm.toLinearEquiv.finiteDimensional }

omit [IsAlgClosed k] in
private def shrinkAlgEquiv (A : CSA.{u, v} k) : shrinkCSA k A ≃ₐ[k] A :=
  letI := smallCarrierOfCSA k A
  Shrink.algEquiv k (↑A.toAlgCat)

omit [IsAlgClosed k] in
private theorem brauerEquivalent_shrink (A : CSA.{u, v} k) :
    IsBrauerEquivalent A (shrinkCSA k A) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨((reindexAlgEquiv k A finOneEquiv).trans uniqueAlgEquiv).trans <|
    (shrinkAlgEquiv k A).symm.trans <|
      ((reindexAlgEquiv k (shrinkCSA k A) finOneEquiv).trans uniqueAlgEquiv).symm⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Lemma 11.5.3, representative-level bridge: over an algebraically closed field, every
finite-dimensional central simple `k`-algebra is Brauer equivalent to the base field. -/
theorem brauerEquivalent_baseField (A : CSA.{u, v} k) :
    IsBrauerEquivalent A (CSA.mk (AlgCat.of k k)) := by
  exact IsBrauerEquivalent.trans (brauerEquivalent_shrink k A)
    (brauerEquivalent_baseField_small k (shrinkCSA k A))

private theorem brauerEquivalent_baseField_unit (k : Type u) [Field k] :
    IsBrauerEquivalent (CSA.mk (AlgCat.of k k)) (CSA.unit k) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨((reindexAlgEquiv k (CSA.mk (AlgCat.of k k)) finOneEquiv).trans uniqueAlgEquiv).trans <|
    (ULift.algEquiv : ↑(CSA.unit k).toAlgCat ≃ₐ[k] k).symm.trans <|
      ((reindexAlgEquiv k (CSA.unit k) finOneEquiv).trans uniqueAlgEquiv).symm⟩

/-- Companion bridge: over an algebraically closed field, every finite-dimensional central simple
`k`-algebra is Brauer equivalent to the canonical neutral representative `CSA.unit k`. -/
theorem brauerEquivalent_unit (A : CSA.{u, max u v} k) :
    IsBrauerEquivalent A (CSA.unit k) := by
  exact IsBrauerEquivalent.trans A.brauerEquivalent_baseField (brauerEquivalent_baseField_unit k)

end

end CSA

namespace BrauerGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Lemma 11.5.3: if `k` is algebraically closed, then every Brauer class over `k` is the unit
class. -/
theorem eq_one_of_isAlgClosed (A : Br(k)) : A = 1 := by
  refine Quotient.inductionOn A fun A ↦ ?_
  rw [one_def]
  exact Quotient.sound A.brauerEquivalent_unit

instance subsingleton_of_isAlgClosed : Subsingleton (Br(k)) := by
  refine ⟨fun A B ↦ ?_⟩
  rw [A.eq_one_of_isAlgClosed, B.eq_one_of_isAlgClosed]

end BrauerGroup
