import StacksProject_2024.Chap10.Lemma_10_116_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- 
Domain-style sampling:
- primary domain: dimension theory of finite type algebras over a field, organized through quotient
  Krull dimensions and the order-theoretic coheight owner on `PrimeSpectrum`;
- sampled owner declarations of the same kind:
  `ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field`,
  `ringKrullDim_quotient`,
  `Order.coheight_eq_krullDim_Ici`,
  `Order.coheight_strictAnti`;
- best owner abstraction: the core canonical owner for the strict inequality is the coheight of the
  corresponding points of `Spec S`; the source-facing transcendence-degree statement should be
  obtained by identifying `ringKrullDim (S ⧸ q)` with `Cardinal.toNat (Algebra.trdeg k
  q.ResidueField)` via Lemma `10.116.1`, rather than by keeping a parallel geometric wrapper;
- primitive data: only the two prime ideals `q`, `q'` and the strict inclusion `hqq' : q < q'`;
- derived API: the quotient/fraction-ring identification with the residue field and the bridge from
  `PrimeSpectrum.zeroLocus q` to the upper interval `Set.Ici ⟨q, _⟩`.

Source/core/bridge triage:
* `source-facing`: the strict transcendence-degree inequality below;
* `core/canonical`: `ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field`,
  `ringKrullDim_quotient`, and `Order.coheight`;
* `bridge/view`: the identifications `FractionRing (S ⧸ q) ≃ₐ[k] q.ResidueField` and
  `PrimeSpectrum.zeroLocus q = Set.Ici ⟨q, _⟩`.

This file therefore stays source-facing while reusing the quotient-dimension and coheight owners
already present upstream, rather than introducing a second local dimension-comparison API.
-/

private theorem ringKrullDim_quotient_eq_trdeg_residueField_of_finiteType_over_field
    (q : Ideal S) [q.IsPrime] :
    ringKrullDim (S ⧸ q) = Cardinal.toNat (Algebra.trdeg k q.ResidueField) := by
  let e : FractionRing (S ⧸ q) ≃ₐ[k] q.ResidueField :=
    (FractionRing.algEquiv (S ⧸ q) q.ResidueField).restrictScalars k
  calc
    ringKrullDim (S ⧸ q) = Cardinal.toNat (Algebra.trdeg k (FractionRing (S ⧸ q))) :=
      ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field
    _ = Cardinal.toNat (Algebra.trdeg k q.ResidueField) := by
      simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq e)

private theorem ringKrullDim_quotient_eq_coheight (q : Ideal S) [q.IsPrime] :
    ringKrullDim (S ⧸ q) = Order.coheight (⟨q, inferInstance⟩ : PrimeSpectrum S) := by
  let x : PrimeSpectrum S := ⟨q, inferInstance⟩
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (q : Set S) = Set.Ici x := by
    ext p
    change q ≤ p.asIdeal ↔ x ≤ p
    rfl
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici x).symm

/-- Lemma 10.116.2: if `q ⊂ q'` are distinct prime ideals in a finite type `k`-algebra `S`, then
the transcendence degree of `q'.ResidueField` over `k` is strictly smaller than the transcendence
degree of `q.ResidueField` over `k`. -/
theorem trdeg_residueField_lt_of_lt_of_finiteType_over_field
    (q q' : Ideal S) [q.IsPrime] [q'.IsPrime] (hqq' : q < q') :
    Cardinal.toNat (Algebra.trdeg k q'.ResidueField) <
      Cardinal.toNat (Algebra.trdeg k q.ResidueField) := by
  let x : PrimeSpectrum S := ⟨q, inferInstance⟩
  let x' : PrimeSpectrum S := ⟨q', inferInstance⟩
  have hq' :
      ringKrullDim (S ⧸ q') = Cardinal.toNat (Algebra.trdeg k q'.ResidueField) :=
    ringKrullDim_quotient_eq_trdeg_residueField_of_finiteType_over_field q'
  have hq :
      ringKrullDim (S ⧸ q) = Cardinal.toNat (Algebra.trdeg k q.ResidueField) :=
    ringKrullDim_quotient_eq_trdeg_residueField_of_finiteType_over_field q
  have hx'fin : Order.coheight x' < ⊤ := by
    have hdim : ringKrullDim (S ⧸ q') < ⊤ := by
      rw [hq']
      exact lt_top_iff_ne_top.mpr (fun h ↦ nomatch h)
    rw [ringKrullDim_quotient_eq_coheight q'] at hdim
    exact WithBot.coe_lt_coe.mp hdim
  have hdim : ringKrullDim (S ⧸ q') < ringKrullDim (S ⧸ q) := by
    rw [ringKrullDim_quotient_eq_coheight q', ringKrullDim_quotient_eq_coheight q]
    exact WithBot.coe_lt_coe.mpr <|
      Order.coheight_strictAnti (show x < x' from hqq') hx'fin
  rw [hq', hq] at hdim
  exact ENat.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hdim)

end
