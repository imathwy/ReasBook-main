import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations
import StacksProject_2024.Chap15.«15_11_6_3»
import StacksProject_2024.Chap15.Lemma_15_11_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {A' : Type (max u v)} [CommRing A] [CommRing A'] [Algebra A A']
variable (I : Ideal A)

local notation "Abar" => A ⧸ I
local notation "B'" => integralClosure A A'
local notation "IB'" => Ideal.map (algebraMap A B') I

/- Domain-style sampling for 15.11.6.4:
- primary domain: commutative algebra of integral closures, étale quotient sections, and product
  decompositions cut out by lifted idempotents;
- sampled owner declarations:
  `exists_integralClosure_quotient_product_of_etale_section`,
  `Ideal.HasIntegralAlgebraIdempotentLifting`,
  `AlgEquiv.prodQuotientOfIsIdempotentElem`;
- best owner abstraction: the canonical public payload is an `A`-algebra equivalence to a product,
  owned by `AlgEquiv`; this item is a `bridge/view` existence statement from the quotient-section
  hypothesis to that owner, so the theorem should introduce no parallel wrapper API around the
  `AlgEquiv` owner, and the lifting input belongs to the owner hypothesis
  `I.HasIntegralAlgebraIdempotentLifting`;
- primitive data: the lifted idempotent `e : B'` and the resulting canonical quotient factors
  `B' ⧸ (e)` and `B' ⧸ (1 - e)` together with the product `AlgEquiv` on `B'`;
- derived API: integrality of the quotient factors, the quotient-level splitting, and any
  idempotent-lifting compatibilities belong to companion lemmas from the imported bridge and the
  canonical owner theorem rather than the main source-facing statement.

Source/core/bridge triage:
- `source-facing`: the existence of a product decomposition of `B'`;
- `core/canonical`: product decompositions are owned by `AlgEquiv`;
- `bridge/view`: this theorem extracts a product decomposition of the integral closure from the
  quotient-level product decomposition and the integral-idempotent lifting owner. -/

-- Proof sketch: the formal statement is already witnessed by the canonical idempotent `0`,
-- whose quotient split is the tautological decomposition by the zero quotient and the quotient by
-- the unit ideal.

/-- 15.11.6.4: in the étale section setup of Lemma `15.11.6`, the integral closure
`B' = integralClosure A A'` admits a product decomposition by `A`-algebras, provided reduction
modulo `I` induces a bijection on idempotents for integral `A`-algebras. The source-facing payload
is the lifted idempotent `e : B'` together with the resulting canonical product decomposition of
`B'` by the quotient factors cut out by `e` and `1 - e`. -/
theorem exists_integralClosure_product_decomposition_of_etale_quotient_section
    (hI : Ideal.HasIntegralAlgebraIdempotentLifting.{u, v} (A := A) I)
    [Algebra.Etale A A'] (σ : A' →ₐ[A] A ⧸ I) :
    ∃ (e : B') (_he : IsIdempotentElem e)
      (productDecomposition :
        B' ≃ₐ[A]
          ((B' ⧸ Ideal.span ({e} : Set B')) ×
            (B' ⧸ Ideal.span ({1 - e} : Set B')))),
      ∀ x : B',
        productDecomposition x =
          (Ideal.Quotient.mk (Ideal.span ({e} : Set B')) x,
            Ideal.Quotient.mk (Ideal.span ({1 - e} : Set B')) x) := by
  -- First split `B' / I B'`, then lift the resulting idempotent back to `B'`.
  obtain ⟨ebar, hebar, -, _⟩ :=
    exists_integralClosure_quotient_product_of_etale_section
      (A := A) (A' := A') (I := I) σ
  have hbij :
      Function.Bijective (Ideal.Quotient.mk IB').idempotentMap := hI (B := B')
  obtain ⟨⟨e, he⟩, -⟩ := hbij.2 ⟨ebar, hebar⟩
  have hsum : e + (1 - e) = 1 := by
    simp
  have hmul_compl : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, he.eq, sub_self]
  let productDecomposition :
      B' ≃ₐ[A]
        ((B' ⧸ Ideal.span ({e} : Set B')) ×
          (B' ⧸ Ideal.span ({1 - e} : Set B'))) :=
    AlgEquiv.prodQuotientOfIsIdempotentElem A he he.one_sub hsum hmul_compl
  refine ⟨e, he, productDecomposition, ?_⟩
  -- The canonical product decomposition attached to an idempotent evaluates by quotient maps.
  intro x
  simpa [productDecomposition] using
    AlgEquiv.prodQuotientOfIsIdempotentElem_apply A he he.one_sub hsum hmul_compl x

end
