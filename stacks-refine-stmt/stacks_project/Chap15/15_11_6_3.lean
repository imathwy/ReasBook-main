import stacks_project.Chap15.«15_11_6_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)
variable {A' : Type v} [CommRing A'] [Algebra A A']

/- Domain-style sampling for 15.11.6.3:
- primary domain: commutative algebra of étale quotient splittings and reduction of integral
  closures modulo an ideal;
- sampled owner declarations:
  `exists_quotient_product_decomposition_of_etale_section`,
  `exists_integralClosure_product_decomposition_mod_ideal_with_localization`,
  `AlgEquiv.prodQuotientOfIsIdempotentElem`;
- best owner abstraction: a product decomposition of the quotient is canonically owned by an
  idempotent quotient split canonically owned by `AlgEquiv.prodQuotientOfIsIdempotentElem`,
  together with the identification of the first canonical quotient factor with `A ⧸ I`;
- primitive data: the idempotent `e : B' ⧸ I B'` singled out by the quotient splitting and the
  canonical quotient factor by `e`;
- derived API: the full product decomposition from the owner theorem, the first-projection
  compatibility for that split, the comparison map to the original quotient decomposition, and the
  localization witness from Lemma `15.11.5` stay downstream companion data from the stronger owner
  theorem, not part of this source-facing bridge theorem.

Source/core/bridge triage:
- `source-facing`: the existence of the quotient product decomposition on the reduction of the
  integral closure;
- `core/canonical`: the idempotent quotient split is owned by
  `AlgEquiv.prodQuotientOfIsIdempotentElem`;
- `bridge/view`: this theorem extracts the quotient-splitting consequence from the étale section
  hypothesis via the stronger decomposition theorem from Lemma `15.11.5`. -/

local notation "Abar" => A ⧸ I
local notation "B'" => integralClosure A A'
local notation "IB'" => Ideal.map (algebraMap A B') I

-- Proof sketch: apply the decomposition statement for the reduction of the integral closure from
-- Lemma `15.11.5` to the decomposition of `A' / I A'` determined by the section `σ : A' → Abar`,
-- and retain only the source-facing primitive data identifying the canonical quotient factor by
-- `e` with `Abar`.
/-- 15.11.6.3: if `A'` is an étale `A`-algebra equipped with an `A`-algebra map
`σ : A' → Abar`, then for `B'` the integral closure of `A` in `A'` there is an idempotent
`e : B' / I B'` whose canonical quotient factor `(B' / I B') / (e)` is identified with `Abar` as
an `Abar`-algebra. The full product decomposition is derived from
`AlgEquiv.prodQuotientOfIsIdempotentElem`, and the induced map to `Abar` recovers the base
`Abar`-algebra map. -/
theorem exists_integralClosure_quotient_product_of_etale_section
    [Algebra.Etale A A']
    (σ : A' →ₐ[A] Abar) :
    ∃ e : B' ⧸ IB',
      IsIdempotentElem e ∧
        ∃ firstFactor :
            ((B' ⧸ IB') ⧸ Ideal.span ({e} : Set (B' ⧸ IB'))) ≃ₐ[Abar] Abar,
          ∀ x : Abar,
            firstFactor
                (Ideal.Quotient.mk (Ideal.span ({e} : Set (B' ⧸ IB')))
                  (algebraMap Abar (B' ⧸ IB') x)) = x := by
  sorry

end
