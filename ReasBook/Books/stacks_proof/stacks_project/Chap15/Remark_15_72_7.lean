import stacks_proof.stacks_project.Chap15.Lemma_15_72_6

open CategoryTheory
open MonoidalCategory
open MonoidalClosed
open scoped ModuleComplexInternalHom

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for Remark 15.72.7:
- primary domain: the summandwise sign in the tensor-to-iterated-internal-Hom comparison of
  Lemma `15.72.6`, expressed through the chapter owner `⟪-, -⟫` and its degreewise product
  decomposition;
- sampled owner declarations:
  `tensor_internal_hom_to_iterated_internal_hom_component`,
  `tensor_internal_hom_to_iterated_internal_hom`,
  `module_complex_internal_hom_piProj`,
  `Int.negOnePow_mul_self`;
- best owner abstraction:
  `source-facing`: the sign comparison for the specific braiding/evaluation component used in
    Lemma `15.72.6`;
  `core/canonical`: `tensor_internal_hom_to_iterated_internal_hom_component`,
    `module_complex_internal_hom_piProj`, and `Int.negOnePow`;
  `bridge/view`: the diagonal-index observation and the resulting simplification of the braiding
    sign to the direct-construction sign;
- primitive data vs. derived API: the primitive owner data are the actual component map of
  Lemma `15.72.6` and the canonical degree decomposition of `⟪K, L⟫`; the remark is derived bridge
  API explaining that, in the `(-r')`-factor of `((⟪K, L⟫).X p)`, the braiding sign only matters
  on the diagonal forced by the degree bookkeeping.
-/

variable (K L M : CpxR) (t r n p : ℤ) (h : t + r = n)

/- Remark 15.72.7 concerns the summandwise braiding/evaluation component used to build the
comparison morphism `tensor_internal_hom_to_iterated_internal_hom K L M`. -/
#check tensor_internal_hom_to_iterated_internal_hom_component K L M t r n p h

section

variable {q r r' p : ℤ}

/-- In the `(-r')`-factor `Hom_R(K^{-r'}, L^q)` of `((⟪K, L⟫).X p)`, the degree bookkeeping from
Remark `15.72.7` forces the tensor summand indexed by `K^r` to lie on the diagonal `r = r'`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_component_diagonal
    (hp : q + r = p) (hp' : q + r' = p) :
    r = r' := by
  exact add_left_cancel (hp.trans hp'.symm)

/-- For the `(-r')`-factor of the target internal Hom in
`tensor_internal_hom_to_iterated_internal_hom_component`, the braiding sign `(-1)^(rp)` agrees,
on the diagonal singled out in Remark `15.72.7`, with the direct-construction sign
`(-1)^(r + qr)`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_component_sign_agrees
    (hp : q + r = p) (hp' : q + r' = p) :
    (r * p).negOnePow = (r + q * r).negOnePow := by
  have hr : r = r' :=
    tensor_internal_hom_to_iterated_internal_hom_component_diagonal hp hp'
  subst hr
  calc
    (r * p).negOnePow = (r * (q + r)).negOnePow := by rw [hp]
    _ = (q * r + r * r).negOnePow := by
      congr 1
      ring
    _ = (q * r).negOnePow * (r * r).negOnePow := by
      rw [Int.negOnePow_add]
    _ = (q * r).negOnePow * r.negOnePow := by
      rw [Int.negOnePow_mul_self]
    _ = (q * r + r).negOnePow := by
      rw [← Int.negOnePow_add]
    _ = (r + q * r).negOnePow := by
      congr 1
      ring

end

end
