import StacksProject_2024.stacks_project.Chap10.Lemma_10_158_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: purely inseparable finite field extensions in characteristic `p`, measured by the
  canonical universal derivation on Kähler differentials;
- sampled owner declarations:
  `KaehlerDifferential.D`,
  `kaehlerDifferential_eq_zero_iff_exists_pth_root`,
  `IntermediateField.adjoin`,
  `IntermediateField.relfinrank`;
- best owner abstraction: the source-facing generated intermediate field
  `IntermediateField.adjoin k (Set.range roots)`, together with the owner derivation
  `KaehlerDifferential.D (ZMod p) k`;
- primitive data: the family `a : Fin n → k`, the chosen roots `roots : Fin n → K`, and the
  equations `roots i ^ p = algebraMap k K (a i)`;
- derived API: the degree computation for the generated extension under linear independence of the
  differentials.

Source/core/bridge triage:
- `source-facing`: `relfinrank_adjoin_pthRoots_eq_pow`;
- `core/canonical`: `KaehlerDifferential.D (ZMod p) k`, `IntermediateField.adjoin`, and
  `IntermediateField.relfinrank`;
- `bridge/view`: Lemma `10.158.2`, which converts vanishing of a differential into existence of a
  `p`th root and is the canonical chapter input for the inductive degree-counting argument.
-/

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p n : ℕ} [Fact p.Prime] [CharP k p]
variable [Algebra (ZMod p) k]

-- Proof sketch: argue by induction on `n`. For the induction step, compare
-- `k(a_1^(1/p), ..., a_(n-1)^(1/p))` with the field obtained by adjoining one more chosen root of
-- `a_n`. If `a_n` became a `p`th power in the smaller field, Lemma `10.158.2` would force
-- `KaehlerDifferential.D (ZMod p) k (a n)` to lie in the `k`-span of the earlier differentials,
-- contradicting linear independence. Hence each step multiplies the relative degree by `p`.
/-- Lemma 10.158.3: if `da₁, ..., daₙ` are linearly independent in `Ω[k⁄ZMod p]`, then adjoining
chosen `p`th roots of the `aᵢ` gives an extension of degree `p ^ n` over `k`. -/
theorem relfinrank_adjoin_pthRoots_eq_pow
    (a : Fin n → k) (roots : Fin n → K)
    (hroots : ∀ i, roots i ^ p = algebraMap k K (a i))
    (hd :
      LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    (⊥ : IntermediateField k K).relfinrank (IntermediateField.adjoin k (Set.range roots)) =
      p ^ n := sorry

end
