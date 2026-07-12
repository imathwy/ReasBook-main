import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/- Domain-style sampling:
- primary domain: projective modules and factorization of linear maps through a target map whose
  range contains the source range;
- sampled owner declarations: `Module.projective_lifting_property`,
  `Module.Projective.of_basis`, and `Module.Projective.of_free`;
- best owner abstraction: `Module.Projective R P`, with
  `Module.projective_lifting_property` as the canonical lifting API;
- primitive data: a projective source module `P`, maps `g : P →ₗ[R] N` and `f : M →ₗ[R] N`, and a
  range inclusion `g.range ≤ f.range`;
- derived API: the range-inclusion factorization theorem below and its finite-free specialization;
- layer: `LinearMap.exists_comp_eq_of_range_le` is a `bridge/view`, while
  `exists_factorization_of_range_le_of_free` remains the `source-facing` finite-free statement. -/

namespace LinearMap

theorem exists_comp_eq_of_range_le
    {R : Type u} [Semiring R]
    {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]
    {M : Type w} [AddCommMonoid M] [Module R M]
    {N : Type _} [AddCommMonoid N] [Module R N]
    (g : P →ₗ[R] N) (f : M →ₗ[R] N)
    (h : g.range ≤ f.range) :
    ∃ l : P →ₗ[R] M, f.comp l = g := by
  let g' : P →ₗ[R] f.range := g.codRestrict f.range fun x ↦ h <| mem_range_self g x
  obtain ⟨l, hl⟩ :=
    Module.projective_lifting_property f.rangeRestrict g' f.surjective_rangeRestrict
  refine ⟨l, ?_⟩
  exact ext fun x ↦ congrArg Subtype.val <| LinearMap.congr_fun hl x

end LinearMap

/-- Lemma 10.5.2: if the image of a linear map `α : (Fin n → R) →ₗ[R] M` from the finite free
module `R^{\oplus n}` is contained in the image of `β : N →ₗ[R] M`, then `α` factors through
`β`. In canonical Lean form, this is the finite-free special case of
`Module.projective_lifting_property`. -/
@[stacks 07JX]
theorem exists_factorization_of_range_le_of_free
    {R : Type u} [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    {N : Type w} [AddCommMonoid N] [Module R N]
    {n : ℕ}
    (α : (Fin n → R) →ₗ[R] M) (β : N →ₗ[R] M)
    (h : α.range ≤ β.range) :
    ∃ γ : (Fin n → R) →ₗ[R] N, β.comp γ = α := by
  exact LinearMap.exists_comp_eq_of_range_le α β h
