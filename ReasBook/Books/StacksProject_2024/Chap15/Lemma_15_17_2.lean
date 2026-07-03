import StacksProject_2024.Chap15.Lemma_15_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R] [IsArtinianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {R' : Type w} [CommRing R'] [Algebra R R']

/- Domain triage:
- primary domain: commutative algebra of Artinian flatness criteria under quotienting and base
  change;
- sampled owner declarations of the same kind:
  `Ideal.IsFlatQuotient`,
  `Module.Flat.baseChange`,
  `IsBaseChange.tensorEquiv`,
  `TensorProduct.tensorQuotMapSMulEquivTensorQuot`;
- best owner abstraction in this chapter: the source-facing ideal predicate `J.IsFlatQuotient M`,
  whose canonical core is `Module.Flat` on the quotient ring and quotient module;
- primitive data: the base ring `R`, the module `M`, the least ideal `I`, and the target
  `R`-algebra `R'`;
- derived API: the base-change flatness criterion characterized by vanishing of the image ideal.

Layering:
- `source-facing`: this theorem identifies when the least flat-quotient ideal becomes zero after
  base change;
- `core/canonical`: `Ideal.IsFlatQuotient`, `Module.Flat`, the quotient-base-change owner
  `IsBaseChange.tensorEquiv`, the packaged quotient/tensor comparison
  `TensorProduct.tensorQuotMapSMulEquivTensorQuot`, and the
  Chapter 10 Artinian descent theorem
  `flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct`;
- no separate `bridge/view` owner is introduced here.
-/

-- Proof sketch: the quotient map `M → M ⧸ (I • ⊤)` is the base change of `M` along
-- `R → R ⧸ I`, so after any further `R ⧸ I`-algebra base change, `IsBaseChange.tensorEquiv`
-- identifies `R' ⊗[R ⧸ I] (M ⧸ (I • ⊤))` with `R' ⊗[R] M`. If `I.map (algebraMap R R') = ⊥`,
-- endow `R'` with its induced `R ⧸ I`-algebra structure and base-change the flat quotient module
-- to conclude that `R' ⊗[R] M` is flat. Conversely, for `J = RingHom.ker (algebraMap R R')`, the
-- same base-change comparison identifies `R' ⊗[R ⧸ J] (M ⧸ (J • ⊤))` with `R' ⊗[R] M`; applying
-- `flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct` over `R ⧸ J` shows
-- `J.IsFlatQuotient M`, and the leastness of `I` then forces `I ≤ J`, equivalently
-- `I.map (algebraMap R R') = ⊥`.

/-- Lemma 15.17.2: if `I` is the smallest ideal such that `M / IM` is flat over `R ⧸ I`, then
for any `R`-algebra `R'`, the base change `R' ⊗[R] M` is flat over `R'` if and only if the image
of `I` in `R'` is zero. -/
theorem flat_baseChange_iff_map_eq_bot_of_isLeast_flat_quotient_ideal
    {I : Ideal R}
    (hI : IsLeast {J : Ideal R | J.IsFlatQuotient M} I) :
    Module.Flat R' (R' ⊗[R] M) ↔ I.map (algebraMap R R') = ⊥ := by
  constructor
  · intro hflat
    sorry
  · intro hmap
    sorry

end
