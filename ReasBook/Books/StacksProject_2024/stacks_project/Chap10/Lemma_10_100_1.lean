import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x y

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
variable (W : Submonoid (S ⊗[R] R'))
variable [Algebra (S ⊗[R] R') S']
variable [IsScalarTower S (S ⊗[R] R') S'] [IsScalarTower R' (S ⊗[R] R') S']
variable [IsLocalization W S']

variable {M : Type y} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/- Domain triage:
- primary domain: commutative algebra of flatness under base change, localization, and descent;
- source-facing layer: the four Stacks implications comparing flatness of `M` with flatness of the
  textbook base-changed module `S' ⊗[S] M`;
- core/canonical owner: `Module.Flat`, `Module.FaithfullyFlat`, `Module.Flat.trans`,
  `Module.Flat.of_isLocalizedModule`, `IsLocalization.flat`, and
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`;
- bridge/view: the identification of `S' ⊗[S] M` with the localization of the canonical
  base-change over `S ⊗[R] R'`.

The public items stay source-facing. The refinement only trims redundant ambient hypotheses:
parts `(1)` and `(3)` need only base change plus localization, while parts `(2)` and `(4)` add
exactly the local-hom hypotheses needed for faithful-flat descent along `S → S'`.
-/

-- Proof sketch: first base change the `R`-flat `S`-module `M` along `R → R'` to obtain an
-- `R'`-flat module over `S ⊗[R] R'`; then identify `S' ⊗[S] M` with the localization of that
-- base change along the localization map `(S ⊗[R] R') → S'`, and use that localization preserves
-- flatness.
/-- Lemma 10.100.1 (1): if `M` is flat over `R`, then after forming
`M' = S' ⊗[S] M`, the module `M'` is flat over `R'`, provided `S'` is a localization of
`S ⊗[R] R'`. -/
theorem flat_tensorProduct_of_flat_of_isLocalization_tensorProduct
    (hM : Module.Flat R M) : Module.Flat R' (S' ⊗[S] M) := sorry

-- Proof sketch: use part (1) with `M := S` to show that `S → S'` is flat when `R → R'` is flat;
-- because `S → S'` is also a local homomorphism of local rings, it is faithfully flat. Then apply
-- faithfully flat descent for flatness along `S → S'` to descend flatness of `S' ⊗[S] M` back to
-- flatness of `M` over `R`.
/-- Lemma 10.100.1 (2): if `M' = S' ⊗[S] M` is flat over `R'` and `R'` is flat over `R`, then
`M` is flat over `R`. -/
theorem flat_of_flat_tensorProduct_of_isLocalization_tensorProduct
    [IsLocalRing S] [IsLocalRing S'] [IsLocalHom (algebraMap S S')]
    (hM' : Module.Flat R' (S' ⊗[S] M)) (hR' : Module.Flat R R') :
    Module.Flat R M := sorry

-- Proof sketch: specialize part (1) to the `S`-module `M := S`; then `S' ⊗[S] S` identifies with
-- `S'`, so flatness of `S` over `R` ascends to flatness of `S'` over `R'`.
/-- Lemma 10.100.1 (3): if `S` is flat over `R`, then `S'` is flat over `R'`. -/
theorem flat_target_of_flat_source_of_isLocalization_tensorProduct
    (hS : Module.Flat R S) : Module.Flat R' S' := sorry

-- Proof sketch: specialize part (2) to the `S`-module `M := S`; then `S' ⊗[S] S` is canonically
-- `S'`, so flatness of `R' → S'` together with flatness of `R → R'` descends to flatness of
-- `R → S`.
/-- Lemma 10.100.1 (4): if `R' → S'` is flat and `R → R'` is flat, then `S` is flat over `R`.
-/
theorem flat_source_of_flat_target_of_isLocalization_tensorProduct
    [IsLocalRing S] [IsLocalRing S'] [IsLocalHom (algebraMap S S')]
    (hS' : Module.Flat R' S') (hR' : Module.Flat R R') : Module.Flat R S := sorry

end
