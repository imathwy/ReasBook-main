import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Algebra.Category.Ring.Instances

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

-- Semantic recall: `lean_leansearch` located the canonical owner
-- `AlgebraicGeometry.Scheme.fromSpecStalk`, which matches the general clause of the source.
--
-- Source/core/bridge triage for Example 26.23.10:
-- - `source-facing`: the two monomorphism assertions from the example;
-- - `core/canonical`: the existing map `Scheme.fromSpecStalk` and the
--   `IsPreimmersion`-to-`Mono` instance;
-- - `bridge/view`: the second statement is kept as the owner-level companion theorem
--   for the canonical morphism `Spec(𝒪_{S,s}) ⟶ S`.

namespace AlgebraicGeometry

/-- Example 26.23.10 (1): the canonical morphism `Spec(ℚ) ⟶ Spec(ℤ)` is a monomorphism. -/
@[stacks 01L9]
theorem specRatToSpecInt_mono :
    Mono (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) := by
  let _ : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) :=
    IsPreimmersion.of_isLocalization (Submonoid.pos ℤ)
  infer_instance

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Example 26.23.10 (2): for any scheme `S` and any point `s ∈ S`, the canonical morphism
`Spec(\mathcal{O}_{S, s}) ⟶ S` is a monomorphism. -/
@[stacks 01L9]
theorem mono_fromSpecStalk (S : Scheme) (s : S) :
    Mono (S.fromSpecStalk s) :=
  inferInstance

end AlgebraicGeometry.Scheme
