import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Index
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CanonicalPacketFrontier
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_PacketReindex
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_CharZeroSupportedFamily

noncomputable section

open scoped MonoidAlgebra
open Representation
open CategoryTheory

universe u v w x y

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

/-- Helper for Proposition 16-16.4-1: transporting a group-algebra element along a group
equivalence carries any verified coefficient formula by precomposing the coefficient function with
the inverse equivalence. This isolates the `MonoidAlgebra.domCongr` coefficient rewrite used when
the characteristic-zero packet preimage is moved from `Shrink G` back to `G`. -/
lemma domCongr_coeff_formula_transport_local
    {R : Type*} [CommSemiring R]
    {H : Type*} [Group H]
    {G' : Type*} [Group G']
    (e : H ≃* G')
    (u : MonoidAlgebra R H)
    (f : H → R)
    (hu : ∀ s : H, u s = f s) :
    ∀ s : G', (MonoidAlgebra.domCongr R R e u) s = f (e.symm s) := by
  intro s
  -- Read the transported coefficient through `domCongr_apply` and then substitute the known
  -- `H`-side formula.
  rw [MonoidAlgebra.domCongr_apply]
  exact hu (e.symm s)

/-- Helper for Proposition 16-16.4-1: transporting a group-algebra element along a group
equivalence matches precomposing the representation by that equivalence. This isolates the action
transport needed when the characteristic-zero supported preimage is moved from `Shrink G` back to
`G`. -/
lemma asAlgebraHom_domCongr_eq_comp_local
    {R : Type*} [CommSemiring R]
    {H : Type*} [Group H]
    {G' : Type*} [Group G']
    {V : Type*} [AddCommMonoid V] [Module R V]
    (ρ' : Representation R G' V)
    (e : H ≃* G')
    (u : MonoidAlgebra R H) :
    ρ'.asAlgebraHom (MonoidAlgebra.domCongr R R e u) =
      (Representation.asAlgebraHom (ρ'.comp e.toMonoidHom) u) := by
  induction u using MonoidAlgebra.induction_linear with
  | zero =>
      simp
  | add u v hu hv =>
      -- Both sides are additive in the group-algebra variable, so the transport identity extends
      -- from the summands to their sum.
      simp [hu, hv]
  | single h a =>
      -- On one basis vector `[h]`, `domCongr` renames it to `[e h]` (`domCongr_single`), so both
      -- sides reduce to the same generator action `a • ρ' (e h)`.
      rw [MonoidAlgebra.domCongr_single]
      simp [MonoidHom.comp_apply]


end DefectZero

end StableLattice

end
