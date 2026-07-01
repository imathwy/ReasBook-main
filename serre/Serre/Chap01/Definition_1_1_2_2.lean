import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Representation

universe u

section

variable {G : Type u} [Finite G]

/-- The regular complex representation has degree equal to the order of the group. -/
theorem leftRegular_finrank_eq_nat_card :
    Module.finrank ℂ (G →₀ ℂ) = Nat.card G := by
  let _ : Fintype G := Fintype.ofFinite G
  simpa [Nat.card_eq_fintype_card] using
    (show Module.finrank ℂ (G →₀ ℂ) = Fintype.card G from Module.finrank_finsupp_self)

end

section

variable {G : Type u} [Group G]

/- Definition 1-1.2-2: for a finite group `G`, the regular complex representation is the
canonical representation `Representation.leftRegular ℂ G` on the free complex vector space
`G →₀ ℂ`, whose standard basis is indexed by the elements of `G`. -/
#check Representation.leftRegular ℂ G

/-- In the regular representation, the translate of the basis vector at `1` is the basis vector
indexed by the translating group element. -/
theorem leftRegular_basisSingleOne_eq_orbit (s : G) :
    (Finsupp.basisSingleOne : Module.Basis G ℂ (G →₀ ℂ)) s =
      Representation.leftRegular ℂ G s (Finsupp.single (1 : G) (1 : ℂ)) := by
  simpa [Finsupp.coe_basisSingleOne] using
    (show Representation.leftRegular ℂ G s (Finsupp.single (1 : G) (1 : ℂ)) =
        Finsupp.single s (1 : ℂ) from
      Representation.ofMulAction_single s (1 : G) (1 : ℂ)).symm

section orbit_basis

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ G W) (b : Module.Basis G ℂ W) (w : W)

private theorem leftRegularMapEquiv_symm_bijective
    (hb : ∀ s : G, b s = ρ s w) :
    Function.Bijective ((Representation.leftRegularMapEquiv ρ).symm w) := by
  let f := (Representation.leftRegularMapEquiv ρ).symm w
  -- The candidate intertwiner sends each standard basis vector to the corresponding orbit vector.
  have hf_basis : ∀ s : G, f (Finsupp.single s (1 : ℂ)) = b s := by
    intro s
    simpa [f, hb s] using Representation.leftRegularMapEquiv_symm_single ρ s w
  -- In basis coordinates, the candidate intertwiner is the identity on the standard basis.
  have hcomp : b.repr.toLinearMap.comp f.toLinearMap = LinearMap.id := by
    refine Finsupp.basisSingleOne.ext fun s ↦ ?_
    simpa [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, hf_basis s] using Basis.repr_self b s
  -- Hence every vector has the same coordinates before and after applying `f`.
  have hrepr : ∀ x : G →₀ ℂ, b.repr (f x) = x := by
    intro x
    have h := congrArg (fun l : (G →₀ ℂ) →ₗ[ℂ] G →₀ ℂ => l x) hcomp
    simpa [LinearMap.comp_apply] using h
  constructor
  · intro x y hxy
    -- Injectivity follows by comparing the basis coordinates of equal images.
    rw [← hrepr x, ← hrepr y]
    exact congrArg b.repr hxy
  · intro y
    -- The coordinate vector `b.repr y` is a preimage of `y`.
    refine ⟨b.repr y, ?_⟩
    apply b.repr.injective
    rw [hrepr]
/-- If the orbit of `w` under `ρ` is a basis indexed by `G`, then `ρ` is equivariantly
isomorphic to the regular representation. -/
noncomputable def leftRegular_equiv_of_basis_eq_orbit
    (hb : ∀ s : G, b s = ρ s w) :
    (Representation.leftRegular ℂ G).Equiv ρ :=
  (((Representation.leftRegularMapEquiv ρ).symm w).ofBijective
    (leftRegularMapEquiv_symm_bijective ρ b w hb))

/-- The canonical orbit-basis equivalence sends the standard basis vector at `s` to `ρ s w`. -/
theorem leftRegular_equiv_of_basis_eq_orbit_apply_single
    (hb : ∀ s : G, b s = ρ s w) (s : G) :
    leftRegular_equiv_of_basis_eq_orbit ρ b w hb (Finsupp.single s (1 : ℂ)) = ρ s w := by
  simpa [leftRegular_equiv_of_basis_eq_orbit] using
    Representation.leftRegularMapEquiv_symm_single ρ s w

end orbit_basis

end
