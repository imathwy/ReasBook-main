import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Tactic.Group

noncomputable section

universe u

section

variable (k : Type u) [Field k]

/-- Helper for Chap10 Example 10 55 5: the endpoint-unit ratio homomorphism
`(a, b) ↦ b / a`, written additively for later quotient computations. -/
abbrev equalEndpointEndpointUnitRatioHom :
    Additive (kˣ × kˣ) →+ Additive kˣ :=
  MonoidHom.toAdditive ((MonoidHom.snd kˣ kˣ) * (MonoidHom.fst kˣ kˣ)⁻¹)

/-- Helper for Chap10 Example 10 55 5: the diagonal endpoint-unit homomorphism, written
additively to match the kernel/range API for the Milnor boundary sequence. -/
abbrev equalEndpointEndpointUnitDiagonalHom :
    Additive kˣ →+ Additive (kˣ × kˣ) :=
  MonoidHom.toAdditive ((MonoidHom.id kˣ).prod (MonoidHom.id kˣ))

/-- Helper for Chap10 Example 10 55 5: the endpoint-unit ratio homomorphism evaluates to
`b / a` on a pair `(a, b)`. -/
theorem equalEndpointEndpointUnitRatioHom_apply (p : kˣ × kˣ) :
    equalEndpointEndpointUnitRatioHom k (Additive.ofMul p) =
      Additive.ofMul (p.2 * p.1⁻¹) := by
  -- The homomorphism was defined by transporting the multiplicative pointwise ratio.
  rfl

/-- Helper for Chap10 Example 10 55 5: the endpoint pair `(1, u)` represents the ratio `u`. -/
theorem equalEndpointEndpointUnitRatioHom_one_pair (u : kˣ) :
    equalEndpointEndpointUnitRatioHom k (Additive.ofMul ((1 : kˣ), u)) =
      Additive.ofMul u := by
  -- This is the chosen representative used by the endpoint quotient equivalences.
  rw [equalEndpointEndpointUnitRatioHom_apply]
  simp

/-- Helper for Chap10 Example 10 55 5: the diagonal endpoint-unit homomorphism sends `a` to
`(a, a)`. -/
theorem equalEndpointEndpointUnitDiagonalHom_apply (a : kˣ) :
    equalEndpointEndpointUnitDiagonalHom k (Additive.ofMul a) =
      Additive.ofMul (a, a) := by
  -- The diagonal map is the product of two identity homomorphisms.
  rfl

/-- Helper for Chap10 Example 10 55 5: every unit occurs as an endpoint-unit ratio. -/
theorem equalEndpointEndpointUnitRatioHom_surjective :
    Function.Surjective (equalEndpointEndpointUnitRatioHom k) := by
  intro u
  -- The pair `(1, u)` has ratio `u`.
  refine ⟨Additive.ofMul ((1 : kˣ), u.toMul), ?_⟩
  simp [equalEndpointEndpointUnitRatioHom]

/-- Helper for Chap10 Example 10 55 5: an endpoint-unit pair has trivial ratio exactly when it
is diagonal. -/
theorem equalEndpointEndpointUnitRatioHom_eq_zero_iff (p : kˣ × kˣ) :
    equalEndpointEndpointUnitRatioHom k (Additive.ofMul p) = 0 ↔ p.2 = p.1 := by
  constructor
  · intro h
    -- Translate the additive zero statement back to the multiplicative identity ratio.
    change Additive.ofMul (p.2 * p.1⁻¹) = 0 at h
    change p.2 * p.1⁻¹ = 1 at h
    calc
      p.2 = (p.2 * p.1⁻¹) * p.1 := by group
      _ = p.1 := by rw [h]; simp
  · intro h
    -- A diagonal pair has ratio `1`, hence additive value `0`.
    change Additive.ofMul (p.2 * p.1⁻¹) = 0
    change p.2 * p.1⁻¹ = 1
    rw [h]
    simp

/-- Helper for Chap10 Example 10 55 5: the diagonal endpoint units are exactly the kernel of the
ratio homomorphism. -/
theorem equalEndpointEndpointUnitDiagonalHom_range_eq_ratioHom_ker :
    (equalEndpointEndpointUnitDiagonalHom k).range =
      (equalEndpointEndpointUnitRatioHom k).ker := by
  ext x
  constructor
  · intro hx
    -- A diagonal unit pair has trivial ratio, so its class lies in the kernel.
    rcases hx with ⟨a, rfl⟩
    simp [equalEndpointEndpointUnitRatioHom, equalEndpointEndpointUnitDiagonalHom]
  · intro hx
    -- A kernel element has equal endpoints, hence is reached from its common endpoint.
    have hdiag : x.toMul.2 = x.toMul.1 := by
      exact (equalEndpointEndpointUnitRatioHom_eq_zero_iff (k := k) x.toMul).mp hx
    refine ⟨Additive.ofMul x.toMul.1, ?_⟩
    change Additive.ofMul (x.toMul.1, x.toMul.1) = x
    change (x.toMul.1, x.toMul.1) = x.toMul
    exact Prod.ext rfl hdiag.symm

end
