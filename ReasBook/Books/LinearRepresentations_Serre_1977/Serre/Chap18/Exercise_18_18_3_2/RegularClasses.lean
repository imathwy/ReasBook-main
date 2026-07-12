import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Remark_2_2_1_2
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.RegularConjClassCore

noncomputable section

universe u x

namespace Representation

section CentralizerPPart

variable {G : Type u} [Group G]

local notation "C(" x ")" => Subgroup.centralizer ({x} : Set G)

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `p`, the `p`-part of the order of the centralizer of an element of `G`. -/
noncomputable def centralizerPPart [Finite G] (p : ℕ) [Fact p.Prime] (g : G) : ℕ :=
  p ^ Nat.factorization (Nat.card C(g)) p

-- Proof sketch: this is the canonical Sylow-cardinality formula for the centralizer `C_G(g)`.
-- The source-facing integer is the `p`-part of `|C_G(g)|`, and any Sylow subgroup of `C_G(g)` has
-- exactly that cardinality by `Sylow.card_eq_multiplicity`.
/-- `centralizerPPart p g` equals the cardinality of any `p`-Sylow subgroup of the
centralizer of `g` in `G`. -/
theorem centralizerPPart_eq_card [Finite G] (g : G) (P : Sylow p C(g)) :
    centralizerPPart p g = Nat.card P := by
  symm
  simpa [centralizerPPart, Nat.card_eq_fintype_card] using
    P.card_eq_multiplicity

/-- The centralizer `p`-part depends only on the conjugacy class of `g`. -/
theorem centralizerPPart_eq_of_isConj [Finite G] {g h : G} (hgh : IsConj g h) :
    centralizerPPart p g = centralizerPPart p h := by
  rcases hgh with ⟨u, hu⟩
  have hh : h = (u : G) * g * (u : G)⁻¹ := by
    symm
    exact mul_inv_eq_iff_eq_mul.mpr hu
  rw [hh]
  let e : C(g) ≃* C((u : G) * g * (u : G)⁻¹) :=
    { toFun := fun x ↦
        ⟨(u : G) * x * (u : G)⁻¹, by
          have hx : (x : G) * g = g * x := by
            exact (Subgroup.mem_centralizer_singleton_iff).1 x.2
          simpa [Subgroup.mem_centralizer_singleton_iff, mul_assoc] using
            congrArg (fun t => (u : G) * t * (u : G)⁻¹) hx⟩
      invFun := fun x ↦
        ⟨(u : G)⁻¹ * x * (u : G), by
          have hx : (x : G) * ((u : G) * g * (u : G)⁻¹) = ((u : G) * g * (u : G)⁻¹) * x := by
            exact (Subgroup.mem_centralizer_singleton_iff).1 x.2
          simpa [Subgroup.mem_centralizer_singleton_iff, mul_assoc] using
            congrArg (fun t => (u : G)⁻¹ * t * (u : G)) hx⟩
      left_inv := fun x ↦ Subtype.ext <| by
        simp [mul_assoc]
      right_inv := fun x ↦ Subtype.ext <| by
        simp [mul_assoc]
      map_mul' := fun x y ↦ Subtype.ext <| by
        simp [mul_assoc] }
  have hcard : Nat.card C(g) = Nat.card C((u : G) * g * (u : G)⁻¹) :=
    Nat.card_congr e.toEquiv
  unfold centralizerPPart
  rw [hcard]

end Prime

end CentralizerPPart

namespace ConjClasses

variable {p : ℕ}
variable {G : Type u} [Group G] [Finite G]

section Prime

variable [Fact p.Prime]

/-- For a prime `p`, the `p`-part of the order of the centralizer of any representative of the
conjugacy class `c`. -/
noncomputable def centralizerPPart (p : ℕ) [Fact p.Prime] (c : ConjClasses G) : ℕ :=
  Quotient.lift (Representation.centralizerPPart p)
    (fun _ _ h ↦ Representation.centralizerPPart_eq_of_isConj h) c

@[simp] theorem centralizerPPart_mk (g : G) :
    ConjClasses.centralizerPPart p (ConjClasses.mk g) = Representation.centralizerPPart p g :=
  rfl

/-- The centralizer `p`-part attached to a conjugacy class is a power of `p`. -/
theorem centralizerPPart_eq_prime_pow (c : ConjClasses G) :
    ∃ e : ℕ, ConjClasses.centralizerPPart p c = p ^ e := by
  obtain ⟨g, hg⟩ := ConjClasses.mk_surjective c
  refine ⟨Nat.factorization (Nat.card (Subgroup.centralizer ({g} : Set G))) p, ?_⟩
  rw [← hg, ConjClasses.centralizerPPart_mk, Representation.centralizerPPart]

end Prime

end ConjClasses

end Representation
