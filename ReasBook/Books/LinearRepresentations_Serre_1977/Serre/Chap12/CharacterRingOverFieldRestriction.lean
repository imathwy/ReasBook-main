/-
Restriction API for `R[K](G)` (Serre §12.6), factored out of `Proposition_12_12_6_4` so that it
lives strictly upstream of `Theorem_12_12_6_2`.  This breaks the import cycle that previously
prevented `Theorem_12_12_6_2` from reusing the cyclic-descent infrastructure (Serre §12.7
Lemma 15).  The definitions below use nothing from `Theorem_12_12_6_2`.
-/
import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_5
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1

noncomputable section

universe u v

open CategoryTheory
open scoped BigOperators Representation SubgroupInduction

namespace Subgroup

section

variable {G : Type u} [Group G]

/-- Internal owner for precomposition on function algebras. The public mathematical content of
this file is the induced restriction on `R[K](G)`, not this raw function-space bridge. -/
private def precompAlgHom {α β : Type*} (K : Type v) [Field K] (f : α → β) :
    (β → K) →ₐ[ℤ] α → K where
  toFun := LinearMap.funLeft ℤ K f
  map_zero' := rfl
  map_one' := rfl
  map_add' χ ψ := by
    ext x
    rfl
  map_mul' χ ψ := by
    ext x
    rfl
  commutes' n := by
    ext x
    rfl

private theorem finiteDimensional_res
    {H J : Type u} [Monoid H] [Monoid J] (K : Type v) [Field K]
    (f : H →* J) (ρ : Rep.{max u v} K J) [FiniteDimensional K ρ] :
    FiniteDimensional K (Rep.res f ρ) := by
  -- Restriction does not change the underlying `K`-vector space, so finite-dimensionality is
  -- inherited by instance search.
  infer_instance

private theorem precomp_mem_characterRingOverField
    {H J : Type u} [Group H] [Group J] (K : Type v) [Field K]
    (f : H →* J) (χ : R[K](J)) :
    precompAlgHom K f χ ∈ R[K](H) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.2
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    change (Rep.res f ρ).ρ.character ∈ R[K](H)
    letI : FiniteDimensional K ρ := hρfd
    letI : FiniteDimensional K (Rep.res f ρ) := finiteDimensional_res K f ρ
    exact Representation.rep_character_mem_characterRingOverField (Rep.res f ρ)
  · intro n
    exact (R[K](H)).algebraMap_mem n
  · intro x y _ _ hx hy
    simpa using (R[K](H)).add_mem hx hy
  · intro x y _ _ hx hy
    simpa using (R[K](H)).mul_mem hx hy

-- Proof sketch: write `χ` as an integral linear combination of irreducible `K`-characters of
-- `G`. Restrict each generator along `H.subtype`; this is the character of the restricted
-- representation, hence lies in `R_K(H)`. The result follows by `ℤ`-linearity of the span
-- defining `characterRingOverField K`.
/-- Restricting an element of Serre's representation ring `R_K(G)` to a subgroup `H` gives an
element of `R_K(H)`. -/
theorem restrict_mem_characterRingOverField
    (K : Type v) [Field K] (H : Subgroup G) (χ : R[K](G)) :
    (fun h : H ↦ (χ : G → K) h) ∈ R[K](H) := by
  simpa using precomp_mem_characterRingOverField K H.subtype χ

/-- The canonical restriction algebra hom `R_K(G) → R_K(H)` attached to a subgroup `H ≤ G`. -/
def characterRingOverFieldRestriction (H : Subgroup G) (K : Type v) [Field K] :
    R[K](G) →ₐ[ℤ] R[K](H) :=
  (((precompAlgHom K H.subtype).comp (R[K](G)).val).codRestrict (R[K](H))
    (restrict_mem_characterRingOverField K H))

scoped[Representation] notation:max H " ↾R[" K "]" =>
  Subgroup.characterRingOverFieldRestriction H K

-- Proof sketch: `(H ↾R[K])` is defined by pointwise evaluation along `H.subtype`.
/-- Evaluating `(H ↾R[K]) χ` at `h ∈ H` just evaluates `χ` at the same group element. -/
@[simp] theorem characterRingOverFieldRestriction_apply
    (K : Type v) [Field K] (H : Subgroup G) (χ : R[K](G)) (h : H) :
    (((H ↾R[K]) χ : R[K](H)) : H → K) h = (χ : G → K) h :=
  rfl

-- Proof sketch: this is the same precomposition argument as
-- `restrict_mem_characterRingOverField`, now applied to the subgroup inclusion `H ↪ J`.
/-- Restricting an element of `R_K(J)` along an inclusion `H ≤ J` gives an element of `R_K(H)`. -/
theorem restrict_mem_characterRingOverFieldOfLe
    (K : Type v) [Field K] {H J : Subgroup G} (h : H ≤ J) (χ : R[K](J)) :
    (fun x : H ↦ (χ : J → K) (Subgroup.inclusion h x)) ∈ R[K](H) := by
  simpa using precomp_mem_characterRingOverField K (Subgroup.inclusion h) χ

/-- The canonical restriction map `R_K(J) → R_K(H)` attached to an inclusion `H ≤ J`. -/
def characterRingOverFieldRestrictionOfLe
    {H J : Subgroup G} (h : H ≤ J) (K : Type v) [Field K] :
    R[K](J) →ₐ[ℤ] R[K](H) :=
  (((precompAlgHom K (Subgroup.inclusion h)).comp (R[K](J)).val).codRestrict (R[K](H))
    (restrict_mem_characterRingOverFieldOfLe K h))

scoped[Representation] notation:max h " ↾R[" K "]" =>
  Subgroup.characterRingOverFieldRestrictionOfLe h K

-- Proof sketch: `(h ↾R[K])` is defined by evaluating `χ` on `H` through the inclusion `H ↪ J`.
/-- Evaluating `(h ↾R[K]) χ` at `x ∈ H` evaluates `χ` at the same group element viewed in `J`. -/
@[simp] theorem characterRingOverFieldRestrictionOfLe_apply
    {H J : Subgroup G} (h : H ≤ J) (K : Type v) [Field K] (χ : R[K](J)) (x : H) :
    (((h ↾R[K]) χ : R[K](H)) : H → K) x =
      (χ : J → K) (Subgroup.inclusion h x) :=
  rfl

end

end Subgroup
end
