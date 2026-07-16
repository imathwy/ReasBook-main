import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra Representation

noncomputable section

universe u v

namespace Representation

section

variable {k : Type*} [CommSemiring k]
variable {G : Type u} [Group G]

/-- The coefficient function of a central element of `k[G]` is a class function. -/
theorem coeff_isClassFunction_of_mem_center (u : Subalgebra.center k (k[G])) :
    IsClassFunction fun s ↦ (u : k[G]) s :=
  ⟨by
    intro a b hab
    rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab) with ⟨g, hg⟩
    subst b
    have h :=
      congrArg (fun x : k[G] ↦ x (g * a))
        ((Subalgebra.mem_center_iff.mp u.2) (MonoidAlgebra.of k G g))
    simpa [MonoidAlgebra.of_apply, mul_assoc] using h⟩

end

section

variable {k : Type*} [CommSemiring k]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommMonoid V] [Module k V]

variable (ρ : Representation k G V)

private theorem asAlgebraHom_isIntertwining_of_mem_center
    (u : Subalgebra.center k (k[G])) :
    ρ.IsIntertwiningMap ρ (ρ.asAlgebraHom u) := by
  rw [isIntertwiningMap_iff]
  intro g v
  have h :=
    congrArg (ρ.asAlgebraHom)
      (((Subalgebra.mem_center_iff.mp u.2) (MonoidAlgebra.of k G g)).symm)
  simpa [asAlgebraHom_of, Module.End.mul_apply] using LinearMap.congr_fun h v

end

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

variable (ρ : Representation k G V) [ρ.IsIrreducible]

private noncomputable def centerToIntertwining :
    Subalgebra.center k (k[G]) →ₐ[k] ρ.IntertwiningMap ρ where
  toFun u :=
    (ρ.asAlgebraHom u).intertwiningMap_of_isIntertwiningMap ρ ρ
      (asAlgebraHom_isIntertwining_of_mem_center ρ u).isIntertwining
  map_zero' := by
    ext v
    rfl
  map_one' := by
    ext v
    simp
  map_add' u v := by
    ext w
    simp
  map_mul' u v := by
    ext w
    simp [Module.End.mul_apply]
  commutes' c := by
    ext v
    simp

private noncomputable def schurAlgEquiv :
    k ≃ₐ[k] ρ.IntertwiningMap ρ :=
  AlgEquiv.ofBijective (Algebra.ofId k (ρ.IntertwiningMap ρ))
    IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed

/-- The algebra homomorphism from the center of `k[G]` to `k` determined by an irreducible
finite-dimensional representation over an algebraically closed field: a central group-algebra
element acts by a scalar, and `centralCharacter ρ` records that scalar. -/
def centralCharacter :
    Subalgebra.center k (k[G]) →ₐ[k] k :=
  (schurAlgEquiv ρ).symm.toAlgHom.comp (centerToIntertwining ρ)

scoped[Representation] notation "ω[" ρ "]" => centralCharacter ρ

-- Proof sketch: `ρ.asAlgebraHom u` is an equivariant endomorphism of the irreducible
-- representation `ρ`; Schur's lemma over an algebraically closed field makes it scalar, and the
-- normalized trace formula identifies that scalar with `ω[ρ] u`.
/-- Proposition 6-6.3-1: for an irreducible finite-dimensional representation over an algebraically
closed field, every central element of `k[G]` acts by the homothety whose ratio is given by the
algebra homomorphism
`centralCharacter ρ : Subalgebra.center k (k[G]) →ₐ[k] k`, written `ω[ρ]`. -/
theorem asAlgebraHom_center_eq_centralCharacter_smul_id
    (u : Subalgebra.center k (k[G])) :
    ρ.asAlgebraHom u = ω[ρ] u • LinearMap.id := by
  have h :
      schurAlgEquiv ρ (ω[ρ] u) = centerToIntertwining ρ u := by
    simp [centralCharacter, schurAlgEquiv]
  simpa [centerToIntertwining, IntertwiningMap.algebraMap_apply] using
    (congrArg IntertwiningMap.toLinearMap h).symm

end

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

variable (ρ : Representation k G V) [ρ.IsIrreducible]

local instance instFintypeGCentralCharacterApplyEqSumCharacter : Fintype G := Fintype.ofFinite G

-- Proof sketch: apply the class-function endomorphism formula of Proposition `2-2.5-1` to the
-- coefficient function `s ↦ (u : k[G]) s`, which is constant on conjugacy classes because `u`
-- lies in the center; then identify the resulting scalar with `ω[ρ] u` by unfolding
-- `centralCharacter`.
/-- The value of the central character on a central group-algebra element is the normalized sum of
its coefficients weighted by the character values of the representation; this is the normalized
trace formula for `ω[ρ]` when `↑(dim V)` is nonzero in `k`. -/
theorem centralCharacter_apply_eq_sum_character
    (u : Subalgebra.center k (k[G])) (hfinrank : (Module.finrank k V : k) ≠ 0) :
    ω[ρ] u =
      (Module.finrank k V : k)⁻¹ * ∑ s : G, (u : k[G]) s * ρ.character s := by
  letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp fun hV ↦
    (show (⊥ : Subrepresentation ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) <|
      top_unique <| by
        intro x hx
        change x = 0
        exact hV.elim x 0
  letI : Invertible (Module.finrank k V : k) := invertibleOfNonzero hfinrank
  let a : k := (Module.finrank k V : k)⁻¹ * ∑ s : G, (u : k[G]) s * ρ.character s
  let fu : classFunctionSubmodule k G :=
    ⟨fun s ↦ (u : k[G]) s, coeff_isClassFunction_of_mem_center u⟩
  have haction :
      centerToIntertwining ρ u = algebraMap k (ρ.IntertwiningMap ρ) a := by
    have hsum_pkg :
        Finsupp.equivFunOnFinite.symm fu = ∑ s : G, fu s • MonoidAlgebra.of k G s := by
      simpa [MonoidAlgebra.of] using Finsupp.equivFunOnFinite_symm_eq_sum fu
    have hfu :
        Finsupp.equivFunOnFinite.symm fu = (u : k[G]) := by
      ext s
      simp [fu]
    have hu :
        (∑ s : G, fu s • MonoidAlgebra.of k G s) = (u : k[G]) := by
      rw [← hsum_pkg, hfu]
    have hsum :
        ρ.asAlgebraHom (∑ s : G, fu s • MonoidAlgebra.of k G s) = a • LinearMap.id := by
      simpa [a] using asAlgebraHom_classFunction_sum_eq_character_sum_smul_id ρ fu hfinrank
    have hscalar :
        ρ.asAlgebraHom u = a • LinearMap.id := by
      calc
        ρ.asAlgebraHom u = ρ.asAlgebraHom (∑ s : G, fu s • MonoidAlgebra.of k G s) := by rw [← hu]
        _ = a • LinearMap.id := hsum
    ext v
    simpa [a, centerToIntertwining, IntertwiningMap.algebraMap_apply, fu] using
      congrArg (fun f : Module.End k V ↦ f v) hscalar
  change (schurAlgEquiv ρ).symm (centerToIntertwining ρ u) = a
  simpa [centralCharacter, schurAlgEquiv, a] using
    congrArg (schurAlgEquiv ρ).symm haction

end

end Representation
