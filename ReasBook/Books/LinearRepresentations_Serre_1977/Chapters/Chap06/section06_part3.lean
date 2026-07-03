import Mathlib
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.NumberTheory.Niven
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_6_6_3_4 (from Chap06) -/
open scoped MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {k G : Type u} [Field k] [IsAlgClosed k]
variable {ι : Type v} [Group G] [Finite G] [Invertible (Nat.card G : k)]
variable (π : ι → Rep k G)
variable [∀ i, FiniteDimensional k (π i)]

-- Source/core/bridge triage:
-- * source-facing: the exercise says that every `k`-algebra map from the center of `k[G]` to `k`
--   is the central character of one irreducible constituent in a complete family.
-- * core/canonical: the chapter owner `ω[ρ] = centralCharacter ρ` from
--   Proposition `6-6.3-1`, together with the owner equivalence
--   `centralCharacterFamilyAlgEquiv` from Proposition `6-6.3-2`.
-- * bridge/view: the scalar-action reformulation comes afterward from
--   `asAlgebraHom_center_eq_centralCharacter_smul_id`.
-- Proof sketch: Proposition `centralCharacterFamilyAlgEquiv` identifies the center of `k[G]`
-- with the product algebra `ι → k`. The completeness and pairwise-nonisomorphism hypotheses make
-- `ι` finite, so `AlgHom.eq_piEvalAlgHom` says that any algebra map `(ι → k) →ₐ[k] k` is
-- evaluation at some index `i`. Transporting back along the equivalence identifies `η` with the
-- central character `ω[(π i).ρ]`.
/-- For a complete pairwise nonisomorphic irreducible family, every `k`-algebra homomorphism from
the center of `k[G]` to `k` is the central character of one member of the family. -/
theorem exists_centralCharacter_of_pairwise_complete_irreducible_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (η : Subalgebra.center k (k[G]) →ₐ[k] k) :
    ∃ i,
      let _ : (π i).ρ.IsIrreducible :=
        IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
      ω[(π i).ρ] = η := by
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  obtain ⟨i, hi⟩ := (η.comp e.symm.toAlgHom).eq_piEvalAlgHom
  refine ⟨i, ?_⟩
  letI : (π i).ρ.IsIrreducible := IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  ext u
  -- Evaluate the algebra-map identity on the image of `u` under the central-character equivalence.
  have hu : η u = (e u) i := by
    simpa using congrArg (fun f : (ι → k) →ₐ[k] k ↦ f (e u)) hi
  simpa [e] using hu.symm

-- Proof sketch: first identify `η` with `ω[(π i).ρ]` via the previous theorem, then use
-- Proposition `asAlgebraHom_center_eq_centralCharacter_smul_id` to translate equality of central
-- characters into the scalar-action formula.
/-- Scalar-action reformulation of
`exists_centralCharacter_of_pairwise_complete_irreducible_family`. -/
theorem exists_centralCharacter_action_of_pairwise_complete_irreducible_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (η : Subalgebra.center k (k[G]) →ₐ[k] k) :
    ∃ i,
      ∀ u : Subalgebra.center k (k[G]),
        (π i).ρ.asAlgebraHom u = η u • LinearMap.id := by
  obtain ⟨i, hi⟩ :=
    exists_centralCharacter_of_pairwise_complete_irreducible_family π hπ_pairwise hπ_complete η
  refine ⟨i, ?_⟩
  letI : (π i).ρ.IsIrreducible := IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  have hi' : ω[(π i).ρ] = η := hi
  intro u
  have hiu : ω[(π i).ρ] u = η u := by
    simpa using congrArg (fun f : Subalgebra.center k (k[G]) →ₐ[k] k ↦ f u) hi'
  rw [← hiu]
  exact asAlgebraHom_center_eq_centralCharacter_smul_id (π i).ρ u

/-- Helper for Exercise 6-6.3-4: isomorphism of the underlying representations defines the
quotient relation used to choose one representative from each isomorphism class. -/
private abbrev representationIsoSetoid : Setoid ι :=
  { r := fun i j ↦ Nonempty ((π i).ρ.Equiv (π j).ρ)
    iseqv :=
      ⟨fun i ↦ ⟨Representation.Equiv.refl ((π i).ρ)⟩,
        fun {i j} hij ↦ by
          rcases hij with ⟨e⟩
          exact ⟨e.symm⟩,
        fun {i j l} hij hjl ↦ by
          rcases hij with ⟨eij⟩
          rcases hjl with ⟨ejl⟩
          exact ⟨eij.trans ejl⟩⟩ }

/-- Helper for Exercise 6-6.3-4: choose a concrete representative for each isomorphism class in
the complete family. -/
private abbrev quotientRepresentativeFamily :
    Quotient (representationIsoSetoid (π := π)) → Rep k G :=
  fun q ↦ π (Quotient.out q)

/-- Helper for Exercise 6-6.3-4: different quotient classes cannot label isomorphic chosen
representatives. -/
private theorem quotientRepresentativeFamily_pairwiseNonisomorphic :
    PairwiseNonisomorphic (quotientRepresentativeFamily (π := π)) := by
  -- Distinct quotient classes would coincide if their chosen representatives were isomorphic.
  intro q q' hqq' hIso
  rcases hIso with ⟨e⟩
  have hrel :
      Nonempty ((π (Quotient.out q)).ρ.Equiv (π (Quotient.out q')).ρ) := by
    simpa [quotientRepresentativeFamily] using
      (show
          Nonempty
            (((quotientRepresentativeFamily (π := π) q).ρ).Equiv
              ((quotientRepresentativeFamily (π := π) q').ρ)) from
        ⟨Representation.equivOfIso e⟩)
  have hclasses :
      (⟦Quotient.out q⟧ : Quotient (representationIsoSetoid (π := π))) =
        (⟦Quotient.out q'⟧ : Quotient (representationIsoSetoid (π := π))) :=
    Quotient.sound hrel
  apply hqq'
  calc
    q = (⟦Quotient.out q⟧ : Quotient (representationIsoSetoid (π := π))) :=
      (Quotient.out_eq q).symm
    _ = (⟦Quotient.out q'⟧ : Quotient (representationIsoSetoid (π := π))) := hclasses
    _ = q' := Quotient.out_eq q'

/-- Helper for Exercise 6-6.3-4: the chosen representative of the class of `i` remains equivalent
to the original representation indexed by `i`. -/
private theorem quotientRepresentativeFamily_equiv_original (i : ι) :
    Nonempty
      (((quotientRepresentativeFamily (π := π)
            (⟦i⟧ : Quotient (representationIsoSetoid (π := π)))).ρ).Equiv
        (π i).ρ) := by
  -- `Quotient.out` picks a representative of the class `⟦i⟧`, so it is equivalent to `i`.
  simpa [quotientRepresentativeFamily] using
    (Quotient.exact
      (Quotient.out_eq (⟦i⟧ : Quotient (representationIsoSetoid (π := π)))))

/-- Helper for Exercise 6-6.3-4: the quotient representative family is still complete and
irreducible after passing to one representative per isomorphism class. -/
private theorem quotientRepresentativeFamily_complete
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    IsCompleteIrreducibleFamily
      (fun q ↦ FDRep.of ((quotientRepresentativeFamily (π := π) q).ρ)) := by
  refine
    { isSimple := ?_
      exists_iso := ?_ }
  · intro q
    -- Each chosen representative is literally one member of the original complete family.
    simpa [quotientRepresentativeFamily] using hπ_complete.isSimple (Quotient.out q)
  · intro τ hτ
    -- First use completeness of the original family, then move the witness to its quotient class.
    obtain ⟨i, hi⟩ := hπ_complete.exists_iso τ hτ
    refine ⟨(⟦i⟧ : Quotient (representationIsoSetoid (π := π))), ?_⟩
    have hout :
        Nonempty
          (((quotientRepresentativeFamily (π := π)
                (⟦i⟧ : Quotient (representationIsoSetoid (π := π)))).ρ).Equiv
            (π i).ρ) :=
      quotientRepresentativeFamily_equiv_original (π := π) i
    rcases hout with ⟨hout⟩
    rcases hi with ⟨hi⟩
    simpa [quotientRepresentativeFamily] using ⟨hi.trans hout.toFDRepIso.symm⟩

-- Proof sketch: first replace the complete family by a complete pairwise nonisomorphic
-- representative subfamily; then apply
-- `exists_centralCharacter_of_pairwise_complete_irreducible_family` and transport the resulting
-- central-character identity back along the chosen isomorphism into the original family.
/-- Exercise 6-6.3-4: for a complete family of irreducible finite-dimensional representations of a
finite group over an algebraically closed field in which `|G|` is invertible, every `k`-algebra
homomorphism from the center of `k[G]` to `k` is the central character of one member of the
family. -/
theorem exists_centralCharacter_of_complete_irreducible_family
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (η : Subalgebra.center k (k[G]) →ₐ[k] k) :
    ∃ i,
      let _ : (π i).ρ.IsIrreducible :=
        IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
      ω[(π i).ρ] = η := by
  classical
  let πq := quotientRepresentativeFamily (π := π)
  letI : ∀ q, FiniteDimensional k (πq q) :=
    fun q ↦ by
      simpa [πq, quotientRepresentativeFamily] using
        (inferInstance : FiniteDimensional k (π (Quotient.out q)))
  have hπq_pairwise : PairwiseNonisomorphic πq :=
    quotientRepresentativeFamily_pairwiseNonisomorphic (π := π)
  have hπq_complete :
      IsCompleteIrreducibleFamily (fun q ↦ FDRep.of (πq q).ρ) := by
    -- The quotient family keeps exactly one representative from each original isomorphism class.
    simpa [πq] using quotientRepresentativeFamily_complete (π := π) hπ_complete
  -- Apply the pairwise theorem to the quotient family and return its chosen original index.
  obtain ⟨q, hq⟩ :=
    exists_centralCharacter_of_pairwise_complete_irreducible_family
      (π := πq) hπq_pairwise hπq_complete η
  refine ⟨Quotient.out q, ?_⟩
  simpa [πq, quotientRepresentativeFamily] using hq

-- Proof sketch: use the central-character form of Exercise `6-6.3-4`, then translate it to the
-- scalar-action statement via Proposition `asAlgebraHom_center_eq_centralCharacter_smul_id`.
/-- Scalar-action reformulation of
`exists_centralCharacter_of_complete_irreducible_family`. -/
theorem exists_centralCharacter_action_of_complete_irreducible_family
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (η : Subalgebra.center k (k[G]) →ₐ[k] k) :
    ∃ i,
      ∀ u : Subalgebra.center k (k[G]),
        (π i).ρ.asAlgebraHom u = η u • LinearMap.id := by
  obtain ⟨i, hi⟩ := exists_centralCharacter_of_complete_irreducible_family π hπ_complete η
  refine ⟨i, ?_⟩
  letI : (π i).ρ.IsIrreducible := IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  have hi' : ω[(π i).ρ] = η := hi
  intro u
  have hiu : ω[(π i).ρ] u = η u := by
    simpa using congrArg (fun f : Subalgebra.center k (k[G]) →ₐ[k] k ↦ f u) hi'
  rw [← hiu]
  exact asAlgebraHom_center_eq_centralCharacter_smul_id (π i).ρ u

end

end Representation

/-! ### Proposition_6_6_3_1 (from Chap06) -/
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

/-! ### Proposition_6_6_3_2 (from Chap06) -/
open scoped MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {k G : Type u} {ι : Type v} [Field k] [IsAlgClosed k]
variable [Monoid G]
variable (π : ι → Rep k G)
variable [∀ i, FiniteDimensional k (π i)]

/-- The source-facing product algebra homomorphism whose `i`-th coordinate is the central
character of `π i`. This is the thin bridge from the family of central characters to the canonical
product owner `Pi.algHom`. -/
abbrev centralCharacterFamilyAlgHom
    (hπ_irreducible : ∀ i, (π i).ρ.IsIrreducible)
    : Subalgebra.center k (k[G]) →ₐ[k] (ι → k) :=
  Pi.algHom k (fun _ : ι ↦ k) fun i ↦
    letI := hπ_irreducible i
    ω[(π i).ρ]

-- Proof sketch: for a central element `u`, the `i`-th component of the canonical Wedderburn map
-- is `(π i).ρ.asAlgebraHom u`; Proposition `asAlgebraHom_center_eq_centralCharacter_smul_id`
-- identifies this endomorphism with the scalar `ω[(π i).ρ] u` times the identity.
/-- On central elements, the `i`-th factor of the canonical Wedderburn map is scalar
multiplication by the `i`-th value of the central-character family map. -/
@[simp] theorem familyEndAlgHom_center_apply
    (hπ_irreducible : ∀ i, (π i).ρ.IsIrreducible)
    (u : Subalgebra.center k (k[G])) (i : ι) :
    (ρ̃[π]) u i = centralCharacterFamilyAlgHom π hπ_irreducible u i • LinearMap.id := by
  -- Read the `i`-th coordinate of the product map and then apply Proposition `6-6.3-1`.
  simpa [centralCharacterFamilyAlgHom, familyEndAlgHom] using
    asAlgebraHom_center_eq_centralCharacter_smul_id ((π i).ρ) u

end

section

variable {k G : Type u} {ι : Type v} [Field k] [IsAlgClosed k]
variable [Group G] [Finite G] [Invertible (Nat.card G : k)]
variable (π : ι → Rep k G)
variable [∀ i, FiniteDimensional k (π i)]

/-- Helper for Proposition 6-6.3-2: if the canonical Wedderburn image of a group-algebra element
is a family of homotheties, then the element itself lies in the center. -/
lemma mem_center_of_familyEndAlgHom_eq_smul_id
    (hinj : Function.Injective (ρ̃[π])) {x : k[G]} {a : ι → k}
    (hx : (ρ̃[π]) x = fun i ↦ a i • LinearMap.id) :
    x ∈ Subalgebra.center k (k[G]) := by
  -- Pull commutativity of the scalar family back through the injective Wedderburn map.
  rw [Subalgebra.mem_center_iff]
  intro y
  apply hinj
  ext i v
  have hxi : (π i).ρ.asAlgebraHom x = a i • LinearMap.id := by
    simpa [familyEndAlgHom] using congrArg (fun f : (∀ j, Module.End k (π j)) ↦ f i) hx
  -- Each scalar endomorphism commutes with every endomorphism on the `i`-th factor.
  simp [familyEndAlgHom, map_mul, hxi, Module.End.mul_apply]

-- Proof sketch: combine Proposition `irreducibleFamilyEndAlgHom_bijective` with the restriction of
-- the Wedderburn isomorphism to the center. Proposition
-- `asAlgebraHom_center_eq_centralCharacter_smul_id`
-- identifies the scalar on the `i`-th simple factor with the central character of the `i`-th
-- member of the complete family,
-- and Schur's lemma identifies the center of `Module.End k (π i)` with `k`.
/-- The product of the central characters furnished by a complete pairwise nonisomorphic
irreducible family is bijective on the center of `k[G]`. -/
theorem centralCharacterFamilyAlgHom_bijective
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Function.Bijective
      (centralCharacterFamilyAlgHom π
        (fun i ↦ IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i)) := by
  let hπ_irreducible : ∀ i, (π i).ρ.IsIrreducible :=
    fun i ↦ IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  let hρ := irreducibleFamilyEndAlgHom_bijective π hπ_pairwise hπ_complete
  constructor
  · intro u v huv
    -- Compare the two central elements through the injective Wedderburn map.
    apply Subtype.ext
    apply hρ.1
    ext i x
    rw [familyEndAlgHom_center_apply (π := π) hπ_irreducible u i,
      familyEndAlgHom_center_apply (π := π) hπ_irreducible v i]
    have hcoord :
        centralCharacterFamilyAlgHom π hπ_irreducible u i =
          centralCharacterFamilyAlgHom π hπ_irreducible v i := by
      simpa using congrArg (fun f : ι → k ↦ f i) huv
    rw [hcoord]
  · intro a
    -- Lift the scalar family through the surjective Wedderburn map.
    obtain ⟨x, hx⟩ := hρ.2 (fun i ↦ a i • LinearMap.id)
    let u : Subalgebra.center k (k[G]) :=
      ⟨x, mem_center_of_familyEndAlgHom_eq_smul_id (π := π) hρ.1 hx⟩
    refine ⟨u, ?_⟩
    ext i
    letI : (π i).ρ.IsIrreducible := hπ_irreducible i
    letI : Nontrivial (π i) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hV
      have htop : (⊤ : Subrepresentation (π i).ρ).toSubmodule = ⊥ := by
        apply le_antisymm
        · intro x hx
          change x = 0
          exact hV.elim x 0
        · exact bot_le
      have hEq : (⊤ : Subrepresentation (π i).ρ) = ⊥ :=
        Subrepresentation.toSubmodule_injective htop
      exact bot_ne_top hEq.symm
    -- Compare the two scalar endomorphisms on the `i`-th factor and cancel `LinearMap.id`.
    have hcoord :
        centralCharacterFamilyAlgHom π hπ_irreducible u i •
            (LinearMap.id : Module.End k (π i)) =
          a i • (LinearMap.id : Module.End k (π i)) := by
      calc
        centralCharacterFamilyAlgHom π hπ_irreducible u i •
            (LinearMap.id : Module.End k (π i)) =
          (ρ̃[π]) u i := by
          symm
          exact familyEndAlgHom_center_apply (π := π) hπ_irreducible u i
        _ = a i • (LinearMap.id : Module.End k (π i)) := by
          simpa [u] using congrArg (fun f : (∀ j, Module.End k (π j)) ↦ f i) hx
    have hscalar : centralCharacterFamilyAlgHom π hπ_irreducible u i = a i := by
      apply sub_eq_zero.mp
      have hid_ne : (LinearMap.id : Module.End k (π i)) ≠ 0 := by
        intro hid
        obtain ⟨x, hx⟩ := exists_ne (0 : π i)
        exact hx <| by
          simpa using congrArg (fun f : Module.End k (π i) ↦ f x) hid
      have hzero :
          (centralCharacterFamilyAlgHom π hπ_irreducible u i - a i) •
              (LinearMap.id : Module.End k (π i)) = 0 := by
        rw [sub_smul, hcoord, sub_self]
      exact (smul_eq_zero.mp hzero).resolve_right hid_ne
    exact hscalar

/-- Proposition 6-6.3-2: for a complete pairwise nonisomorphic family of irreducible
finite-dimensional representations over an algebraically closed field in which `|G|` is
invertible, the family of central characters yields an algebra isomorphism from the center of
`k[G]` onto the product algebra `ι → k`. Specializing to `k = ℂ` recovers LinearRepresentations_Serre_1977's original
statement `\mathbf{C}^h`. -/
def centralCharacterFamilyAlgEquiv
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    : Subalgebra.center k (k[G]) ≃ₐ[k] (ι → k) :=
  AlgEquiv.ofBijective
    (centralCharacterFamilyAlgHom π
      (fun i ↦ IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i))
    (centralCharacterFamilyAlgHom_bijective π hπ_pairwise hπ_complete)

-- Proof sketch: the underlying algebra homomorphism of `centralCharacterFamilyAlgEquiv` is
-- `centralCharacterFamilyAlgHom`, so the coordinate formula reduces to the defining `Pi.algHom`
-- coordinate formula for that bridge.
/-- The central-character equivalence acts by the source-facing product central-character map. -/
@[simp] theorem centralCharacterFamilyAlgEquiv_apply
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (u : Subalgebra.center k (k[G])) :
    centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete u =
      centralCharacterFamilyAlgHom π
        (fun i ↦ IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i) u := by
  -- The packaged equivalence was built from `AlgEquiv.ofBijective`, so its forward map is
  -- definitionally the original product central-character homomorphism.
  rfl

end

end Representation

/-! ### Corollary_6_6_4_2 (from Chap06) -/
universe u

section

variable {R : Type u} [Ring R] [Module.Finite ℤ R]

-- Source/core/bridge triage:
-- * source-facing: Corollary 6-6.4-2, specialized to the base ring `ℤ`.
-- * core/canonical owner: `Algebra.IsIntegral ℤ R`.
-- * bridge/view: the elementwise theorem `IsIntegral.of_finite ℤ`.
-- Primitive data are only the finite `ℤ`-module structure on `R`; elementwise integrality is
-- derived canonically from the ambient integral-extension owner.
/- Corollary 6-6.4-2: if a ring is finitely generated as a `ℤ`-module, then it is an integral
extension of `ℤ`, so in particular each of its elements is integral over `ℤ`. This is the
integer-base specialization of the canonical owner instance `Algebra.IsIntegral.of_finite`. -/
#check (Algebra.IsIntegral.of_finite ℤ R : Algebra.IsIntegral ℤ R)

end

/-! ### Corollary_6_6_4_3 (from Chap06) -/
universe u

section

-- Source/core/bridge triage:
-- * source-facing: the subring of elements of `R` integral over `ℤ`.
-- * core/canonical: `integralClosure ℤ R : Subalgebra ℤ R`.
-- * bridge/view: `Subalgebra.toSubring`.
-- Primitive data live in the owner `integralClosure ℤ R`; the membership characterization is
-- already derived canonically by `mem_integralClosure_iff` and `Subalgebra.mem_toSubring`.

variable {R : Type u} [CommRing R]

/- Corollary 6-6.4-3: the elements of a commutative ring that are integral over `ℤ` form a
subring. This is the canonical subring view of `integralClosure ℤ R`. -/
#check (integralClosure ℤ R).toSubring

end

/-! ### Proposition_6_6_4_1 (from Chap06) -/
universe u

open scoped Algebra

section

variable {R : Type u} [Ring R]

-- Source/core/bridge triage:
-- * source-facing: Proposition 6-6.4-1, specialized to the base ring `ℤ`.
-- * core/canonical owner: the simple adjoin `ℤ[x]`, with mathlib owner theorem
--   `Algebra.finite_adjoin_simple_of_isIntegral`.
-- * bridge/view: `isIntegral_tfae_finite_adjoin_simple`, which packages the textbook three-way
--   equivalence without introducing a parallel local owner.
/- Proposition 6-6.4-1: for `x` in a ring, the following are equivalent: `x` is integral over
`ℤ`; the simple subring `ℤ[x]` is finitely generated as a `ℤ`-module; and `ℤ[x]` is contained in
a finitely generated `ℤ`-submodule of the ambient ring. In the current API, this is the
integer-base specialization of the general theorem
`isIntegral_tfae_finite_adjoin_simple`. -/
#check
  (isIntegral_tfae_finite_adjoin_simple ℤ :
    ∀ x : R,
      [IsIntegral ℤ x,
        Module.Finite ℤ ℤ[x],
        ∃ M : Submodule ℤ R,
          Module.Finite ℤ M ∧ ℤ[x].toSubmodule ≤ M].TFAE)

end

/-! ### Remark_6_6_4_4 (from Chap06) -/
open scoped Algebra

universe u v

section

/-- Remark 6-6.4-4: after replacing `ℤ` by an arbitrary commutative noetherian ring, the three
conditions from Proposition 6-6.4-1 remain equivalent for elements of any ring algebra over that
base. -/
lemma isIntegral_tfae_finite_adjoin_simple (A : Type u) {B : Type v}
    [CommRing A] [Ring B] [Algebra A B] [IsNoetherianRing A] (x : B) :
    [IsIntegral A x,
      Module.Finite A A[x],
      ∃ M : Submodule A B,
        Module.Finite A M ∧ A[x].toSubmodule ≤ M].TFAE := by
  tfae_have 1 → 2 := Algebra.finite_adjoin_simple_of_isIntegral
  tfae_have 2 → 1 := by
    intro h
    letI : Module.Finite A A[x].toSubmodule :=
      Module.Finite.equiv (Subalgebra.toSubmoduleEquiv A[x]).symm
    exact IsIntegral.of_mem_of_fg A[x] Submodule.FG.of_finite x
      (Algebra.self_mem_adjoin_singleton A x)
  tfae_have 2 → 3 := fun h ↦
    ⟨A[x].toSubmodule, by simpa using h, le_rfl⟩
  tfae_have 3 → 2 := by
    rintro ⟨M, hM, hle⟩
    letI : Module.Finite A M := hM
    simpa using Module.Finite.of_fg ((Submodule.FG.of_finite : M.FG).of_le hle)
  tfae_finish

end

/-! ### Corollary_6_6_5_3 (from Chap06) -/
open scoped BigOperators MonoidAlgebra Representation

noncomputable section

universe u v

namespace Representation

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]

local instance fintypeGCor6653 : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: `isIntegral_finrank_inv_sum_coeff_mul_character`.
-- * core/canonical owner: the central character `ω[ρ]`.
-- * upstream derived API: `IsIrreducible.finiteDimensional_of_finite ρ` supplies the
--   finite-dimensional structure required to evaluate `ω[ρ]` and `Module.finrank k V`.
-- * upstream derived API: the trace formula `centralCharacter_apply_eq_sum_character`, the
--   center-valued bridge `MonoidAlgebra.isIntegral_center_of_coeff_isIntegral`, and the canonical
--   transport theorem `map_isIntegral_int`.
-- Primitive data: the irreducible representation `ρ`, a central element
-- `u : Subalgebra.center k (k[G])`, and the coefficientwise integrality hypothesis `hu`.
-- Derived API: map that integrality along `ω[ρ]`, and then rewrite the result by the normalized
-- trace formula. Finite-dimensionality is derived internally from irreducibility because `G` is
-- finite.

/-- Corollary 6-6.5-3: if `ρ` is an irreducible representation of `G` over an algebraically
closed field `k`, and `u` is a central element of `k[G]` whose
coefficients are algebraic integers, then the
normalized sum of the coefficients of `u` weighted by the character of `ρ` is an algebraic
integer. For finite `G`, finite-dimensionality is automatic. -/
theorem isIntegral_finrank_inv_sum_coeff_mul_character
    (u : Subalgebra.center k (k[G])) (hu : ∀ s : G, IsIntegral ℤ ((u : k[G]) s)) :
    IsIntegral ℤ
      ((Module.finrank k V : k)⁻¹ *
        ∑ s : G, (u : k[G]) s * ρ.character s) := by
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
  by_cases hfinrank : (Module.finrank k V : k) = 0
  -- When the rank vanishes in `k`, the normalized scalar is literally zero.
  · simpa [hfinrank] using (isIntegral_zero : IsIntegral ℤ (0 : k))
  -- Otherwise, transport integrality through `ω[ρ]` and rewrite its value by the trace formula.
  · simpa [centralCharacter_apply_eq_sum_character ρ u hfinrank] using
      map_isIntegral_int (ω[ρ])
        (MonoidAlgebra.isIntegral_center_of_coeff_isIntegral u hu)

end

end Representation

/-! ### Corollary_6_6_5_4 (from Chap06) -/
open scoped BigOperators MonoidAlgebra Representation

noncomputable section

universe u v

namespace Representation

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module k V]

/-- Helper for Corollary 6-6.5-4: the inverse character of a finite-dimensional representation is
a class function. -/
lemma inverse_character_mem_classFunctionSubmodule [FiniteDimensional k V]
    (ρ : Representation k G V) :
    (fun s : G ↦ ρ.character s⁻¹) ∈ classFunctionSubmodule k G := by
  -- Conjugate elements have conjugate inverses, so the inverse character stays constant on
  -- conjugacy classes.
  rw [mem_classFunctionSubmodule_iff]
  refine ⟨?_⟩
  intro a b hab
  rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab) with ⟨g, hg⟩
  calc
    ρ.character a⁻¹ = ρ.character (g * a⁻¹ * g⁻¹) := by
      exact (ρ.char_conj a⁻¹ g).symm
    _ = ρ.character b⁻¹ := by
      -- Rewrite the conjugate of `a⁻¹` as `b⁻¹`.
      have hinv : g * a⁻¹ * g⁻¹ = b⁻¹ := by
        rw [← hg]
        simp [mul_assoc]
      simp [hinv]

end

section

variable {k : Type*} [Field k] [CharZero k]

/-- Helper for Corollary 6-6.5-4: if `(m : k) / n` is integral over `ℤ`, then `n` divides `m`.
-/
lemma nat_dvd_of_isIntegral_natCast_div (m n : ℕ) (hn : n ≠ 0)
    (h : IsIntegral ℤ ((m : k) / n)) :
    n ∣ m := by
  let q : ℚ := m / n
  have hq : IsIntegral ℤ q := by
    -- Descend integrality from the ambient field to the rational scalar itself.
    have hqk : IsIntegral ℤ (q : k) := by
      simpa [q] using h
    exact IsIntegral.ratCast_iff.mp hqk
  obtain ⟨z, hz : q = z⟩ := hq.exists_int_iff_exists_rat |>.mp ⟨q, rfl⟩
  have hden : q.den = 1 := by
    -- Once the rational is an integer, its denominator is `1`.
    rw [hz]
    simp
  exact (Rat.den_div_natCast_eq_one_iff m n hn).mp <| by
    simpa [q] using hden

end

section

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V]

-- Source/core/bridge triage: this corollary is source-facing. The core owner declarations reused
-- in the proof are the Chapter 6 center/class-function equivalence `centerClassFunctionEquiv`, the
-- Chapter 6 integrality theorem `isIntegral_finrank_inv_sum_coeff_mul_character`, and the mathlib
-- owner theorem `Representation.IsIrreducible.finrank_intertwiningMap_self`, applied through the
-- canonical character-pairing identity `card_inv_mul_sum_char_mul_char_eq_finrank`.
--
-- Primitive data: only the irreducible representation `ρ`; the group-algebra element used in the
-- proof is derived canonically from the class function `s ↦ ρ.character s⁻¹`.
-- Derived API: coefficientwise integrality from `char_isIntegral_of_isOfFinOrder`, then
-- `isIntegral_finrank_inv_sum_coeff_mul_character`, then the canonical character self-pairing.
--
-- Proof sketch: view `s ↦ ρ.character s⁻¹` as a class function and transport it through
-- `centerClassFunctionEquiv` to the corresponding central group-algebra element
-- `u = ∑ s : G, ρ.character s⁻¹ • s`, whose coefficients are algebraic integers by
-- Proposition `6-6.5-1`. Corollary `6-6.5-3` then shows that the scalar
-- `(Nat.card G : k) / Module.finrank k V` is an algebraic integer. Since this scalar is rational,
-- it is an integer, which is equivalent to `Module.finrank k V ∣ Nat.card G`.
/-- Corollary 6-6.5-4: the degree of an irreducible finite-dimensional representation of a finite
group over an algebraically closed field of characteristic zero divides the order of the group. -/
theorem finrank_dvd_card (ρ : Representation k G V) [ρ.IsIrreducible] :
    Module.finrank k V ∣ Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  -- Install the finite-dimensional and simple-module instances needed by the Chapter 6 API.
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Module k[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule k[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial k[G] V
  have hfinrank_ne_zero : (Module.finrank k V : k) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt Module.finrank_pos
  letI : NeZero (Module.finrank k V : k) := ⟨hfinrank_ne_zero⟩
  have hcard_ne_zero : (Nat.card G : k) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero hcard_ne_zero
  let f : classFunctionSubmodule k G :=
    ⟨fun s ↦ ρ.character s⁻¹, inverse_character_mem_classFunctionSubmodule ρ⟩
  let u : Subalgebra.center k (k[G]) :=
    (centerClassFunctionEquiv k).symm f
  have hu : ∀ s : G, ((u : k[G]) s) = ρ.character s⁻¹ := by
    -- The coefficients of the central element `u` are exactly the inverse character values.
    intro s
    rfl
  have hcoeff : ∀ s : G, IsIntegral ℤ ((u : k[G]) s) := by
    -- Proposition `6-6.5-1` gives algebraic integrality of each inverse character coefficient.
    intro s
    rw [hu s]
    exact char_isIntegral_of_isOfFinOrder ρ (isOfFinOrder_of_finite s⁻¹)
  have hsum : ∑ s : G, ρ.character s⁻¹ * ρ.character s = Nat.card G := by
    -- Orthogonality identifies the normalized self-pairing with the self-intertwining rank.
    have hpair :
        (Nat.card G : k)⁻¹ * ∑ s : G, ρ.character s⁻¹ * ρ.character s = 1 := by
      simpa [mul_comm, IsIrreducible.finrank_intertwiningMap_self ρ] using
        (card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ)
    field_simp [hcard_ne_zero] at hpair
    simpa using hpair
  have hint :
      IsIntegral ℤ ((Nat.card G : k) / Module.finrank k V) := by
    have hint_raw := isIntegral_finrank_inv_sum_coeff_mul_character ρ u hcoeff
    have hsum' :
        (Module.finrank k V : k)⁻¹ * ∑ s : G, (u : k[G]) s * ρ.character s =
          (Nat.card G : k) / Module.finrank k V := by
      -- Rewrite Corollary `6-6.5-3` using the explicit coefficients of `u` and the self-pairing
      -- identity for `ρ.character`.
      calc
        (Module.finrank k V : k)⁻¹ * ∑ s : G, (u : k[G]) s * ρ.character s
          = (Module.finrank k V : k)⁻¹ * ∑ s : G, ρ.character s⁻¹ * ρ.character s := by
              simp [hu]
        _ = (Module.finrank k V : k)⁻¹ * Nat.card G := by rw [hsum]
        _ = (Nat.card G : k) / Module.finrank k V := by
              simp [div_eq_mul_inv, mul_comm]
    rw [hsum'] at hint_raw
    exact hint_raw
  -- A rational algebraic integer is an integer, so the denominator `dim V` divides `|G|`.
  exact nat_dvd_of_isIntegral_natCast_div
    (Nat.card G) (Module.finrank k V) (Nat.ne_of_gt Module.finrank_pos) hint

end

end Representation

/-! ### Exercise_6_6_5_10 (from Chap06) -/
namespace Representation

/-
Domain-style sampling:
* primary domain: finite-group character theory and complex representation theory.
* sampled owner declarations in this domain:
  `exists_irreducible_rep_with_character_ne_zero_of_conjClass_card_eq_prime_pow`,
  `exists_smul_id_of_prime_pow_conjClass_card_of_character_ne_zero`,
  `quotient_mk_mem_center_of_exists_smul_id`.
* best owner abstraction: the existing Chapter `6` owner theorems already formalized in
  `LinearRepresentations_Serre_1977.Chap06.Exercise_6_6_5_10`.

Primitive data versus derived API:
* primitive source-facing data: the prime-power conjugacy-class hypothesis and the resulting
  irreducible-character existence statement.
* derived API: the scalar-action and quotient-centrality consequences attached to the same exercise.

Source/core/bridge triage:
* `source-facing`: Exercise `6-6.5-10` itself.
* `core/canonical`: the existing Chapter `6` theorem declarations of the same names.
* `bridge/view`: the two consequence theorems, which remain direct recalls rather than parallel
  redeclarations.
-/

/- Exercise 6-6.5-10: the source-facing existence statement already has the correct public owner in
`LinearRepresentations_Serre_1977.Chap06.Exercise_6_6_5_10`, so this file reuses it directly. -/
recall exists_irreducible_rep_with_character_ne_zero_of_conjClass_card_eq_prime_pow

end Representation

/-! ### Exercise_6_6_5_6 (from Chap06) -/
open scoped MonoidAlgebra

universe u

section

variable (k : Type*) [CommSemiring k]
variable {G : Type u} [Group G] [Finite G]

/-- The class sum in `k[G]` attached to a conjugacy class, obtained from its indicator function. -/
noncomputable def conjugacyClassSum (c : ConjClasses G) : k[G] :=
  Finsupp.equivFunOnFinite.symm c.indicator

@[simp] theorem conjugacyClassSum_apply (c : ConjClasses G) (g : G) :
    conjugacyClassSum k c g = (c.indicator : G → k) g := by
  rfl

/-- A class function defines a central element of `k[G]`. -/
theorem mem_center_of_classFunction (f : classFunctionSubmodule k G) :
    Finsupp.equivFunOnFinite.symm (f : G → k) ∈ Subalgebra.center k (k[G]) := by
  have hf : IsClassFunction (f : G → k) := by
    exact (mem_classFunctionSubmodule_iff k _).1 f.2
  set z : k[G] := Finsupp.equivFunOnFinite.symm (f : G → k)
  change z ∈ Subsemiring.center k[G]
  rw [Subsemiring.mem_center_iff]
  intro y
  ext h
  rw [MonoidAlgebra.mul_apply_left, MonoidAlgebra.mul_apply_right]
  rw [Finsupp.sum, Finsupp.sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have hcomm : (f : G → k) (a⁻¹ * h) = (f : G → k) (h * a⁻¹) :=
    hf.map_mul_comm a⁻¹ h
  simpa [z, mul_comm] using congrArg (fun t : k ↦ y a * t) hcomm

/-- Each conjugacy-class sum lies in the center of `k[G]`. -/
theorem conjugacyClassSum_mem_center (c : ConjClasses G) :
    conjugacyClassSum k c ∈ Subalgebra.center k (k[G]) :=
  mem_center_of_classFunction k
    ⟨c.indicator, (mem_classFunctionSubmodule_iff k _).2 inferInstance⟩

/-- The conjugacy-class sum attached to `c`, regarded as an element of the center of `k[G]`. -/
noncomputable abbrev conjugacyClassSumInCenter (c : ConjClasses G) :
    Subalgebra.center k (k[G]) :=
  ⟨conjugacyClassSum k c, conjugacyClassSum_mem_center k c⟩

@[simp] theorem coe_conjugacyClassSumInCenter (c : ConjClasses G) :
    (conjugacyClassSumInCenter k c : k[G]) = conjugacyClassSum k c :=
  rfl

/-- The coefficient-function map identifies the center of `k[G]` with the `k`-module of
class functions on `G`. -/
noncomputable def centerClassFunctionEquiv :
    Subalgebra.center k (k[G]) ≃ₗ[k] classFunctionSubmodule k G where
  toFun u :=
    ⟨fun g ↦ (u : k[G]) g, Representation.coeff_isClassFunction_of_mem_center u⟩
  invFun f :=
    ⟨Finsupp.equivFunOnFinite.symm (f : G → k), mem_center_of_classFunction k f⟩
  left_inv u := by
    ext g
    simp
  right_inv f := by
    ext g
    simp
  map_add' u v := by
    ext g
    rfl
  map_smul' n u := by
    ext g
    rfl

/-- The center of `k[G]` is canonically identified with `k`-valued functions on the conjugacy
classes of `G`. -/
noncomputable def centerCoeffEquivFun :
    Subalgebra.center k (k[G]) ≃ₗ[k] (ConjClasses G → k) :=
  (centerClassFunctionEquiv k).trans (classFunctionSubmodule.equivFun k G)

@[simp] theorem centerCoeffEquivFun_apply_mk
    (u : Subalgebra.center k (k[G])) (g : G) :
    centerCoeffEquivFun k u (ConjClasses.mk g) = (u : k[G]) g := by
  rfl

@[simp] theorem centerCoeffEquivFun_conjugacyClassSumInCenter_apply_mk
    (c : ConjClasses G) (g : G) :
    centerCoeffEquivFun k (conjugacyClassSumInCenter k c) (ConjClasses.mk g) =
      (c.indicator : G → k) g := by
  simp [centerCoeffEquivFun_apply_mk, conjugacyClassSum_apply]

/-- The conjugacy-class sums form the canonical `k`-basis of the center of `k[G]`, indexed by the
conjugacy classes of `G`. -/
noncomputable def conjugacyClassSumBasis :
    Module.Basis (ConjClasses G) k (Subalgebra.center k (k[G])) :=
  Module.Basis.ofEquivFun (centerCoeffEquivFun k)

@[simp] theorem centerCoeffEquivFun_conjugacyClassSumInCenter_self (c : ConjClasses G) :
    centerCoeffEquivFun k (conjugacyClassSumInCenter k c) c = 1 := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  have h1 : ((ConjClasses.mk g).indicator : G → k) g = 1 := by
    simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq]
  simpa [centerCoeffEquivFun_apply_mk, conjugacyClassSum_apply] using h1

@[simp] theorem centerCoeffEquivFun_conjugacyClassSumInCenter_of_ne
    {c c' : ConjClasses G} (h : c' ≠ c) :
    centerCoeffEquivFun k (conjugacyClassSumInCenter k c) c' = 0 := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c'
  have h0 : (c.indicator : G → k) g = 0 := by
    simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq, h]
  simpa [centerCoeffEquivFun_apply_mk, conjugacyClassSum_apply] using h0

@[simp] theorem conjugacyClassSumBasis_apply (c : ConjClasses G) :
    conjugacyClassSumBasis k c = conjugacyClassSumInCenter k c := by
  classical
  apply (centerCoeffEquivFun k).injective
  funext c'
  by_cases h : c' = c
  · subst h
    simp [conjugacyClassSumBasis]
  · simp [conjugacyClassSumBasis, h]

end

section

variable {G : Type u} [Group G] [Finite G]

/-- Companion reformulation of Exercise 6-6.5-6 in span form. -/
theorem center_intGroupRing_eq_span_conjugacyClassSum :
    Submodule.span ℤ (Set.range (conjugacyClassSum ℤ : ConjClasses G → ℤ[G])) =
      (Subalgebra.center ℤ (ℤ[G])).toSubmodule := by
  let Z : Subalgebra ℤ (ℤ[G]) := Subalgebra.center ℤ (ℤ[G])
  let i : Z →ₗ[ℤ] ℤ[G] := Z.toSubmodule.subtype
  -- The conjugacy-class sums already form a basis of the center, so they span all of it there.
  have hbasisRange :
      Set.range (conjugacyClassSumInCenter ℤ : ConjClasses G → Z) =
        Set.range (conjugacyClassSumBasis (G := G) (k := ℤ) : ConjClasses G → Z) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, conjugacyClassSumBasis_apply (G := G) (k := ℤ) c⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, (conjugacyClassSumBasis_apply (G := G) (k := ℤ) c).symm⟩
  have hspan :
      Submodule.span ℤ
          (Set.range
            (conjugacyClassSumInCenter ℤ :
              ConjClasses G → Z)) = ⊤ := by
    rw [hbasisRange]
    exact (conjugacyClassSumBasis (G := G) (k := ℤ)).span_eq
  -- Mapping those generators through the center subtype gives exactly the ambient class sums.
  have himage :
      i '' Set.range (conjugacyClassSumInCenter ℤ : ConjClasses G → Z) =
        Set.range (conjugacyClassSum ℤ : ConjClasses G → ℤ[G]) := by
    ext x
    constructor
    · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
      refine ⟨c, ?_⟩
      show conjugacyClassSum ℤ c = i (conjugacyClassSumInCenter ℤ c)
      change conjugacyClassSum ℤ c = ((conjugacyClassSumInCenter ℤ c : Z) : ℤ[G])
      exact (coe_conjugacyClassSumInCenter (k := ℤ) c).symm
    · rintro ⟨c, rfl⟩
      exact ⟨conjugacyClassSumInCenter ℤ c, ⟨c, rfl⟩, by
        show i (conjugacyClassSumInCenter ℤ c) = conjugacyClassSum ℤ c
        change ((conjugacyClassSumInCenter ℤ c : Z) : ℤ[G]) = conjugacyClassSum ℤ c
        exact coe_conjugacyClassSumInCenter (k := ℤ) c⟩
  -- Transport the spanning statement from the center to the ambient group ring.
  calc
    Submodule.span ℤ (Set.range (conjugacyClassSum ℤ : ConjClasses G → ℤ[G]))
        = Submodule.map i
            (Submodule.span ℤ
              (Set.range
                (conjugacyClassSumInCenter ℤ :
                  ConjClasses G → Z))) := by
            rw [Submodule.map_span, himage]
    _ = Submodule.map i ⊤ := by
      rw [hspan]
    _ = Z.toSubmodule := by
      rw [Submodule.map_top]
      simpa only [i] using (Submodule.range_subtype Z.toSubmodule)
    _ = (Subalgebra.center ℤ (ℤ[G])).toSubmodule := by
      rfl

end

/-! ### Exercise_6_6_5_7 (from Chap06) -/
universe u v

namespace Representation

section

open Module.End Polynomial

variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

-- Source/core/bridge triage:
-- * source-facing: the Chapter 6 character bounds for a finite-order element of a
--   finite-dimensional complex representation.
-- * core/canonical owner: `Representation ℂ G V`, together with the canonical character owner
--   `Representation.character` and the identity-value theorem `Representation.char_one`.
-- * bridge/view: scalar-action consequences are exposed as theorem-level API, not as packaged
--   auxiliary data.
--
-- Primitive data: the representation `ρ`, the element `s`, and the finite-order hypothesis `hs`.
-- Derived API: the equality-to-identity criterion is the character-at-`1` reformulation of the
-- scalar-action equality case.

private lemma charpoly_root_pow_orderOf_eq_one_local
    (ρ : Representation ℂ G V) (s : G) {μ : ℂ}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    μ ^ orderOf s = 1 := by
  -- Push the finite-order relation from `s` to the endomorphism `ρ s`.
  have hρs_pow_eq_one : (ρ s) ^ orderOf s = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  -- Then push the eigenvalue relation through the same power.
  have hμeig : HasEigenvalue (ρ s) μ :=
    (hasEigenvalue_iff_isRoot_charpoly (ρ s) μ).2 <|
      (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).1 hμ
  have hμpow : HasEigenvalue (1 : Module.End ℂ V) (μ ^ orderOf s) := by
    simpa [hρs_pow_eq_one] using hμeig.pow (orderOf s)
  obtain ⟨v, hv⟩ := hμpow.exists_hasEigenvector
  -- A nonzero eigenvector for the identity forces the eigenvalue to be `1`.
  have hsmul : (μ ^ orderOf s - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← hv.apply_eq_smul]
    simp
  exact sub_eq_zero.mp <| (smul_eq_zero_iff_left hv.2).mp hsmul

/-- Helper for Exercise 6-6.5-7: every characteristic root of `ρ s` lies on the unit circle when
`s` has finite order. -/
lemma charpoly_root_norm_eq_one_of_isOfFinOrder
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s)
    {μ : ℂ} (hμ : μ ∈ (ρ s).charpoly.roots) :
    ‖μ‖ = 1 := by
  -- The previous helper reduces the norm statement to a root-of-unity calculation.
  have hpow : μ ^ orderOf s = 1 := charpoly_root_pow_orderOf_eq_one_local ρ s hμ
  exact Complex.norm_eq_one_of_pow_eq_one hpow hs.orderOf_pos.ne'

/-- Helper for Exercise 6-6.5-7: a sum of unit complex numbers has norm at most its cardinality. -/
lemma multiset_sum_norm_le_card_of_forall_norm_eq_one
    (zs : Multiset ℂ) (hz : ∀ z ∈ zs, ‖z‖ = 1) :
    ‖zs.sum‖ ≤ zs.card := by
  -- Apply the triangle inequality and then replace every summand norm by `1`.
  calc
    ‖zs.sum‖ ≤ (zs.map fun z ↦ ‖z‖).sum := norm_multiset_sum_le _
    _ = (zs.map fun _ ↦ (1 : ℝ)).sum := by
      refine congrArg Multiset.sum ?_
      exact Multiset.map_congr rfl fun z hz_mem ↦ by simpa using hz z hz_mem
    _ = zs.card := by simp

/-- Helper for Exercise 6-6.5-7: equality in the triangle inequality for a multiset of unit
complex numbers forces all entries to coincide. -/
lemma multiset_exists_eq_of_norm_sum_eq_card_of_forall_norm_eq_one
    (zs : Multiset ℂ) (hz : ∀ z ∈ zs, ‖z‖ = 1) (hsum : ‖zs.sum‖ = zs.card) :
    ∃ w : ℂ, ∀ z ∈ zs, z = w := by
  induction zs using Multiset.induction_on with
  | empty =>
      refine ⟨1, ?_⟩
      intro z hz_mem
      simp at hz_mem
  | @cons a zs ih =>
      by_cases hzs_zero : zs = 0
      · refine ⟨a, ?_⟩
        intro z hz_mem
        simp [hzs_zero] at hz_mem
        simp [hz_mem]
      have ha : ‖a‖ = 1 := hz a (by simp)
      have hz_tail : ∀ z ∈ zs, ‖z‖ = 1 := fun z hz_mem ↦ hz z (by simp [hz_mem])
      have hsum' : ‖a + zs.sum‖ = zs.card + 1 := by
        simpa using hsum
      have htail_le : ‖zs.sum‖ ≤ zs.card :=
        multiset_sum_norm_le_card_of_forall_norm_eq_one zs hz_tail
      have hnorm_add : ‖a + zs.sum‖ ≤ ‖a‖ + ‖zs.sum‖ := norm_add_le _ _
      -- Equality for the whole sum forces equality for the tail as well.
      have htail_eq : ‖zs.sum‖ = zs.card := by
        nlinarith [hsum', ha, htail_le, hnorm_add]
      have hadd_eq : ‖a + zs.sum‖ = ‖a‖ + ‖zs.sum‖ := by
        nlinarith [hsum', ha, htail_eq, hnorm_add]
      rcases ih hz_tail htail_eq with ⟨w, hw⟩
      -- Equality in the two-term triangle inequality shows `a` points in the same direction as
      -- the tail sum.
      have hsameray : SameRay ℝ a zs.sum :=
        (sameRay_iff_norm_add).2 <| by simpa using hadd_eq
      have hsameray_eq : zs.sum = ‖zs.sum‖ • a := by
        simpa [ha] using (sameRay_iff_norm_smul_eq).1 hsameray
      have hzs : zs = Multiset.replicate zs.card w :=
        (Multiset.eq_replicate_card).2 fun z hz_mem ↦ hw z hz_mem
      have hcard_pos : 0 < zs.card := by
        rw [Multiset.card_pos_iff_exists_mem]
        exact Multiset.exists_mem_of_ne_zero hzs_zero
      have hsum_tail : zs.sum = (zs.card : ℝ) • w := by
        rw [hzs]
        simp
      have hscalar_eq : (zs.card : ℝ) • w = (zs.card : ℝ) • a := by
        calc
          (zs.card : ℝ) • w = zs.sum := hsum_tail.symm
          _ = ‖zs.sum‖ • a := hsameray_eq
          _ = (zs.card : ℝ) • a := by rw [htail_eq]
      have hw_eq_a : w = a :=
        (smul_right_injective ℂ
          (show (zs.card : ℝ) ≠ 0 by exact_mod_cast hcard_pos.ne')).eq_iff.mp hscalar_eq
      refine ⟨w, ?_⟩
      intro z hz_mem
      rcases Multiset.mem_cons.1 hz_mem with rfl | hz_mem
      · exact hw_eq_a.symm
      · exact hw z hz_mem

/-- Helper for Exercise 6-6.5-7: a finite-order endomorphism over `ℂ` is semisimple. -/
lemma representation_isSemisimple_of_isOfFinOrder
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s) :
    Module.End.IsSemisimple (ρ s) := by
  -- The endomorphism is annihilated by `X ^ orderOf s - 1`.
  have hpow : (ρ s) ^ orderOf s = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hsep : ((X ^ orderOf s - (1 : ℂ[X]))).Separable := by
    rw [Polynomial.X_pow_sub_one_separable_iff]
    exact_mod_cast hs.orderOf_pos.ne'
  have haeval : Polynomial.aeval (ρ s) (X ^ orderOf s - (1 : ℂ[X])) = 0 := by
    simp [hpow]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree haeval

/-- Helper for Exercise 6-6.5-7: a semisimple complex endomorphism with only one eigenvalue is a
scalar endomorphism. -/
lemma eq_smul_id_of_isSemisimple_of_unique_eigenvalue
    {f : Module.End ℂ V} (hf : f.IsSemisimple)
    {z : ℂ} (hz : ∀ μ : ℂ, HasEigenvalue f μ → μ = z) :
    f = z • 1 := by
  -- Shift by `z`; then it suffices to show the shifted operator has only eigenvalue `0`.
  have hshift : (f - algebraMap ℂ (Module.End ℂ V) z).IsSemisimple :=
    (Module.End.isSemisimple_sub_algebraMap_iff (f := f) (μ := z)).2 hf
  have hzero : f - algebraMap ℂ (Module.End ℂ V) z = 0 := by
    refine (Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue hshift).2 ?_
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    -- An eigenvector for `f - z` with eigenvalue `μ` is an eigenvector for `f` with eigenvalue
    -- `μ + z`.
    have hv_mem : v ∈ f.eigenspace (μ + z) := by
      rw [mem_eigenspace_iff]
      calc
        f v =
            ((f - algebraMap ℂ (Module.End ℂ V) z) +
              algebraMap ℂ (Module.End ℂ V) z) v := by
              simp
        _ = ((f - algebraMap ℂ (Module.End ℂ V) z) v) +
              ((algebraMap ℂ (Module.End ℂ V) z) v) := by
              simp
        _ = μ • v + z • v := by simp [hv.apply_eq_smul]
        _ = (μ + z) • v := by simp [add_smul]
    have hf_eig : HasEigenvalue f (μ + z) := by
      rw [Module.End.hasEigenvalue_iff]
      exact (Submodule.ne_bot_iff _).2 ⟨v, hv_mem, hv.2⟩
    have hz' : μ + z = z := hz (μ + z) hf_eig
    exact add_right_cancel (show μ + z = 0 + z by simpa using hz')
  simpa [sub_eq_zero] using hzero

/-- The modulus of the character value of a finite-dimensional complex representation is bounded by
its degree, equivalently by its value at the identity via `Representation.char_one`. -/
-- Proof sketch: if `s` has finite order, then `ρ s` also has finite order. Over `ℂ`, the
-- eigenvalues of `ρ s` are roots of unity, hence all have modulus `1`, and `ρ.character s` is
-- their sum counted with multiplicity; the triangle inequality gives the bound.
theorem character_norm_le_char_one
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s) :
    ‖ρ.character s‖ ≤ Module.finrank ℂ V := by
  -- Rewrite the character as the sum of the characteristic roots.
  rw [Representation.character, trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  calc
    ‖(ρ s).charpoly.roots.sum‖ ≤ ((ρ s).charpoly.roots.map fun μ ↦ ‖μ‖).sum := by
      exact norm_multiset_sum_le _
    _ = ((ρ s).charpoly.roots.map fun _ ↦ (1 : ℝ)).sum := by
      refine congrArg Multiset.sum ?_
      exact Multiset.map_congr rfl fun μ hμ ↦ by
        simpa using charpoly_root_norm_eq_one_of_isOfFinOrder ρ s hs hμ
    _ = ((ρ s).charpoly.roots.card : ℝ) := by simp
    _ = (ρ s).charpoly.natDegree := by
      rw [← Polynomial.Splits.natDegree_eq_card_roots (f := (ρ s).charpoly) (IsAlgClosed.splits _)]
    _ = Module.finrank ℂ V := by
      simpa using (LinearMap.charpoly_natDegree (f := ρ s))

/-- Exercise 6-6.5-7: equality in the character bound occurs exactly when the representing
endomorphism is a homothety. -/
-- Proof sketch: write `ρ.character s` as the sum of the eigenvalues of `ρ s`, which are roots of
-- unity. Equality in the triangle inequality for a sum of complex numbers of modulus `1` holds
-- exactly when they all coincide, which says precisely that all eigenvalues of `ρ s` are equal and
-- therefore `ρ s` is a scalar endomorphism.
theorem character_norm_eq_char_one_iff_exists_smul_id
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s) :
    ‖ρ.character s‖ = Module.finrank ℂ V ↔ ∃ z : ℂ, ρ s = z • 1 := by
  constructor
  · intro hnorm
    -- Equality in the norm bound forces all characteristic roots to be equal.
    have hroots_sum : ‖(ρ s).charpoly.roots.sum‖ = ((ρ s).charpoly.roots.card : ℝ) := by
      calc
        ‖(ρ s).charpoly.roots.sum‖ = ‖ρ.character s‖ := by
          rw [Representation.character,
            trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
        _ = Module.finrank ℂ V := hnorm
        _ = (ρ s).charpoly.natDegree := by
          simpa using (LinearMap.charpoly_natDegree (f := ρ s)).symm
        _ = ((ρ s).charpoly.roots.card : ℝ) := by
          rw [Polynomial.Splits.natDegree_eq_card_roots (f := (ρ s).charpoly)
            (IsAlgClosed.splits _)]
    have hconst : ∃ z : ℂ, ∀ μ ∈ (ρ s).charpoly.roots, μ = z := by
      refine multiset_exists_eq_of_norm_sum_eq_card_of_forall_norm_eq_one _ ?_ hroots_sum
      intro μ hμ
      exact charpoly_root_norm_eq_one_of_isOfFinOrder ρ s hs hμ
    rcases hconst with ⟨z, hz⟩
    have hunique : ∀ μ : ℂ, HasEigenvalue (ρ s) μ → μ = z := by
      intro μ hμ
      have hroot : μ ∈ (ρ s).charpoly.roots := by
        refine (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).2 ?_
        exact (hasEigenvalue_iff_isRoot_charpoly (ρ s) μ).1 hμ
      exact hz μ hroot
    -- Route correction: the equality case is closed directly from the root geometry and
    -- semisimplicity of a finite-order operator, without importing later Chapter 6 items.
    exact ⟨z,
      eq_smul_id_of_isSemisimple_of_unique_eigenvalue
        (representation_isSemisimple_of_isOfFinOrder ρ s hs) hunique⟩
  · rintro ⟨z, hz⟩
    -- A scalar operator has character `z * dim`; in positive dimension `z` is itself an
    -- eigenvalue, so its norm is `1`.
    by_cases hdim : Module.finrank ℂ V = 0
    · simp [Representation.character, hz, hdim]
    · have hdim_pos : 0 < Module.finrank ℂ V := Nat.pos_of_ne_zero hdim
      have hz_eig : HasEigenvalue (ρ s) z := by
        rw [Module.End.hasEigenvalue_iff]
        rcases (Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := V)).1 hdim_pos with
          ⟨v, hv⟩
        exact (Submodule.ne_bot_iff _).2 ⟨v, by rw [mem_eigenspace_iff, hz]; simp, hv⟩
      have hz_root : z ∈ (ρ s).charpoly.roots :=
        (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).2 <|
          (hasEigenvalue_iff_isRoot_charpoly (ρ s) z).1 hz_eig
      have hz_norm : ‖z‖ = 1 := charpoly_root_norm_eq_one_of_isOfFinOrder ρ s hs hz_root
      have hchar : ρ.character s = z * Module.finrank ℂ V := by
        simp [Representation.character, hz]
      rw [hchar]
      simp [hz_norm]

/-- A finite-dimensional complex representation sends a finite-order element `s` to the identity
exactly when the character at `s` equals the degree of the representation, equivalently the
character at `1` via `Representation.char_one`. -/
-- Proof sketch: if `ρ s = 1`, then the character is the trace of the identity, hence the degree.
-- Conversely, if `ρ.character s = ρ.character 1`, then `Representation.char_one` rewrites this as
-- equality in the previous criterion, so `ρ s` is scalar; comparing traces shows that the scalar
-- is `1`.
theorem eq_one_iff_character_eq_char_one
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s) :
    ρ s = 1 ↔ ρ.character s = ρ.character 1 := by
  constructor
  · intro hs_one
    -- The forward implication is the trace computation for the identity endomorphism.
    rw [Representation.character, hs_one, Representation.char_one]
    simp
  · intro hchar
    -- Rewrite the character equality as equality in the norm bound.
    have hnorm : ‖ρ.character s‖ = Module.finrank ℂ V := by
      rw [hchar, Representation.char_one]
      simp
    rcases (character_norm_eq_char_one_iff_exists_smul_id ρ s hs).1 hnorm with ⟨z, hz⟩
    by_cases hdim : Module.finrank ℂ V = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.mp hdim
      exact Subsingleton.elim _ _
    · -- In positive dimension, comparing traces forces the scalar to be `1`.
      have hzchar : (Module.finrank ℂ V : ℂ) = z * Module.finrank ℂ V := by
        have hzchar' : ρ.character s = z * Module.finrank ℂ V := by
          simp [Representation.character, hz]
        rw [hchar, Representation.char_one] at hzchar'
        exact hzchar'
      have hz_eq_one : z = 1 := by
        apply mul_right_cancel₀ (show (Module.finrank ℂ V : ℂ) ≠ 0 by exact_mod_cast hdim)
        simpa [mul_comm] using hzchar.symm
      simpa [hz_eq_one] using hz

end

end Representation
