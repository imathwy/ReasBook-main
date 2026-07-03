import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_3
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_4_1.ClassFunctionScalarExtension
import LinearRepresentations_Serre_1977.Chap13.Exercise_13_13_1_16.GammaActions
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver

open CategoryTheory
open IsCyclotomicExtension.Rat
open scoped BigOperators MonoidAlgebra Representation
open Representation

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G]

section ExerciseClauses

variable {K : Type u} [Field K] [NumberField K]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ K]

/-- Helper for Exercise 13-13.1-16: under the cyclotomic Galois equivalence, the LinearRepresentations_Serre_1977 subgroup
attached to the fixed field of a subgroup of `Γ_ℚ(G)` is the subgroup itself. -/
theorem gammaSubgroup_fixedField_preimage_eq
    (H : Subgroup (Γ_ℚ(G))) :
    let HGal : Subgroup (Gal(K / ℚ)) :=
      H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom
    Γ[IntermediateField.fixedField HGal](G) = H := by
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {Monoid.exponent G} ℚ K
  let e := galEquivZMod (Monoid.exponent G) K
  dsimp [Representation.gammaSubgroup, e]
  rw [IntermediateField.fixingSubgroup_fixedField]
  change Subgroup.map e.toMonoidHom (H.comap e.toMonoidHom) = H
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [Subgroup.mem_comap] using hx
  · intro ht
    refine ⟨e.symm t, ?_, e.apply_symm_apply t⟩
    simpa [Subgroup.mem_comap] using ht

/-- The `Γ_ℚ`-action on an index set of irreducible `K`-representations is compatible with
Galois conjugation of their characters. This is the source-faithful hypothesis used in Exercise
`13-13.1-16` whenever equivariance of the irreducible-character index set is asserted. -/
def IrreducibleCharacterIndexGaloisCompatible
    {ι : Type u} [MulAction ((ZMod (Monoid.exponent G))ˣ) ι] (π : ι → Rep K G)
    [∀ i, FiniteDimensional K (π i)] : Prop :=
  ∀ (t : Γ_ℚ(G)) (i : ι) (g : G),
    (π (t • i)).ρ.character g = t • (π i).ρ.character g

/-- Helper for Exercise 13-13.1-16: pairwise nonisomorphic irreducible `K`-representations have
linearly independent character functions. -/
theorem character_linearIndependent_of_complete_pairwise_nonisomorphic_rep
    {ι : Type u} (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    LinearIndependent K (fun i ↦ (π i).ρ.character) := by
  classical
  let πfd : ι → FDRep K G := fun i ↦ FDRep.of (π i).ρ
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  have hπ_pairwise_fdrep :
      PairwiseNonisomorphic πfd :=
    pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise
  have horth :
      Pairwise fun i j ↦
        ⟪(πfd i).character, (πfd j).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K πfd hπ_complete.isSimple hπ_pairwise_fdrep
  have hpair_sum :
      ∀ s : Finset ι, ∀ a : ι → K, ∀ ψ : G → K,
        ⟪∑ j ∈ s, a j • (πfd j).character, ψ⟫ =
          ∑ j ∈ s, a j * ⟪(πfd j).character, ψ⟫ := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro a ψ
      simp [Representation.groupFunctionPairingOverField]
    · intro i s hi ih a ψ
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hpair :
      ⟪∑ j ∈ s, g j • (πfd j).character, (πfd i).character⟫ = (0 : K) := by
    have hpair_eq :=
      congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (πfd i).character) hg
    have hzero_pair :
        groupFunctionPairingOverField K (0 : G → K) (πfd i).character = 0 := by
      simp [Representation.groupFunctionPairingOverField]
    exact hpair_eq.trans hzero_pair
  rw [hpair_sum s g ((πfd i).character)] at hpair
  rw [Finset.sum_eq_single i] at hpair
  · have hself_ne :
        ⟪(πfd i).character, (πfd i).character⟫ ≠ (0 : K) :=
      by
        letI : Representation.IsIrreducible (πfd i).ρ :=
          IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
        haveI : Nontrivial (πfd i) := by
          by_contra hX
          letI : Subsingleton (πfd i) := not_nontrivial_iff_subsingleton.mp hX
          have hbot_top : (⊥ : Subrepresentation (πfd i).ρ) = ⊤ := by
            apply Subrepresentation.toSubmodule_injective
            ext x
            constructor
            · intro _
              trivial
            · intro _
              simpa using (Subsingleton.elim x 0)
          exact IsSimpleOrder.bot_ne_top hbot_top
        let n : ℕ := Module.finrank K (Representation.IntertwiningMap (πfd i).ρ (πfd i).ρ)
        have hn_pos : 0 < n := by
          letI : Nontrivial (Representation.IntertwiningMap (πfd i).ρ (πfd i).ρ) := by
            refine ⟨0, 1, ?_⟩
            intro hone
            obtain ⟨x, hx⟩ := exists_ne (0 : πfd i)
            have hx0 :=
              congrArg
                (fun f : Representation.IntertwiningMap (πfd i).ρ (πfd i).ρ ↦ f x) hone
            exact hx (by simpa using hx0.symm)
          simpa [n] using
            (Module.finrank_pos_iff.mpr
              (inferInstance :
                Nontrivial (Representation.IntertwiningMap (πfd i).ρ (πfd i).ρ)))
        have hpair_eq :
            ⟪(πfd i).character, (πfd i).character⟫ = (n : K) := by
          simpa [n] using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              (K := K) (ρ := (πfd i).ρ) (σ := (πfd i).ρ))
        rw [hpair_eq]
        exact Nat.cast_ne_zero.mpr hn_pos.ne'
    exact (mul_eq_zero.mp hpair).resolve_right hself_ne
  · intro j _ hji
    rw [horth hji, mul_zero]
  · intro hnot_mem
    exact (hnot_mem hi).elim

/-- Helper for Exercise 13-13.1-16: a complete pairwise nonisomorphic irreducible family in
`Rep K G` has a finite index set without assuming `[IsAlgClosed K]`. -/
theorem finite_index_of_complete_pairwise_nonisomorphic_rep
    {ι : Type u} (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) :
    Finite ι := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional K (G → K) := by
    infer_instance
  have hlin :
      LinearIndependent K (fun i ↦ (π i).ρ.character) :=
    character_linearIndependent_of_complete_pairwise_nonisomorphic_rep
      (G := G) (K := K) π hπ_pairwise hπ_complete
  exact Cardinal.lt_aleph0_iff_finite.mp
    (LinearIndependent.lt_aleph0_of_finiteDimensional hlin)

section FixedFieldOrbitSums

variable {ι : Type u} [Fintype ι] [MulAction ((ZMod (Monoid.exponent G))ˣ) ι]
variable (π : ι → Rep K G) [∀ i, FiniteDimensional K (π i)]

attribute [local instance] Classical.decEq

/-- Helper for Exercise 13-13.1-16: LinearRepresentations_Serre_1977's subgroup fixes the image of its defining intermediate
field under the cyclotomic Galois action. -/
theorem gammaSubgroup_smul_algebraMap_fixed
    (K0 : IntermediateField ℚ K) (a : K0) (t : Γ[K0](G)) :
    t • algebraMap K0 K a = algebraMap K0 K a := by
  -- Unfold the subgroup action back to the corresponding Galois automorphism of `K / ℚ`.
  change ((galEquivZMod (Monoid.exponent G) K).symm (t : (ZMod (Monoid.exponent G))ˣ))
      (algebraMap K0 K a) = algebraMap K0 K a
  have ht :
      ((galEquivZMod (Monoid.exponent G) K).symm (t : (ZMod (Monoid.exponent G))ˣ)) ∈
        K0.fixingSubgroup := by
    exact Subgroup.mem_map_equiv.mp t.2
  -- Elements of the intermediate field are fixed by its fixing subgroup by definition.
  exact (IntermediateField.mem_fixingSubgroup_iff K0 _).1 ht _ a.2

/-- Helper for Exercise 13-13.1-16: an element of the ambient cyclotomic field that is fixed by
every element of `Γ[K0](G)` already belongs to the intermediate field `K0`. -/
theorem mem_intermediateField_of_gammaSubgroup_fixed_local
    (K0 : IntermediateField ℚ K) (x : K)
    (hx : ∀ t : Γ[K0](G), t • x = x) :
    x ∈ K0 := by
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois (S := {Monoid.exponent G}) ℚ K
  have hx_fixed : x ∈ IntermediateField.fixedField K0.fixingSubgroup := by
    -- Translate the `Γ[K0](G)`-fixedness hypothesis back across the cyclotomic Galois equivalence.
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    have hσ_fix :
        (galEquivZMod (Monoid.exponent G) K).symm
            (galEquivZMod (Monoid.exponent G) K σ) ∈
          K0.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      convert hσ y hy using 1
      exact congrArg (fun f : K ≃ₐ[ℚ] K => f y)
        (MulEquiv.symm_apply_apply (galEquivZMod (Monoid.exponent G) K) σ)
    have ht_mem : galEquivZMod (Monoid.exponent G) K σ ∈ Γ[K0](G) := by
      exact
        (Subgroup.mem_map_equiv.mpr hσ_fix :
          galEquivZMod (Monoid.exponent G) K σ ∈ Γ[K0](G))
    let t : Γ[K0](G) := ⟨galEquivZMod (Monoid.exponent G) K σ, ht_mem⟩
    have ht_fixed : t • x = x := hx t
    have ht_eq :
        (galEquivZMod (Monoid.exponent G) K).symm (t : (ZMod (Monoid.exponent G))ˣ) = σ := by
      simpa [t] using
        (MulEquiv.symm_apply_apply (galEquivZMod (Monoid.exponent G) K) σ)
    change
      (galEquivZMod (Monoid.exponent G) K).symm (t : (ZMod (Monoid.exponent G))ˣ) x = x at ht_fixed
    simpa [ht_eq] using ht_fixed
  simpa [IsGalois.fixedField_fixingSubgroup (F := ℚ) (E := K) K0] using hx_fixed

/-- Helper for Exercise 13-13.1-16: sum the irreducible `K`-characters over one `H`-orbit in the
index set. The definition uses the quotient fiber directly, so no representative choice is needed.
-/
noncomputable def orbit_sum_character
    (H : Subgroup (Γ_ℚ(G))) (q : MulAction.orbitRel.Quotient H ι) : G → K :=
  fun s ↦
    Finset.sum
      (Finset.univ.filter
        (fun i : ι ↦ (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q))
      (fun i ↦ (π i).ρ.character s)

/-- Helper for Exercise 13-13.1-16: the orbit sum is a class function, because it already lies in
the finite additive span of honest characters. -/
theorem isClassFunction_orbit_sum_character
    (H : Subgroup (Γ_ℚ(G))) (q : MulAction.orbitRel.Quotient H ι) :
    _root_.IsClassFunction (orbit_sum_character (G := G) (K := K) π H q) := by
  classical
  refine ⟨?_⟩
  intro x y hxy
  -- Sum the conjugacy-invariant character values term-by-term over the quotient fiber.
  rcases isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.mp hxy) with ⟨a, ha⟩
  unfold orbit_sum_character
  rw [← ha]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact ((π i).ρ.char_conj x a).symm

/-- Helper for Exercise 13-13.1-16: rewrite one orbit sum as a sum over the subtype consisting of
the indices in the chosen quotient fiber. This exposes the orbit fiber as an honest finite type for
later reindexing arguments. -/
theorem orbit_sum_character_eq_sum_fiber_subtype
    (H : Subgroup (Γ_ℚ(G))) (q : MulAction.orbitRel.Quotient H ι) (s : G) :
    orbit_sum_character (G := G) (K := K) π H q s =
      ∑ j : {i // (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q},
        (π j.1).ρ.character s := by
  -- Replace the filtered finite sum by the canonical finite type of the quotient fiber.
  simpa [orbit_sum_character] using
    (Finset.sum_subtype
      (s := Finset.univ.filter
        (fun i : ι ↦ (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q))
      (p := fun i : ι ↦ (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q)
      (h := by
        intro x
        simp)
      (f := fun i : ι ↦ (π i).ρ.character s))

/-- Helper for Exercise 13-13.1-16: a filtered sum over one quotient fiber can be rewritten as a
sum over the corresponding subtype with a stable chosen predicate. This packages the
`Finset.sum_subtype` coercion once so later quotient-fiber regrouping proofs do not depend on
hidden `DecidablePred` instances. -/
theorem sum_filter_quotientFiber_eq_sum_subtype
    (H : Subgroup (Γ_ℚ(G))) (q : MulAction.orbitRel.Quotient H ι) (f : ι → K) :
    Finset.sum
        (Finset.univ.filter
          (fun i : ι ↦ (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q))
        f =
      ∑ j : {i // (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q}, f j.1 := by
  -- Replace the filtered finite sum by the canonical subtype of the quotient fiber.
  simpa using
    (Finset.sum_subtype
      (s := Finset.univ.filter
        (fun i : ι ↦ (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q))
      (p := fun i : ι ↦ (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q)
      (h := by
        intro x
        simp)
      (f := f))

/-- Helper for Exercise 13-13.1-16: after rewriting one quotient fiber as a subtype, an external
scalar multiplies the subtype-indexed sum term-by-term. This isolates the stable post-`mul_sum`
shape needed by the final orbit regrouping proof. -/
theorem fiber_subtype_sum_transport_after_mul_sum
    (H : Subgroup (Γ_ℚ(G))) (q : MulAction.orbitRel.Quotient H ι)
    (a : K) (f : ι → K) :
    a *
        Finset.sum
          (Finset.univ.filter
            (fun i : ι ↦ (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q))
          f =
      ∑ j : {i // (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q}, a * f j.1 := by
  -- First replace the filtered quotient fiber by its canonical subtype, then push the scalar
  -- through the finite sum.
  rw [sum_filter_quotientFiber_eq_sum_subtype (G := G) (K := K) (ι := ι) H q f]
  simp [Finset.mul_sum]

/-- Helper for Exercise 13-13.1-16: the sum of character values over one `H`-orbit is fixed by
the subgroup action on values. This is the fixed-field descent step from LinearRepresentations_Serre_1977's source proof. -/
theorem orbit_sum_character_fixed_by_subgroup
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π)
    (H : Subgroup (Γ_ℚ(G))) (q : MulAction.orbitRel.Quotient H ι) (t : H) (s : G) :
    t • orbit_sum_character (G := G) (K := K) π H q s =
      orbit_sum_character (G := G) (K := K) π H q s := by
  classical
  letI : DecidableEq (MulAction.orbitRel.Quotient H ι) := Classical.decEq _
  let Fiber : Type u :=
    {i // (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = q}
  let e : Fiber → Fiber :=
    fun i ↦ by
      refine ⟨t • i.1, ?_⟩
      have hq :
          (Quotient.mk'' (t • i.1) : MulAction.orbitRel.Quotient H ι) =
            Quotient.mk'' i.1 := by
        apply Quotient.sound
        change t • i.1 ∈ MulAction.orbit H i.1
        exact ⟨t, rfl⟩
      exact hq.trans i.2
  have hFiber :
      orbit_sum_character (G := G) (K := K) π H q s =
        ∑ j : Fiber, (π j.1).ρ.character s := by
    -- First rewrite the orbit sum over the concrete quotient fiber.
    simpa [Fiber] using
      orbit_sum_character_eq_sum_fiber_subtype
        (G := G) (K := K) (π := π) H q s
  calc
    t • orbit_sum_character (G := G) (K := K) π H q s
        = t • ∑ j : Fiber, (π j.1).ρ.character s := by
            rw [hFiber]
    _ =
        ∑ j : Fiber, t • (π j.1).ρ.character s := by
              -- The cyclotomic subgroup action is additive on the ambient field `K`.
              change
                (MulSemiringAction.toRingHom H K t)
                    (∑ j : Fiber, (π j.1).ρ.character s)
                  =
                    ∑ j : Fiber, (MulSemiringAction.toRingHom H K t) ((π j.1).ρ.character s)
              exact
                map_sum (MulSemiringAction.toRingHom H K t)
                  (fun j : Fiber ↦ (π j.1).ρ.character s)
                  Finset.univ
    _ =
        ∑ j : Fiber, (π (t • j.1)).ρ.character s := by
            -- Apply the indexed Galois-compatibility hypothesis term-by-term.
            exact
              Fintype.sum_congr
                (f := fun j : Fiber ↦ t • (π j.1).ρ.character s)
                (g := fun j : Fiber ↦ (π (t • j.1)).ρ.character s)
                (fun j ↦ by
                  symm
                  exact hπ_galois t j.1 s)
    _ = ∑ j : Fiber, (π j.1).ρ.character s := by
            -- Reindex the fiber sum by the orbit action `j ↦ t • j`.
            refine
              Fintype.sum_bijective
                (e := e)
                ?_
                (f := fun j : Fiber ↦ (π (t • j.1)).ρ.character s)
                (g := fun j : Fiber ↦ (π j.1).ρ.character s)
                ?_
            · constructor
              · intro a b hab
                apply Subtype.ext
                exact smul_left_cancel t (congrArg Subtype.val hab)
              · intro b
                refine ⟨⟨t⁻¹ • b.1, ?_⟩, ?_⟩
                · have hq :
                    (Quotient.mk'' (t⁻¹ • b.1) : MulAction.orbitRel.Quotient H ι) =
                      Quotient.mk'' b.1 := by
                    apply Quotient.sound
                    change t⁻¹ • b.1 ∈ MulAction.orbit H b.1
                    exact ⟨t⁻¹, rfl⟩
                  exact hq.trans b.2
                · apply Subtype.ext
                  simp [e]
            · intro j
              rfl
    _ = orbit_sum_character (G := G) (K := K) π H q s := by
          rw [hFiber]

/-- Helper for Exercise 13-13.1-16: every value of an `H`-orbit sum already lies in the fixed
field of the cyclotomic Galois subgroup corresponding to `H`. -/
theorem orbit_sum_character_mem_fixedField
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π)
    (H : Subgroup (Γ_ℚ(G))) (q : MulAction.orbitRel.Quotient H ι) (s : G) :
    let HGal : Subgroup (Gal(K / ℚ)) :=
      H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom
    let KH : IntermediateField ℚ K := IntermediateField.fixedField HGal
    orbit_sum_character (G := G) (K := K) π H q s ∈ KH := by
  let HGal : Subgroup (Gal(K / ℚ)) :=
    H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom
  let KH : IntermediateField ℚ K := IntermediateField.fixedField HGal
  have hGamma : Γ[KH](G) = H := by
    simpa [KH, HGal] using gammaSubgroup_fixedField_preimage_eq (G := G) (K := K) H
  -- Values fixed by `Γ[KH](G)` descend pointwise to the fixed field `KH`.
  exact
    mem_intermediateField_of_gammaSubgroup_fixed_local (G := G) (K := K) KH
      (orbit_sum_character (G := G) (K := K) π H q s) (by
        intro t
        let tH : H := ⟨t.1, by simpa [hGamma] using t.2⟩
        simpa [tH] using
          orbit_sum_character_fixed_by_subgroup
            (G := G) (K := K) (π := π) hπ_galois H q tH s)

/-- Helper for Exercise 13-13.1-16: descend an `H`-orbit sum pointwise to the fixed field
attached to `H`. This is the concrete `KH`-valued character candidate used in LinearRepresentations_Serre_1977's argument. -/
noncomputable def orbit_sum_character_fixedFieldLift
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π)
    (H : Subgroup (Γ_ℚ(G))) :
    let HGal : Subgroup (Gal(K / ℚ)) :=
      H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom
    let KH : IntermediateField ℚ K := IntermediateField.fixedField HGal
    MulAction.orbitRel.Quotient H ι → G → KH :=
  fun q s ↦
    ⟨orbit_sum_character (G := G) (K := K) π H q s,
      orbit_sum_character_mem_fixedField
        (G := G) (K := K) (π := π) hπ_galois H q s⟩

/-- Helper for Exercise 13-13.1-16: extending scalars from the fixed field back to `K` recovers
the original orbit-sum character value. -/
@[simp] theorem algebraMap_orbit_sum_character_fixedFieldLift
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π)
    (H : Subgroup (Γ_ℚ(G))) (q : MulAction.orbitRel.Quotient H ι) (s : G) :
    let HGal : Subgroup (Gal(K / ℚ)) :=
      H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom
    let KH : IntermediateField ℚ K := IntermediateField.fixedField HGal
    algebraMap KH K
        (orbit_sum_character_fixedFieldLift
          (G := G) (K := K) (π := π) hπ_galois H q s) =
      orbit_sum_character (G := G) (K := K) π H q s := by
  rfl

/-- Helper for Exercise 13-13.1-16: coefficientwise extension from an intermediate field to the
ambient cyclotomic field preserves honest character-ring membership. -/
theorem map_mem_characterRingOverField_of_mem_intermediateField_characterRing
    (K0 : IntermediateField ℚ K) {χ : G → K0}
    (hχ : χ ∈ R[K0](G)) :
    (fun s ↦ algebraMap K0 K (χ s)) ∈ R[K](G) := by
  -- Push the coefficientwise field embedding through the algebra-adjoin presentation of `R[K0](G)`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional K0 ρ := hρfd
    let ρK : Rep K G := Rep.of (Representation.scalarExtension ρ.ρ)
    have hscalar :
        (Representation.scalarExtension ρ.ρ).character =
          fun g ↦ algebraMap K0 K (ρ.ρ.character g) := by
      -- Scalar extension changes only the coefficients of the trace character.
      ext g
      exact LinearMap.trace_baseChange (ρ.ρ g) K
    have hchar :
        (fun g ↦ algebraMap K0 K (ρ.ρ.character g)) = ρK.ρ.character := by
      -- Read the scalar-extension character through the bundled `Rep K G` wrapper.
      ext g
      simpa [ρK] using (congrFun hscalar g).symm
    rw [hchar]
    exact Representation.rep_character_mem_characterRingOverField (K := K) (G := G) ρK
  · intro n
    change (fun _ : G ↦ algebraMap K0 K (algebraMap ℤ K0 n)) ∈ R[K](G)
    have hconst :
        (fun _ : G ↦ algebraMap K0 K (algebraMap ℤ K0 n)) = algebraMap ℤ (G → K) n := by
      ext g
      simp
    rw [hconst]
    exact (R[K](G)).algebraMap_mem n
  · intro φ ψ _ _ hφ hψ
    -- The target character ring is closed under addition.
    simpa using (R[K](G)).add_mem hφ hψ
  · intro φ ψ _ _ hφ hψ
    -- The target character ring is also closed under pointwise multiplication.
    simpa using (R[K](G)).mul_mem hφ hψ

/-- Helper for Exercise 13-13.1-16: extending an honest `KH`-character to `K` and expanding it in
the irreducible-character basis produces the expected finite character sum. -/
theorem honest_character_irreducible_basis_expansion
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (KH : IntermediateField ℚ K) {χ : G → KH}
    (hχ : χ ∈ R[KH](G)) :
    let πfd : ι → FDRep K G := fun i ↦ FDRep.of (π i).ρ
    let x : R[K](G) :=
      ⟨fun s ↦ algebraMap KH K (χ s),
        map_mem_characterRingOverField_of_mem_intermediateField_characterRing
          (G := G) (K := K) KH hχ⟩
    let b :=
      Representation.irreducible_characters_basis_of_complete_family K πfd
        (pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise) hπ_complete
    let c := b.repr x
    ∀ s : G,
      algebraMap KH K (χ s) = ∑ i, c i • (π i).ρ.character s := by
  classical
  let πfd : ι → FDRep K G := fun i ↦ FDRep.of (π i).ρ
  let x : R[K](G) :=
    ⟨fun s ↦ algebraMap KH K (χ s),
      map_mem_characterRingOverField_of_mem_intermediateField_characterRing
        (G := G) (K := K) KH hχ⟩
  let b :=
    Representation.irreducible_characters_basis_of_complete_family K πfd
      (pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise) hπ_complete
  let c := b.repr x
  change ∀ g : G, algebraMap KH K (χ g) = ∑ i, c i • (π i).ρ.character g
  have hx :
      (x : G → K) = ∑ i, c i • (π i).ρ.character := by
    -- Rewrite the irreducible-basis reconstruction in the ambient function space first.
    simpa [πfd, x, b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R[K](G) ↦ (z : G → K)) (b.sum_repr x).symm
  intro g
  -- Evaluate that basis expansion at the chosen group element.
  simpa [x] using congrFun hx g

/-- Helper for Exercise 13-13.1-16: in LinearRepresentations_Serre_1977's source proof, the integral multiplicities in the
irreducible `K`-basis expansion of an honest `KH`-character are constant on `H`-orbits. -/
theorem honest_character_irreducible_multiplicity_constant_on_orbits
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π)
    (H : Subgroup (Γ_ℚ(G))) (KH : IntermediateField ℚ K)
    (hGamma : Γ[KH](G) = H)
    {χ : G → KH} (hχ : χ ∈ R[KH](G)) :
    let _ : Finite ι := by
      exact finite_index_of_complete_pairwise_nonisomorphic_rep
        (π := π) hπ_pairwise hπ_complete
    let πfd : ι → FDRep K G := fun i ↦ FDRep.of (π i).ρ
    let x : R[K](G) :=
      ⟨fun s ↦ algebraMap KH K (χ s),
        map_mem_characterRingOverField_of_mem_intermediateField_characterRing
          (G := G) (K := K) KH hχ⟩
    let b :=
      Representation.irreducible_characters_basis_of_complete_family K πfd
        (pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise) hπ_complete
    let c : ι →₀ ℤ := b.repr x
    ∀ (t : H) (i : ι), c (t • i) = c i := by
  classical
  let _ : Finite ι := by
    exact finite_index_of_complete_pairwise_nonisomorphic_rep
      (π := π) hπ_pairwise hπ_complete
  let _ : Fintype ι := Fintype.ofFinite ι
  let πfd : ι → FDRep K G := fun i ↦ FDRep.of (π i).ρ
  let x : R[K](G) :=
    ⟨fun s ↦ algebraMap KH K (χ s),
      map_mem_characterRingOverField_of_mem_intermediateField_characterRing
        (G := G) (K := K) KH hχ⟩
  let b :=
    Representation.irreducible_characters_basis_of_complete_family K πfd
      (pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise) hπ_complete
  let c : ι →₀ ℤ := b.repr x
  change ∀ (t : H) (i : ι), c (t • i) = c i
  have hχ_expand :
      ∀ s : G, algebraMap KH K (χ s) = ∑ i, c i • (π i).ρ.character s := by
    -- Start from the honest irreducible-basis expansion before comparing transported copies.
    simpa [πfd, x, b, c] using
      honest_character_irreducible_basis_expansion
        (G := G) (K := K) (π := π) hπ_pairwise hπ_complete KH hχ
  have hχ_expandK :
      ∀ s : G, algebraMap KH K (χ s) =
        ∑ i, (((c i : ℤ) : K)) • (π i).ρ.character s := by
    intro s
    simpa [zsmul_eq_mul, smul_eq_mul] using hχ_expand s
  have hχ_fixed :
      ∀ (t : H) (s : G), t • algebraMap KH K (χ s) = algebraMap KH K (χ s) := by
    intro t s
    have htGamma : (t : Γ_ℚ(G)) ∈ Γ[KH](G) := by
      simpa [hGamma] using t.2
    let tKH : Γ[KH](G) := ⟨t, htGamma⟩
    -- Every value of the honest `KH`-character is fixed by the subgroup attached to `KH`.
    simpa [tKH] using
      gammaSubgroup_smul_algebraMap_fixed (G := G) (K := K) KH (χ s) tKH
  have hchars : LinearIndependent K (fun i ↦ (π i).ρ.character) :=
    character_linearIndependent_of_complete_pairwise_nonisomorphic_rep
      (G := G) (K := K) π hπ_pairwise hπ_complete
  intro t i
  have hreindexed :
      ∀ s : G, algebraMap KH K (χ s) =
        ∑ j, (((c (t⁻¹ • j) : ℤ) : K)) • (π j).ρ.character s := by
    intro s
    calc
      algebraMap KH K (χ s) = t • algebraMap KH K (χ s) := by
        simpa using (hχ_fixed t s).symm
      _ = t • ∑ j, (((c j : ℤ) : K)) • (π j).ρ.character s := by
            rw [hχ_expandK s]
      _ = ∑ j, t • ((((c j : ℤ) : K)) • (π j).ρ.character s) := by
            change
              (MulSemiringAction.toRingHom H K t)
                  (∑ j, (((c j : ℤ) : K)) • (π j).ρ.character s) =
                ∑ j, (MulSemiringAction.toRingHom H K t)
                  ((((c j : ℤ) : K)) • (π j).ρ.character s)
            simp [map_sum]
      _ = ∑ j, (((c j : ℤ) : K)) • (π (t • j)).ρ.character s := by
            -- Apply the Galois-compatibility hypothesis term-by-term.
            refine Finset.sum_congr rfl ?_
            intro j hj
            change
              (MulSemiringAction.toRingHom H K t)
                  ((((c j : ℤ) : K) * (π j).ρ.character s)) =
                (((c j : ℤ) : K) * (π (t • j)).ρ.character s)
            calc
              (MulSemiringAction.toRingHom H K t)
                  ((((c j : ℤ) : K) * (π j).ρ.character s))
                  = (((c j : ℤ) : K) * (t • (π j).ρ.character s)) := by
                      simp [map_mul]
              _ = (((c j : ℤ) : K) * (π (t • j)).ρ.character s) := by
                    simpa using
                      congrArg
                        (fun z : K ↦ (((c j : ℤ) : K) * z))
                        (hπ_galois t j s).symm
      _ = ∑ j, (((c (t⁻¹ • j) : ℤ) : K)) • (π j).ρ.character s := by
            -- Reindex by the permutation `j ↦ t • j` of the irreducible index set.
            let e : ι ≃ ι := MulAction.toPerm t
            simpa [e] using
              (Fintype.sum_equiv e
                (fun j : ι ↦ (((c j : ℤ) : K)) • (π (t • j)).ρ.character s)
                (fun j : ι ↦ (((c (t⁻¹ • j) : ℤ) : K)) • (π j).ρ.character s)
                (fun j ↦ by
                  dsimp [e]
                  rw [show t⁻¹ • (t • j) = j by
                    simpa using (inv_smul_eq_iff.mpr rfl : t⁻¹ • (t • j) = j)]))
  have hsum_eq :
      (∑ j, (((c j : ℤ) : K)) • (π j).ρ.character) =
        (∑ j, (((c (t⁻¹ • j) : ℤ) : K)) • (π j).ρ.character) := by
    funext s
    -- Compare the original expansion with the transported-and-reindexed expansion of the same
    -- character.
    simpa using (hχ_expandK s).symm.trans (hreindexed s)
  have hcoeff_cast :
      ((c (t • i) : ℤ) : K) = ((c i : ℤ) : K) := by
    have hcoords :
        ∀ j : ι, (((c j : ℤ) : K)) = (((c (t⁻¹ • j) : ℤ) : K)) := by
      intro j
      exact hchars.eq_coords_of_eq hsum_eq j
    simpa using hcoords (t • i)
  exact_mod_cast hcoeff_cast

/-- Helper for Exercise 13-13.1-16: orbit-constant integer coefficients descend canonically to a
quotient-indexed `KH`-valued `Finsupp`. -/
theorem orbit_constant_integer_coefficients_descend_to_quotient
    (H : Subgroup (Γ_ℚ(G))) (KH : IntermediateField ℚ K)
    (c : ι →₀ ℤ)
    (hc : ∀ (t : H) (i : ι), c (t • i) = c i) :
    ∃ d : MulAction.orbitRel.Quotient H ι →₀ KH,
      ∀ i : ι, d (Quotient.mk'' i : MulAction.orbitRel.Quotient H ι) = algebraMap ℤ KH (c i) := by
  classical
  let Q := MulAction.orbitRel.Quotient H ι
  let d : Q →₀ KH :=
    Finsupp.onFinset Finset.univ
      (fun q : Q ↦ algebraMap ℤ KH (c (Quotient.out q)))
      (by
        intro q _hq
        exact Finset.mem_univ q)
  refine ⟨d, ?_⟩
  intro i
  have hout :
      MulAction.orbitRel H ι (Quotient.out (Quotient.mk'' i : Q)) i :=
    Quotient.exact (Quotient.out_eq (Quotient.mk'' i : Q))
  rcases hout with ⟨t, ht⟩
  -- The orbit-constant hypothesis identifies the chosen quotient representative with the original
  -- coefficient.
  calc
    d (Quotient.mk'' i : Q)
        = algebraMap ℤ KH (c (Quotient.out (Quotient.mk'' i : Q))) := by
            simp [d]
    _ = algebraMap ℤ KH (c i) := by
          have hci :
              c i = c (Quotient.out (Quotient.mk'' i : Q)) := by
            simpa [ht] using (hc t i).symm
          simpa [hci]

/-- Helper for Exercise 13-13.1-16: after extending scalars back to `K`, the descended quotient
coefficients regroup into the original irreducible-character expansion. -/
theorem orbitLift_linearCombination_algebraMap_eq_irreducible_sum
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π)
    (H : Subgroup (Γ_ℚ(G))) (c : ι →₀ ℤ)
    (d : MulAction.orbitRel.Quotient H ι →₀
      IntermediateField.fixedField
        (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom))
    (hd : ∀ i : ι,
      d (Quotient.mk'' i :
          MulAction.orbitRel.Quotient H ι) =
        algebraMap ℤ
          (IntermediateField.fixedField
            (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom))
          (c i)) :
    ∀ s : G,
      algebraMap
          (IntermediateField.fixedField
            (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom))
          K
          ((Finsupp.linearCombination
              (IntermediateField.fixedField
                (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom))
              (orbit_sum_character_fixedFieldLift
                (G := G) (K := K) (π := π) hπ_galois H) d) s) =
        ∑ i : ι, (((c i : ℤ) : K)) • (π i).ρ.character s := by
  classical
  let KH : IntermediateField ℚ K :=
    IntermediateField.fixedField
      (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom)
  let Q := MulAction.orbitRel.Quotient H ι
  letI : DecidableEq Q := Classical.decEq _
  let orbitLift : Q → G → KH :=
    orbit_sum_character_fixedFieldLift
      (G := G) (K := K) (π := π) hπ_galois H
  intro s
  -- Normalize the `Finsupp.linearCombination` into a quotient-indexed sum before reindexing the
  -- quotient fibers back to the original irreducible-character index set.
  calc
    algebraMap KH K ((Finsupp.linearCombination KH orbitLift d) s)
        = ∑ q : Q, algebraMap KH K (d q) * orbit_sum_character (G := G) (K := K) π H q s := by
            -- Extend scalars through the `Q`-indexed linear combination term-by-term.
            have hd_finite :
                (Finsupp.linearEquivFunOnFinite KH KH Q).symm (fun q : Q ↦ d q) = d := by
              ext q
              rfl
            rw [← hd_finite]
            rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply
              (R := KH) (v := orbitLift) (x := fun q : Q ↦ d q)]
            rw [Fintype.linearCombination_apply]
            simp only [Finset.sum_apply, Pi.smul_apply]
            rw [map_sum]
            refine Fintype.sum_congr
              (fun q : Q ↦ algebraMap KH K (d q * orbitLift q s))
              (fun q : Q ↦ algebraMap KH K (d q) *
                orbit_sum_character (G := G) (K := K) π H q s)
              ?_
            intro q
            simpa [orbitLift] using
              (map_mul (algebraMap KH K) (d q) (orbitLift q s))
    _ =
        ∑ i : ι,
          algebraMap KH K (d (Quotient.mk'' i : Q)) * (π i).ρ.character s := by
            -- Rewrite each orbit sum by its quotient fiber and then collapse the sigma-fiber
            -- indexing back to the original index set `ι`.
            rw [show
                (∑ q : Q, algebraMap KH K (d q) * orbit_sum_character
                    (G := G) (K := K) π H q s) =
                  ∑ q : Q,
                    ∑ j : {i // (Quotient.mk'' i : Q) = q},
                      algebraMap KH K (d q) * (π j.1).ρ.character s by
                  congr with q
                  simpa [orbit_sum_character] using
                    fiber_subtype_sum_transport_after_mul_sum
                      (G := G) (K := K) (ι := ι) H q (algebraMap KH K (d q))
                      (fun i : ι ↦ (π i).ρ.character s)]
            rw [← Fintype.sum_sigma']
            let e : ((q : Q) × {i // (Quotient.mk'' i : Q) = q}) ≃ ι :=
              Equiv.sigmaFiberEquiv (fun i : ι ↦ (Quotient.mk'' i : Q))
            exact
              Fintype.sum_equiv e
                (fun x ↦ algebraMap KH K (d x.1) * (π x.2.1).ρ.character s)
                (fun i ↦ algebraMap KH K (d (Quotient.mk'' i : Q)) * (π i).ρ.character s)
                (fun x ↦ by
                  rcases x with ⟨q, j⟩
                  change algebraMap KH K (d q) * (π j.1).ρ.character s =
                    algebraMap KH K (d (Quotient.mk'' j.1 : Q)) * (π j.1).ρ.character s
                  rw [j.2])
    _ = ∑ i : ι, (((c i : ℤ) : K)) • (π i).ρ.character s := by
          -- Only after the reindexing is complete do we substitute the descended coefficients `d`.
          refine Fintype.sum_congr
            (fun i : ι ↦ algebraMap KH K (d (Quotient.mk'' i : Q)) * (π i).ρ.character s)
            (fun i : ι ↦ (((c i : ℤ) : K)) • (π i).ρ.character s)
            ?_
          intro i
          change algebraMap KH K (d (Quotient.mk'' i : Q)) * (π i).ρ.character s =
            (((c i : ℤ) : K)) • (π i).ρ.character s
          rw [hd i]
          have hcoeff :
              algebraMap KH K (algebraMap ℤ KH (c i)) = (((c i : ℤ) : K)) := by
            exact
              congrArg (fun f : ℤ →+* K => f (c i))
                (IsScalarTower.algebraMap_eq ℤ KH K)
          rw [hcoeff]
          simp [smul_eq_mul]

/-- Helper for Exercise 13-13.1-16: once the regrouped scalar-extension identity is known,
injectivity of `algebraMap KH K` descends it back to the original `KH`-valued character. -/
theorem honest_character_eq_linearCombination_orbitLift
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π)
    (H : Subgroup (Γ_ℚ(G))) (c : ι →₀ ℤ)
    {χ : G →
      IntermediateField.fixedField
        (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom)}
    (d : MulAction.orbitRel.Quotient H ι →₀
      IntermediateField.fixedField
        (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom))
    (hd : ∀ i : ι,
      d (Quotient.mk'' i :
          MulAction.orbitRel.Quotient H ι) =
        algebraMap ℤ
          (IntermediateField.fixedField
            (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom))
          (c i))
    (hχ_expand : ∀ s : G,
      algebraMap
          (IntermediateField.fixedField
            (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom))
          K
          (χ s) =
        ∑ i : ι, (((c i : ℤ) : K)) • (π i).ρ.character s) :
    χ =
      Finsupp.linearCombination
        (IntermediateField.fixedField
          (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom))
        (orbit_sum_character_fixedFieldLift
          (G := G) (K := K) (π := π) hπ_galois H) d := by
  classical
  let KH : IntermediateField ℚ K :=
    IntermediateField.fixedField
      (H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom)
  let Q := MulAction.orbitRel.Quotient H ι
  let χ' : G → KH := χ
  let d' : Q →₀ KH := d
  let orbitLift : Q → G → KH :=
    orbit_sum_character_fixedFieldLift
      (G := G) (K := K) (π := π) hπ_galois H
  change χ' = Finsupp.linearCombination KH orbitLift d'
  ext s
  -- Compare both `KH`-valued functions after extending scalars to `K`.
  calc
    (χ' s : K) = ∑ i : ι, (((c i : ℤ) : K)) • (π i).ρ.character s := by
      simpa [χ'] using hχ_expand s
    _ = (((Finsupp.linearCombination KH orbitLift d') s : KH) : K) := by
      symm
      have hdi : ∀ i : ι, d' (Quotient.mk'' i : Q) = algebraMap ℤ KH (c i) := by
        intro i
        simpa [d'] using hd i
      simpa [Q, orbitLift, KH, d'] using
        orbitLift_linearCombination_algebraMap_eq_irreducible_sum
          (G := G) (K := K) (π := π) hπ_galois H c d' hdi s

/-- Helper for Exercise 13-13.1-16: the honest-generator case of LinearRepresentations_Serre_1977's descent rewrites one
`KH`-character as a `KH`-linear combination of the descended orbit sums. -/
theorem mem_span_orbit_sum_character_fixedFieldLift_of_mem_characterRingOverField
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))
    (hπ_galois : IrreducibleCharacterIndexGaloisCompatible π)
    (H : Subgroup (Γ_ℚ(G))) :
    let _ : Finite ι := by
      exact finite_index_of_complete_pairwise_nonisomorphic_rep
        (π := π) hπ_pairwise hπ_complete
    let HGal : Subgroup (Gal(K / ℚ)) :=
      H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom
    let KH : IntermediateField ℚ K := IntermediateField.fixedField HGal
    let orbitLift : MulAction.orbitRel.Quotient H ι → G → KH :=
      orbit_sum_character_fixedFieldLift
        (G := G) (K := K) (π := π) hπ_galois H
    ∀ {χ : G → KH}, χ ∈ R[KH](G) →
      χ ∈ Submodule.span KH (Set.range orbitLift) := by
  classical
  let _ : Finite ι := by
    exact finite_index_of_complete_pairwise_nonisomorphic_rep
      (π := π) hπ_pairwise hπ_complete
  let HGal : Subgroup (Gal(K / ℚ)) :=
    H.comap (galEquivZMod (Monoid.exponent G) K).toMonoidHom
  let KH : IntermediateField ℚ K := IntermediateField.fixedField HGal
  let orbitLift : MulAction.orbitRel.Quotient H ι → G → KH :=
    orbit_sum_character_fixedFieldLift
      (G := G) (K := K) (π := π) hπ_galois H
  change ∀ {χ : G → KH}, χ ∈ R[KH](G) →
      χ ∈ Submodule.span KH (Set.range orbitLift)
  intro χ hχ
  have hχK : (fun s ↦ algebraMap KH K (χ s)) ∈ R[K](G) := by
    -- First extend the honest `KH`-character back to the ambient cyclotomic field `K`.
    exact
      map_mem_characterRingOverField_of_mem_intermediateField_characterRing
        (G := G) (K := K) KH hχ
  let Q := MulAction.orbitRel.Quotient H ι
  let πfd : ι → FDRep K G := fun i ↦ FDRep.of (π i).ρ
  let x : R[K](G) := ⟨fun s ↦ algebraMap KH K (χ s), hχK⟩
  let b :=
    Representation.irreducible_characters_basis_of_complete_family K πfd
      (pairwiseNonisomorphic_fdrep_of_rep π hπ_pairwise) hπ_complete
  let c : ι →₀ ℤ := b.repr x
  have hGamma : Γ[KH](G) = H := by
    simpa [KH, HGal] using gammaSubgroup_fixedField_preimage_eq (G := G) (K := K) H
  have hχ_expand :
      ∀ s : G, algebraMap KH K (χ s) = ∑ i, c i • (π i).ρ.character s := by
    -- Expand the honest `KH`-character in the irreducible `K`-basis before descending to orbits.
    simpa [πfd, x, b, c] using
      honest_character_irreducible_basis_expansion
        (G := G) (K := K) (π := π) hπ_pairwise hπ_complete KH hχ
  have hχ_fixed :
      ∀ (t : H) (s : G), t • algebraMap KH K (χ s) = algebraMap KH K (χ s) := by
    intro t s
    have htGamma : (t : Γ_ℚ(G)) ∈ Γ[KH](G) := by
      simpa [hGamma] using t.2
    let tKH : Γ[KH](G) := ⟨t, htGamma⟩
    -- Every `KH`-value is fixed by the subgroup attached to `KH`.
    simpa [tKH] using
      gammaSubgroup_smul_algebraMap_fixed (G := G) (K := K) KH (χ s) tKH
  have hc_orbit :
      ∀ (t : H) (i : ι), c (t • i) = c i := by
    -- Compare the original basis expansion with its `t`-transported and reindexed copy.
    simpa [πfd, x, b, c] using
      honest_character_irreducible_multiplicity_constant_on_orbits
        (G := G) (K := K) (π := π) hπ_pairwise hπ_complete hπ_galois H KH hGamma hχ
  obtain ⟨d, hd⟩ :=
    orbit_constant_integer_coefficients_descend_to_quotient
      (G := G) (K := K) (ι := ι) H KH c hc_orbit
  have hχ_expandK :
      ∀ s : G, algebraMap KH K (χ s) =
        ∑ i : ι, (((c i : ℤ) : K)) • (π i).ρ.character s := by
    intro s
    -- Rewrite the honest basis expansion with coefficients viewed in `K`.
    simpa [zsmul_eq_mul, smul_eq_mul] using hχ_expand s
  have hχ_orbit :
      χ = Finsupp.linearCombination KH orbitLift d := by
    -- Route correction: the source proof descends the orbit-constant coefficients to `Q`,
    -- regroups by quotient fibers, and then descends the resulting equality via injectivity.
    simpa [Q, orbitLift, KH, HGal] using
      honest_character_eq_linearCombination_orbitLift
        (G := G) (K := K) (π := π) hπ_galois H c d hd hχ_expandK
  -- The descended quotient coefficients `d` now provide the explicit span witness.
  refine
    (Finsupp.mem_span_range_iff_exists_finsupp
      (R := KH) (v := orbitLift)).2 ?_
  refine ⟨d, ?_⟩
  simpa [Finsupp.linearCombination_apply] using hχ_orbit.symm

end FixedFieldOrbitSums

end ExerciseClauses
