import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_1
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra Representation
open CategoryTheory
open MonoidAlgebra
open Representation
open Module.End

noncomputable section

universe u v w

section FieldUnitSubgroups

variable {G : Type u} [Group G]
variable {K : Type w} [Field K]
variable (U : Subgroup K[G]ˣ) [Finite U]

section SingleRepresentation

variable {V : Type v} [AddCommGroup V] [Module K V]
variable (ρ : Representation K G V)

-- Proof sketch: if the image of `s` and `u` both lie in the finite group `U`, then the unit
-- `((of K G).toHomUnits s⁻¹) * u` also lies in `U`, so its image under
-- `Units.map ρ.asAlgebraHom.toMonoidHom` has finite order in
-- `Module.End K Vˣ`. The underlying endomorphism is
-- `ρ s⁻¹ * ρ.asAlgebraHom u`, hence any eigenvalue has finite order.
/-- Exercise 6-6.2-4 (1): refined to the field-valued owner layer, if `u` lies in a finite
subgroup of `K[G]ˣ` together with the image of `s`, then every eigenvalue of `ρ(s⁻¹) ∘ uᵢ` has
finite order. -/
theorem hasEigenvalue_isOfFinOrder_of_mem_finite_unitSubgroup
    (u : K[G]ˣ) (hu : u ∈ U) (s : G) (hs : (of K G).toHomUnits s ∈ U) (μ : K)
    (hμ : HasEigenvalue ((ρ s⁻¹) * ρ.asAlgebraHom u) μ) :
    IsOfFinOrder μ := by
  let t : K[G]ˣ := ((of K G).toHomUnits s⁻¹) * u
  -- Move the source unit into the finite subgroup so its image has finite order.
  have ht : t ∈ U := by
    refine U.mul_mem ?_ hu
    simpa using U.inv_mem hs
  have hfinite_t_sub : IsOfFinOrder (⟨t, ht⟩ : U) := isOfFinOrder_of_finite _
  have hfinite_t : IsOfFinOrder t := by
    exact (Submonoid.isOfFinOrder_coe).2 hfinite_t_sub
  have hfinite_img : IsOfFinOrder (Units.map ρ.asAlgebraHom.toMonoidHom t) :=
    MonoidHom.isOfFinOrder (Units.map ρ.asAlgebraHom.toMonoidHom) hfinite_t
  obtain ⟨n, hnpos, hn⟩ := hfinite_img.exists_pow_eq_one
  -- Rewrite the finite-order relation in `End_K(V)` and push it to the eigenvalue.
  have ht_end : ((ρ s⁻¹) * ρ.asAlgebraHom u) ^ n = 1 := by
    have hn' := congrArg (fun x : (Module.End K V)ˣ ↦ (x : Module.End K V)) hn
    have hunit_inv : ρ.asAlgebraHom ↑((of K G).toHomUnits s)⁻¹ = ρ s⁻¹ := by
      change ρ.asAlgebraHom (of K G s⁻¹) = ρ s⁻¹
      simp
    have hmap_t : ρ.asAlgebraHom ↑t = (ρ s⁻¹) * ρ.asAlgebraHom u := by
      calc
        ρ.asAlgebraHom ↑t =
            ρ.asAlgebraHom ↑((of K G).toHomUnits s)⁻¹ * ρ.asAlgebraHom u := by
              simp [t, map_mul]
        _ = (ρ s⁻¹) * ρ.asAlgebraHom u := by
              rw [hunit_inv]
    simpa [hmap_t] using hn'
  have hμpow : HasEigenvalue (1 : Module.End K V) (μ ^ n) := by
    simpa [ht_end] using hμ.pow n
  obtain ⟨x, hxμ⟩ := hμpow.exists_hasEigenvector
  have hsx : (μ ^ n - 1) • x = 0 := by
    rw [sub_smul, one_smul, ← hxμ.apply_eq_smul]
    simp
  have hmn : μ ^ n = 1 := by
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hxμ.2).mp hsx)
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hnpos, hmn⟩

end SingleRepresentation

end FieldUnitSubgroups

section ComplexUnitSubgroups

variable {G : Type} [Group G]
variable (U : Subgroup ℂ[G]ˣ) [Finite U]

section SingleRepresentation

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V)

-- Proof sketch: apply part (1), specialized to `K = ℂ`, to every eigenvalue of
-- `ρ s⁻¹ * ρ.asAlgebraHom u`.
-- Those eigenvalues are roots of unity, so their inverses are their complex conjugates. Summing
-- over the eigenvalues identifies the complex conjugate of the trace with the trace of the inverse
-- endomorphism, while the image of `s` and the unit `u⁻¹` still lie in `U` because `U` is a
-- subgroup.
/-- Exercise 6-6.2-4 (2): if `u` and the image of `s` lie in a finite subgroup of `ℂ[G]ˣ`, then
the conjugate of `Tr(ρ(s⁻¹) ∘ uᵢ)` is `Tr((u⁻¹)ᵢ ∘ ρ(s))`. -/
theorem star_trace_eq_trace_inverse_of_mem_finite_unitSubgroup
    (u : ℂ[G]ˣ) (hu : u ∈ U) (s : G) (hs : (of ℂ G).toHomUnits s ∈ U) :
    star (LinearMap.trace ℂ V ((ρ s⁻¹) * ρ.asAlgebraHom u)) =
      LinearMap.trace ℂ V (ρ.asAlgebraHom ↑(u⁻¹) * ρ s) := by
  -- Route correction: instead of rebuilding the Chapter 2 trace lemma locally, restrict the
  -- algebra action to the finite subgroup `U` and apply the imported finite-order character
  -- identity there.
  let σ : Representation ℂ U V :=
    { toFun := fun x ↦ ρ.asAlgebraHom (x : ℂ[G]ˣ)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro x y
        ext z
        simp [map_mul] }
  let t : U := ⟨((of ℂ G).toHomUnits s⁻¹) * u, U.mul_mem (by simpa using U.inv_mem hs) hu⟩
  -- The finite subgroup element `t` has finite order, so its character value is conjugate to the
  -- character value of `t⁻¹`.
  have hunit_inv : ρ.asAlgebraHom ↑((of ℂ G).toHomUnits s)⁻¹ = ρ s⁻¹ := by
    change ρ.asAlgebraHom (of ℂ G s⁻¹) = ρ s⁻¹
    simp
  have hchar :=
    Representation.char_inv_eq_star_of_isOfFinOrder (ρ := σ) t (isOfFinOrder_of_finite t)
  -- Reinterpret the character identity as the required trace identity.
  simpa [Representation.character, σ, t, map_mul, mul_assoc, hunit_inv] using hchar.symm

end SingleRepresentation

section CoefficientRecovery

variable {ι : Type v}
variable [Finite G]
variable (π : ι → FDRep ℂ G) [IsCompleteIrreducibleFamily π]

-- Proof sketch: apply Proposition `groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace` to `u`
-- and to `u'`. The owner instance `IsCompleteIrreducibleFamily π` supplies the canonical
-- irreducible family required by that proposition, and `htrace` identifies the normalized trace
-- sums formed from the canonical Wedderburn images
-- `ρ̃[fun i ↦ Rep.of (π i).ρ] u i` and
-- `ρ̃[fun i ↦ Rep.of (π i).ρ] u' i`, so the coefficient of `u` at `s`, after
-- complex conjugation, equals
-- the coefficient of `u'` at `s⁻¹`.
/-- Exercise 6-6.2-4 (3): if the trace identities from part (2) hold on a complete family of
irreducible complex representations, then the coefficients satisfy `u(s)^* = u'(s⁻¹)`. -/
theorem complex_groupRing_coeff_star_eq_inverse_coeff
    (hpairwise : PairwiseNonisomorphic π)
    (u u' : ℂ[G]) (s : G)
    (htrace :
      let φ := ρ̃[fun i ↦ Rep.of (π i).ρ]
      ∀ i,
        star (LinearMap.trace ℂ (π i) ((π i).ρ s⁻¹ * φ u i)) =
          LinearMap.trace ℂ (π i) (φ u' i * (π i).ρ s)) :
    star (u s) = u' s⁻¹ := by
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π inferInstance hpairwise
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  let F : FDRep ℂ G ⥤ Rep ℂ G := forget₂ (FDRep ℂ G) (Rep ℂ G)
  have hpairwise_rep : PairwiseNonisomorphic (fun i ↦ Rep.of (π i).ρ) := by
    intro i j hij hij_iso
    apply hpairwise hij
    rcases hij_iso with ⟨e⟩
    simpa [F] using ⟨F.preimageIso e⟩
  let c : ℂ := (Nat.card G : ℂ)⁻¹
  let tu : ι → ℂ := fun i ↦
    (Module.finrank ℂ (π i) : ℂ) *
      LinearMap.trace ℂ (π i) ((π i).ρ s⁻¹ * (ρ̃[fun i ↦ Rep.of (π i).ρ]) u i)
  let tu' : ι → ℂ := fun i ↦
    (Module.finrank ℂ (π i) : ℂ) *
      LinearMap.trace ℂ (π i) (((ρ̃[fun i ↦ Rep.of (π i).ρ]) u' i) * (π i).ρ s)
  -- Expand both coefficients by Proposition 6-6.2-2 on the same complete irreducible family.
  have hu : u s = c * ∑ i, tu i := by
    change u s =
      (Nat.card G : ℂ)⁻¹ *
        ∑ i, (Module.finrank ℂ (π i) : ℂ) *
          LinearMap.trace ℂ (π i) ((π i).ρ s⁻¹ * (ρ̃[fun i ↦ Rep.of (π i).ρ]) u i)
    rw [Representation.groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace
      (π := fun i ↦ Rep.of (π i).ρ)
      (hπ_pairwise := hpairwise_rep)
      (hπ_complete := by simpa using (inferInstance : IsCompleteIrreducibleFamily π))]
    rw [Representation.finsum_eq_sum_univ (K := ℂ)]
  have hu' : u' s⁻¹ = c * ∑ i, tu' i := by
    calc
      u' s⁻¹ =
          (Nat.card G : ℂ)⁻¹ *
            ∑ i, (Module.finrank ℂ (π i) : ℂ) *
              LinearMap.trace ℂ (π i) ((π i).ρ s * (ρ̃[fun i ↦ Rep.of (π i).ρ]) u' i) := by
                rw [Representation.groupAlgebra_coeff_eq_card_inv_sum_finrank_mul_trace
                  (π := fun i ↦ Rep.of (π i).ρ)
                  (hπ_pairwise := hpairwise_rep)
                  (hπ_complete := by simpa using (inferInstance : IsCompleteIrreducibleFamily π))]
                rw [Representation.finsum_eq_sum_univ (K := ℂ)]
                simp [inv_inv]
      _ = c * ∑ i, tu' i := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [tu', LinearMap.trace_mul_comm]
  -- Conjugate the first trace sum termwise and replace each term using the trace hypothesis.
  calc
    star (u s) = c * star (∑ i, tu i) := by
      rw [hu]
      simp [c]
    _ = c * ∑ i, tu' i := by
      congr 1
      calc
        star (∑ i, tu i) = ∑ i, star (tu i) := by
          simp
        _ = ∑ i, tu' i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            star (tu i) =
                (Module.finrank ℂ (π i) : ℂ) *
                  star (LinearMap.trace ℂ (π i)
                    ((π i).ρ s⁻¹ * (ρ̃[fun i ↦ Rep.of (π i).ρ]) u i)) := by
                      simp [tu]
            _ =
                (Module.finrank ℂ (π i) : ℂ) *
                  LinearMap.trace ℂ (π i)
                    (((ρ̃[fun i ↦ Rep.of (π i).ρ]) u' i) * (π i).ρ s) := by
                      rw [htrace i]
            _ = tu' i := by
                  simp [tu']
    _ = u' s⁻¹ := by
      rw [hu']

end CoefficientRecovery

end ComplexUnitSubgroups

section ComplexNormSquare

variable {G : Type} [Group G]
variable (U : Subgroup ℂ[G]ˣ) [Finite U]

/-- Helper for Exercise 6-6.2-4: if the coefficients of `b` are the conjugate inverses of the
coefficients of `a`, then the coefficient of `1` in `b * a` is the sum of the squared norms of
the coefficients of `a`. -/
lemma coeff_mul_apply_one_eq_sum_normSq_of_star_coeff
    (a b : ℂ[G]) (hcoeff : ∀ s : G, star (a s) = b s⁻¹) :
    (b * a) 1 = ((a.sum (fun _ c ↦ Complex.normSq c) : ℝ) : ℂ) := by
  have hstar :
      a.support.sum (fun x ↦ b (1 * x⁻¹) * a x) =
        a.support.sum (fun x ↦ star (a x) * a x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [one_mul]
    rw [← hcoeff x]
  have hnorm :
      a.support.sum (fun x ↦ star (a x) * a x) =
        a.support.sum (fun x ↦ (Complex.normSq (a x) : ℂ)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simpa [Complex.normSq_eq_norm_sq] using (RCLike.conj_mul (a x))
  calc
    (b * a) 1 = a.sum (fun x c ↦ b (1 * x⁻¹) * c) := by
      rw [MonoidAlgebra.mul_apply_right]
    _ = a.support.sum (fun x ↦ b (1 * x⁻¹) * a x) := by
      simp [Finsupp.sum]
    _ = a.support.sum (fun x ↦ star (a x) * a x) := hstar
    _ = a.support.sum (fun x ↦ (Complex.normSq (a x) : ℂ)) := hnorm
    _ = ((a.sum (fun _ c ↦ Complex.normSq c) : ℝ) : ℂ) := by
      simp [Finsupp.sum]

/-- Helper for Exercise 6-6.2-4: on the left regular representation, the algebra action of
`ℂ[G]` is ordinary left multiplication on `ℂ[G]`. -/
lemma leftRegular_asAlgebraHom_apply_eq_mul [Finite G] (a b : ℂ[G]) :
    ((Representation.leftRegular ℂ G).asAlgebraHom a) b = a * b := by
  let x : (Representation.leftRegular ℂ G).asModule :=
    ((Representation.leftRegular ℂ G).asModuleEquiv).symm b
  -- Transport the module action back across the tautological `asModuleEquiv`.
  have hsmul := Representation.asModuleEquiv_map_smul (Representation.leftRegular ℂ G) a x
  -- For the regular action, scalar multiplication by `a` is multiplication by `a`.
  simpa [x, Representation.ofMulAction_self_smul_eq_mul] using hsmul.symm

/-- Helper for Exercise 6-6.2-4: the trace of the left regular action by `a` is `|G|` times the
coefficient of `a` at `1`. -/
lemma leftRegular_trace_eq_card_mul_coeff_one [Finite G] (a : ℂ[G]) :
    LinearMap.trace ℂ (ℂ[G]) ((Representation.leftRegular ℂ G).asAlgebraHom a) =
      (Nat.card G : ℂ) * a 1 := by
  -- Rewrite the regular algebra action as the explicit left-multiplication operator.
  have hmap : ((Representation.leftRegular ℂ G).asAlgebraHom a) = Algebra.lmul ℂ (ℂ[G]) a := by
    apply LinearMap.ext
    intro b
    exact leftRegular_asAlgebraHom_apply_eq_mul a b
  rw [hmap]
  -- Proposition 6-6.2-2 already computed this trace on the group algebra.
  exact Representation.trace_lmul_groupAlgebra_eq_card_mul_coeff_one (K := ℂ) (G := G) a

/-- Helper for Exercise 6-6.2-4: part (2) applied to the regular representation identifies the
coefficient of `u⁻¹` at `s⁻¹` with the conjugate of the coefficient of `u` at `s`. -/
lemma star_coeff_eq_inverse_coeff_of_mem_finite_unitSubgroup [Finite G]
    (hG : ∀ s : G, (of ℂ G).toHomUnits s ∈ U)
    (u : ℂ[G]ˣ) (hu : u ∈ U) (s : G) :
    star ((u : ℂ[G]) s) = ((↑(u⁻¹) : ℂ[G]) s⁻¹) := by
  have htrace :=
    star_trace_eq_trace_inverse_of_mem_finite_unitSubgroup
      (U := U) (ρ := Representation.leftRegular ℂ G) u hu s (hG s)
  have hleft :
      LinearMap.trace ℂ (ℂ[G])
          (((Representation.leftRegular ℂ G) s⁻¹) *
            (Representation.leftRegular ℂ G).asAlgebraHom u) =
        (Nat.card G : ℂ) * (u : ℂ[G]) s := by
    have hs_inv :
        (Representation.leftRegular ℂ G) s⁻¹ =
          (Representation.leftRegular ℂ G).asAlgebraHom (of ℂ G s⁻¹) := by
      simp
    -- Interpret the left trace as the trace of left multiplication by `(of s⁻¹) * u`.
    calc
      LinearMap.trace ℂ (ℂ[G])
          (((Representation.leftRegular ℂ G) s⁻¹) *
            (Representation.leftRegular ℂ G).asAlgebraHom u)
          =
            LinearMap.trace ℂ (ℂ[G])
              ((Representation.leftRegular ℂ G).asAlgebraHom
                ((of ℂ G s⁻¹) * (u : ℂ[G]))) := by
                  congr 1
                  rw [hs_inv]
                  rw [← map_mul]
      _ = (Nat.card G : ℂ) * (((of ℂ G s⁻¹) * (u : ℂ[G])) 1) := by
            exact leftRegular_trace_eq_card_mul_coeff_one ((of ℂ G s⁻¹) * (u : ℂ[G]))
      _ = (Nat.card G : ℂ) * (u : ℂ[G]) s := by
            simp [MonoidAlgebra.of_apply]
  have hright :
      LinearMap.trace ℂ (ℂ[G])
          ((Representation.leftRegular ℂ G).asAlgebraHom ↑(u⁻¹) *
            (Representation.leftRegular ℂ G) s) =
        (Nat.card G : ℂ) * ((↑(u⁻¹) : ℂ[G]) s⁻¹) := by
    have hs :
        (Representation.leftRegular ℂ G) s =
          (Representation.leftRegular ℂ G).asAlgebraHom (of ℂ G s) := by
      simp
    -- Interpret the right trace as the trace of left multiplication by `u⁻¹ * of s`.
    calc
      LinearMap.trace ℂ (ℂ[G])
          ((Representation.leftRegular ℂ G).asAlgebraHom ↑(u⁻¹) *
            (Representation.leftRegular ℂ G) s)
          =
            LinearMap.trace ℂ (ℂ[G])
              ((Representation.leftRegular ℂ G).asAlgebraHom
                (((↑(u⁻¹) : ℂ[G]) * of ℂ G s))) := by
                  congr 1
                  rw [hs]
                  rw [← map_mul]
      _ = (Nat.card G : ℂ) * ((((↑(u⁻¹) : ℂ[G]) * of ℂ G s)) 1) := by
            exact leftRegular_trace_eq_card_mul_coeff_one (((↑(u⁻¹) : ℂ[G]) * of ℂ G s))
      _ = (Nat.card G : ℂ) * ((↑(u⁻¹) : ℂ[G]) s⁻¹) := by
            simp [MonoidAlgebra.of_apply]
  have hscaled :
      (Nat.card G : ℂ) * star ((u : ℂ[G]) s) =
        (Nat.card G : ℂ) * ((↑(u⁻¹) : ℂ[G]) s⁻¹) := by
    -- Rewrite the regular-representation character identity as a coefficient identity.
    calc
      (Nat.card G : ℂ) * star ((u : ℂ[G]) s)
          = star ((Nat.card G : ℂ) * (u : ℂ[G]) s) := by
              simp
      _ = star
            (LinearMap.trace ℂ (ℂ[G])
              (((Representation.leftRegular ℂ G) s⁻¹) *
                (Representation.leftRegular ℂ G).asAlgebraHom u)) := by
              rw [hleft]
      _ = LinearMap.trace ℂ (ℂ[G])
            ((Representation.leftRegular ℂ G).asAlgebraHom ↑(u⁻¹) *
              (Representation.leftRegular ℂ G) s) := htrace
      _ = (Nat.card G : ℂ) * ((↑(u⁻¹) : ℂ[G]) s⁻¹) := hright
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    have hcard_nat : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast hcard_nat.ne'
  exact mul_left_cancel₀ hcard hscaled

-- Proof sketch: apply part (3) with `u' = u⁻¹` to identify the coefficient of `u⁻¹` at `s⁻¹`
-- with the complex conjugate of the coefficient of `u` at `s`. The coefficient of `1 = u * u⁻¹`
-- at the identity is then the canonical finitely supported sum `∑ ‖u(s)‖²` of the coefficients,
-- and this coefficient is equal to `1`.
/-- Exercise 6-6.2-4 (4): an element of a finite subgroup of `ℂ[G]ˣ` containing `G` has
coefficient square-sum equal to `1`. -/
theorem sum_sq_norm_coeff_eq_one_of_mem_finite_unitSubgroup
    (hG : ∀ s : G, (of ℂ G).toHomUnits s ∈ U)
    (u : ℂ[G]ˣ) (hu : u ∈ U) :
    (u : ℂ[G]).sum (fun _ a ↦ Complex.normSq a) = 1 := by
  -- Route correction: use part (2) only on the regular representation, so the trace identity
  -- becomes a direct coefficient identity on `ℂ[G]`.
  let f : G → U := fun s ↦ ⟨(of ℂ G).toHomUnits s, hG s⟩
  have hf : Function.Injective f := by
    intro s t hst
    have hunits : (of ℂ G).toHomUnits s = (of ℂ G).toHomUnits t :=
      congrArg (fun x : U => (x : ℂ[G]ˣ)) hst
    have hcoeff : (of ℂ G s : ℂ[G]) = of ℂ G t :=
      congrArg (fun x : ℂ[G]ˣ => (x : ℂ[G])) hunits
    by_contra hne
    have hs_eval : ((of ℂ G s : ℂ[G]) s) = (of ℂ G t : ℂ[G]) s :=
      congrArg (fun x : ℂ[G] => x s) hcoeff
    simp [MonoidAlgebra.of_apply, hne] at hs_eval
  letI : Finite G := Finite.of_injective f hf
  letI : Fintype G := Fintype.ofFinite G
  have hcoeff :
      ∀ s : G, star ((u : ℂ[G]) s) = ((↑(u⁻¹) : ℂ[G]) s⁻¹) := by
    intro s
    -- Part (2) now reads as a coefficient identity because the regular traces are coefficients.
    exact star_coeff_eq_inverse_coeff_of_mem_finite_unitSubgroup (U := U) hG u hu s
  have hsum :
      (((↑(u⁻¹) : ℂ[G]) * (u : ℂ[G])) 1) =
        (((u : ℂ[G]).sum (fun _ a ↦ Complex.normSq a) : ℝ) : ℂ) := by
    -- The coefficient of `1` in `u⁻¹ * u` is the square-sum of the coefficients of `u`.
    exact coeff_mul_apply_one_eq_sum_normSq_of_star_coeff
      (a := (u : ℂ[G])) (b := (↑(u⁻¹) : ℂ[G])) hcoeff
  have hone :
      (((u : ℂ[G]).sum (fun _ a ↦ Complex.normSq a) : ℝ) : ℂ) = 1 := by
    have hmul : ((↑(u⁻¹) : ℂ[G]) * (u : ℂ[G])) = (1 : ℂ[G]) := by
      simp
    -- Since `u⁻¹ * u = 1`, that coefficient at `1` is exactly `1`.
    calc
      (((u : ℂ[G]).sum (fun _ a ↦ Complex.normSq a) : ℝ) : ℂ) =
          (((↑(u⁻¹) : ℂ[G]) * (u : ℂ[G])) 1) := hsum.symm
      _ = (1 : ℂ[G]) 1 := by
            rw [hmul]
      _ = 1 := by
            change (of ℂ G (1 : G)) 1 = 1
            simp [MonoidAlgebra.of_apply]
  exact_mod_cast hone

end ComplexNormSquare

section IntegralUnitSubgroups

variable {G : Type} [Group G]
variable (U : Subgroup ℤ[G]ˣ) [Finite U]
variable (hG : ∀ s : G, (of ℤ G).toHomUnits s ∈ U)

include hG
/-- Helper for Exercise 6-6.2-4: casting coefficients to `ℂ` turns the complex norm-square
identity from part (4) into an integer square-sum identity. -/
lemma integral_coeff_square_sum_eq_one_of_mem_finite_unitSubgroup
    (u : ℤ[G]ˣ) (hu : u ∈ U) :
    (u : ℤ[G]).sum (fun _ a ↦ a * a) = 1 := by
  let φ : ℤ[G] →+* ℂ[G] := MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ)
  let UC : Subgroup ℂ[G]ˣ := U.map (Units.map φ.toMonoidHom)
  have hUCfinite : Finite UC := by
    let f : U → UC := fun x ↦ ⟨Units.map φ.toMonoidHom x, by exact ⟨x, x.2, rfl⟩⟩
    exact Finite.of_surjective f (by
      intro y
      rcases y.2 with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      exact Subtype.ext hxy)
  letI : Finite UC := hUCfinite
  have hGC : ∀ s : G, (of ℂ G).toHomUnits s ∈ UC := by
    intro s
    -- Map the embedded copy of `G` from `ℤ[G]` into `ℂ[G]`.
    refine ⟨(of ℤ G).toHomUnits s, hG s, ?_⟩
    ext t
    simp [φ]
  have huC : Units.map φ.toMonoidHom u ∈ UC := ⟨u, hu, rfl⟩
  have hsumC :
      (((Units.map φ.toMonoidHom u : ℂ[G]ˣ) : ℂ[G]).sum
        (fun _ a ↦ Complex.normSq a)) = 1 := by
    -- Part (4) applies to the image subgroup in `ℂ[G]ˣ`.
    simpa using
      sum_sq_norm_coeff_eq_one_of_mem_finite_unitSubgroup (U := UC) hGC
        (Units.map φ.toMonoidHom u) huC
  -- The mapped coefficients are just the integer coefficients cast to `ℂ`.
  have hcast_sum :
      (((Units.map φ.toMonoidHom u : ℂ[G]ˣ) : ℂ[G]).sum
        (fun _ a ↦ Complex.normSq a)) =
        (((u : ℤ[G]).sum (fun _ a ↦ a * a) : ℤ) : ℝ) := by
    change (Finsupp.mapRange (Int.castRingHom ℂ) (Int.castRingHom ℂ).map_zero (u : ℤ[G])).sum
        (fun _ a ↦ Complex.normSq a) =
      (((u : ℤ[G]).sum (fun _ a ↦ a * a) : ℤ) : ℝ)
    simpa [Complex.normSq_intCast] using
      (Finsupp.sum_mapRange_index (g := (u : ℤ[G]))
        (f := Int.castRingHom ℂ) (hf := by simp)
        (h := fun _ a ↦ Complex.normSq a)
        (h0 := fun _ ↦ by simp))
  rw [hcast_sum] at hsumC
  exact_mod_cast hsumC

omit hG

/-- Helper for Exercise 6-6.2-4: an integer-valued finitely supported function with square-sum
`1` has singleton support, and the unique nonzero coefficient is `1` or `-1`. -/
lemma integral_square_sum_eq_one_imp_support_eq_singleton
    (f : G →₀ ℤ) (hsum : f.sum (fun _ a ↦ a * a) = 1) :
    ∃ t : G, f.support = {t} ∧ (f t = 1 ∨ f t = -1) := by
  classical
  have hne : f ≠ 0 := by
    intro hf
    simp [hf] at hsum
  obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hsq_le : f t * f t ≤ 1 := by
    -- Every coefficient square is bounded above by the total square-sum.
    simpa [hsum] using
      (Finsupp.single_eval_le_sum (f := f) (g := fun a : ℤ ↦ a * a) (a := t)
        (by simp) (by
          intro a
          exact mul_self_nonneg a))
  have ht_ne_zero : f t ≠ 0 := Finsupp.mem_support_iff.mp ht
  have hsq_pos : 0 < f t * f t := by
    exact mul_self_pos.mpr ht_ne_zero
  have hsq_eq : f t * f t = 1 := by
    omega
  have hsum_support : f.support.sum (fun x ↦ f x * f x) = 1 := by
    simpa [Finsupp.sum] using hsum
  have hsum_diff : (f.support \ {t}).sum (fun x ↦ f x * f x) = 0 := by
    -- Once the distinguished square already contributes `1`, the remaining squares sum to `0`.
    have hone : 1 = 1 + (f.support \ {t}).sum (fun x ↦ f x * f x) := by
      calc
        1 = f.support.sum (fun x ↦ f x * f x) := hsum_support.symm
        _ = f t * f t + (f.support \ {t}).sum (fun x ↦ f x * f x) :=
          Finset.sum_eq_add_sum_diff_singleton_of_mem ht (fun x ↦ f x * f x)
        _ = 1 + (f.support \ {t}).sum (fun x ↦ f x * f x) := by rw [hsq_eq]
    omega
  have hzero : ∀ x ∈ f.support \ {t}, f x = 0 := by
    intro x hx
    have hsq_zero :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun y hy ↦ mul_self_nonneg (f y))).1 hsum_diff x hx
    exact (mul_eq_zero.mp hsq_zero).elim id id
  have hsupport : f.support = {t} := by
    refine Finset.eq_singleton_iff_nonempty_unique_mem.mpr ?_
    refine ⟨⟨t, ht⟩, ?_⟩
    intro x hx
    by_contra hxt
    exact (Finsupp.mem_support_iff.mp hx) (hzero x (by simp [hx, hxt]))
  have hsign : f t = 1 ∨ f t = -1 := by
    exact mul_self_eq_one_iff.mp hsq_eq
  exact ⟨t, hsupport, hsign⟩

-- Proof sketch: apply part (4) to the image of `u` in `ℂ[G]`. Since the coefficients of `u` are
-- integers and the sum of their squared absolute values is `1`, exactly one coefficient is nonzero
-- and that coefficient is `±1`.
include hG
/-- Exercise 6-6.2-4 (5): in a finite subgroup of `ℤ[G]ˣ` containing `G`, every element has
exactly one nonzero coefficient, and that coefficient is `1` or `-1`. -/
theorem integral_groupRing_support_eq_singleton_of_mem_finite_unitSubgroup
    (u : ℤ[G]ˣ) (hu : u ∈ U) :
    ∃ t : G, ((u : ℤ[G]).support = {t}) ∧ (((u : ℤ[G]) t = 1) ∨ ((u : ℤ[G]) t = -1)) := by
  -- Route correction: the invariant from part (4) is the square-sum, so we pass directly to the
  -- integer square identity instead of transporting support through coefficient extension.
  exact integral_square_sum_eq_one_imp_support_eq_singleton
    ((u : ℤ[G]))
    (integral_coeff_square_sum_eq_one_of_mem_finite_unitSubgroup
      (U := U) (hG := hG) u hu)

-- Proof sketch: combine part (5) with `Finsupp.support_eq_singleton` to rewrite the element of
-- `ℤ[G]` as a single basis term with coefficient `1` or `-1`, and package that sign as a unit
-- `ε : ℤˣ`.
/-- Exercise 6-6.2-4 (6): every element of a finite subgroup of `ℤ[G]ˣ` containing `G` is of the
form `± t` for some `t ∈ G`. -/
theorem integral_groupRing_unit_eq_sign_smul_of_mem_finite_unitSubgroup
    (u : ℤ[G]ˣ) (hu : u ∈ U) :
    ∃ ε : ℤˣ, ∃ t : G, (u : ℤ[G]) = (ε : ℤ) • of ℤ G t := by
  obtain ⟨t, hsupport, hcoeff⟩ :=
    integral_groupRing_support_eq_singleton_of_mem_finite_unitSubgroup
      (U := U) (hG := hG) u hu
  have hsingle : (u : ℤ[G]) = Finsupp.single t ((u : ℤ[G]) t) :=
    (Finsupp.support_eq_singleton.mp hsupport).2
  rcases hcoeff with hcoeff | hcoeff
  · -- A singleton coefficient `1` is exactly the basis element `of ℤ G t`.
    refine ⟨1, t, ?_⟩
    rw [hsingle, hcoeff]
    ext x
    by_cases hx : x = t
    · subst hx
      simp [MonoidAlgebra.of_apply]
    · simp [hx, MonoidAlgebra.of_apply]
  · -- A singleton coefficient `-1` is the negative of the same basis element.
    refine ⟨-1, t, ?_⟩
    rw [hsingle, hcoeff]
    ext x
    by_cases hx : x = t
    · subst hx
      simp [MonoidAlgebra.of_apply]
    · simp [hx, MonoidAlgebra.of_apply]

omit hG

end IntegralUnitSubgroups

section Higman

variable {G : Type} [Finite G] [CommGroup G]

/-- Helper for Exercise 6-6.2-4: for a torsion unit in `ℤ[G]ˣ`, the subgroup generated by the
group image and that unit can be realized as `range((of ℤ G).toHomUnits) ⊔ Subgroup.zpowers u`,
and this subgroup is finite. -/
lemma finite_unitSubgroup_containing_group_image_and_torsion
    (u : ℤ[G]ˣ) (hu : IsOfFinOrder u) :
    ∃ W : Subgroup ℤ[G]ˣ, u ∈ W ∧ (∀ s : G, (of ℤ G).toHomUnits s ∈ W) ∧ Finite W := by
  let H : Subgroup ℤ[G]ˣ := (of ℤ G).toHomUnits.range
  let K : Subgroup ℤ[G]ˣ := Subgroup.zpowers u
  let W : Subgroup ℤ[G]ˣ := H ⊔ K
  have hHfinite : Finite H := by
    exact Finite.of_surjective
      (of ℤ G).toHomUnits.rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hKfinite : Finite K := by
    simpa [K] using (Finite.of_equiv (Fin (orderOf u)) (finEquivZPowers hu))
  have hWfinite : Finite W := by
    -- Every element of `H ⊔ K` is a product of an element of `H` and an element of `K`.
    let f : H × K → W := fun x ↦ ⟨x.1.1 * x.2.1, by
      exact Subgroup.mul_mem_sup x.1.2 x.2.2⟩
    have hsurj : Function.Surjective f := by
      intro w
      have hwW : (w : ℤ[G]ˣ) ∈ H ⊔ K := by
        simp [W] at w
        exact w.2
      rcases Subgroup.mem_sup.mp hwW with ⟨h, hh, k, hk, hw⟩
      refine ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, ?_⟩
      exact Subtype.ext hw
    exact Finite.of_surjective f hsurj
  refine ⟨W, ?_, ?_, hWfinite⟩
  · have huK : u ∈ K := by
      simp [K]
    exact Subgroup.mem_sup_right huK
  · intro s
    exact Subgroup.mem_sup_left ⟨s, rfl⟩

-- Proof sketch: for a torsion unit `u`, the subgroup generated by the finite abelian group `G`
-- together with `u` inside `ℤ[G]ˣ` is finite because `u` has finite order and `ℤ[G]` is
-- commutative. Apply part (6) to that finite subgroup.
/-- Exercise 6-6.2-4 (7): if `G` is finite abelian, every finite-order unit of `ℤ[G]` is of the
form `± t` for some `t ∈ G` (Higman's theorem). -/
theorem integral_groupRing_torsion_unit_eq_sign_smul_of_abelian
    (u : ℤ[G]ˣ) (hu : IsOfFinOrder u) :
    ∃ ε : ℤˣ, ∃ t : G, (u : ℤ[G]) = (ε : ℤ) • of ℤ G t := by
  obtain ⟨W, huW, hGW, hWfinite⟩ :=
    finite_unitSubgroup_containing_group_image_and_torsion u hu
  letI : Finite W := hWfinite
  -- Apply part (6) inside the finite subgroup generated by the image of `G` and the torsion unit.
  exact integral_groupRing_unit_eq_sign_smul_of_mem_finite_unitSubgroup
    (U := W) (hG := hGW) u huW

end Higman
