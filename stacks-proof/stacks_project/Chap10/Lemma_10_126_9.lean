import Mathlib
import stacks_project.Chap10.Definition_10_32_1
import stacks_project.Chap10.Lemma_10_32_3
import stacks_project.Chap10.Lemma_10_32_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S']

/-- Helper for Lemma 10.126.9: coefficients lying in the image of a ring map lift to a
multivariate polynomial over the source ring. -/
lemma exists_mvPolynomial_lift_of_coeffs_subset {R₀ : Type*} [CommRing R₀]
    {n : ℕ} (φ : R₀ →+* R) (q : MvPolynomial (Fin n) R)
    (hq : (q.coeffs : Set R) ⊆ Set.range φ) :
    ∃ q₀ : MvPolynomial (Fin n) R₀, MvPolynomial.map φ q₀ = q := by
  -- The coefficientwise characterization of `MvPolynomial.map` is exactly the lifting criterion.
  exact q.mem_range_map_iff_coeffs_subset.mpr hq

/-- Helper for Lemma 10.126.9: after restricting coefficients to a finitely generated
`ℤ`-subalgebra, the pulled-back locally nilpotent ideal becomes nilpotent. -/
lemma isNilpotent_comap_of_locallyNilpotent_on_adjoin_int {I : Ideal R}
    (hI : I.IsLocallyNilpotent) {A : Set R} (hA : A.Finite) :
    IsNilpotent (Ideal.comap (algebraMap (Algebra.adjoin ℤ A) R) I) := by
  let R₀ : Subalgebra ℤ R := Algebra.adjoin ℤ A
  let J₀ : Ideal R₀ := Ideal.comap (algebraMap R₀ R) I
  have hfiniteType : Algebra.FiniteType ℤ R₀ :=
    Algebra.FiniteType.adjoin_of_finite hA
  letI : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have hmem : ∀ x ∈ J₀, IsNilpotent x := by
    intro x hx
    have hxR : IsNilpotent ((algebraMap R₀ R) x) := by
      exact (Ideal.isLocallyNilpotent_iff I).mp hI _ hx
    -- The coefficient subring embeds into `R`, so nilpotence descends back along the inclusion.
    exact
      (IsNilpotent.map_iff
          (show Function.Injective (algebraMap R₀ R) by
            intro x y hxy
            ext
            exact hxy)).1
        hxR
  -- In the Noetherian coefficient ring, elementwise nilpotence upgrades to nilpotence of the ideal.
  exact (Ideal.forall_mem_isNilpotent_iff_isNilpotent J₀).1 hmem

/-- Helper for Lemma 10.126.9: quotient-surjectivity modulo `I S'` produces lifts of the
presentation variables whose corrections have coefficients in `I`. -/
lemma exists_corrected_generator_lifts {I : Ideal R} (f : S →ₐ[R] S')
    (hquot :
      Function.Surjective ((Ideal.Quotient.mkₐ R (I.map (algebraMap R S'))).comp f))
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S')
    (hπ : Function.Surjective π) :
    ∃ s : Fin n → S, ∃ g : Fin n → MvPolynomial (Fin n) R,
      (∀ i, π (g i) = f (s i)) ∧
      ∀ i, g i - MvPolynomial.X i ∈ Ideal.map MvPolynomial.C I := by
  classical
  have hcomap :
      Ideal.comap π.toRingHom (Ideal.map (algebraMap R S') I) =
        Ideal.map MvPolynomial.C I ⊔ Ideal.comap π.toRingHom ⊥ := by
    -- Pulling back the extended ideal along a surjective presentation splits into the coefficient
    -- ideal together with the kernel of the presentation.
    have hcomp : π.toRingHom.comp MvPolynomial.C = algebraMap R S' := by
      ext r
      simp
    rw [← hcomp, ← Ideal.map_map]
    exact Ideal.comap_map_of_surjective (f := π.toRingHom) hπ (Ideal.map MvPolynomial.C I)
  choose s hs using fun i : Fin n ↦
    hquot ((Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S') I)) (π (MvPolynomial.X i)))
  choose p hp using fun i : Fin n ↦ hπ (f (s i))
  have hsup :
      ∀ i : Fin n,
        p i - MvPolynomial.X i ∈
          Ideal.map MvPolynomial.C I ⊔ Ideal.comap π.toRingHom ⊥ := by
    intro i
    have hmemQuot :
        f (s i) - π (MvPolynomial.X i) ∈ Ideal.map (algebraMap R S') I := by
      have hzero :
          (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S') I)) (f (s i)) -
              (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S') I)) (π (MvPolynomial.X i)) = 0 := by
        exact sub_eq_zero.mpr (hs i)
      exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa [map_sub] using hzero)
    have hmemComap :
        p i - MvPolynomial.X i ∈ Ideal.comap π.toRingHom (Ideal.map (algebraMap R S') I) := by
      change π (p i - MvPolynomial.X i) ∈ Ideal.map (algebraMap R S') I
      simpa [hp i, map_sub] using hmemQuot
    exact hcomap ▸ hmemComap
  choose a ha b hb hab using fun i : Fin n ↦ Submodule.mem_sup.mp (hsup i)
  refine ⟨s, fun i ↦ p i - b i, ?_, ?_⟩
  · intro i
    have hbzero : π (b i) = 0 := by
      simpa [Ideal.mem_comap] using hb i
    -- Subtracting the kernel correction preserves the chosen image inside `range f`.
    simpa [map_sub, hp i, hbzero]
  · intro i
    -- The residual difference from `X i` is exactly the coefficient-ideal piece of the pullback.
    have hcalc : (p i - b i) - MvPolynomial.X i = a i := by
      calc
        (p i - b i) - MvPolynomial.X i = p i - MvPolynomial.X i - b i := by ring
        _ = (a i + b i) - b i := by rw [hab i]
        _ = a i := by ring
    rw [hcalc]
    exact ha i

/-- Helper for Lemma 10.126.9: substitution by a nilpotent coefficient perturbation is congruent
to the identity modulo the coefficient ideal. -/
lemma sub_aeval_mem_coeff_ideal {A : Type*} [CommRing A] {n : ℕ} {J : Ideal A}
    (g : Fin n → MvPolynomial (Fin n) A)
    (hg : ∀ i, g i - MvPolynomial.X i ∈ Ideal.map MvPolynomial.C J)
    (q : MvPolynomial (Fin n) A) :
    q - MvPolynomial.aeval (R := A) g q ∈ Ideal.map MvPolynomial.C J := by
  -- The congruence is stable under the polynomial constructors defining `MvPolynomial`.
  induction q using MvPolynomial.induction_on with
  | C a =>
      simp
  | add p q hp hq =>
      -- Additivity reduces the claim to the two summands.
      have hsum :
        p + q - MvPolynomial.aeval (R := A) g (p + q)
            = (p - MvPolynomial.aeval (R := A) g p) +
                (q - MvPolynomial.aeval (R := A) g q) := by
                  rw [map_add]
                  ring
      rw [hsum]
      exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
      have hXi :
          MvPolynomial.X i - g i ∈ Ideal.map MvPolynomial.C J := by
        -- Reversing the perturbation keeps us inside the same ideal.
        have hsub :
            0 - (g i - MvPolynomial.X i) ∈ Ideal.map MvPolynomial.C J := by
          exact Ideal.sub_mem _ (by simp) (hg i)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub
      -- Multiplication by a variable introduces one copy of the basic perturbation error.
      have hmul :
        p * MvPolynomial.X i - MvPolynomial.aeval (R := A) g (p * MvPolynomial.X i)
            = (p - MvPolynomial.aeval (R := A) g p) * MvPolynomial.X i +
                MvPolynomial.aeval (R := A) g p * (MvPolynomial.X i - g i) := by
                  rw [map_mul, MvPolynomial.aeval_X]
                  ring
      rw [hmul]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hXi)

/-- Helper for Lemma 10.126.9: multiplying the coefficient filtration by one more copy of `J`
raises the filtration index by one. -/
lemma coeff_ideal_mul_eq_succ {A : Type*} [CommRing A] {n : ℕ} {J : Ideal A} (m : ℕ) :
    Ideal.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) (J ^ m : Ideal A) *
        Ideal.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) J =
      Ideal.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) (J ^ (m + 1) : Ideal A) := by
  -- This is just compatibility of `Ideal.map` with multiplication and powers.
  rw [pow_succ, ← Ideal.map_mul]

/-- Helper for Lemma 10.126.9: a monomial with coefficient in `J^m` changes by an element of the
next coefficient-ideal layer under the perturbed substitution. -/
lemma sub_aeval_monomial_mem_next_coeff_ideal {A : Type*} [CommRing A] {n : ℕ} {J : Ideal A}
    (g : Fin n → MvPolynomial (Fin n) A)
    (hg : ∀ i, g i - MvPolynomial.X i ∈ Ideal.map MvPolynomial.C J)
    {m : ℕ} (d : Fin n →₀ ℕ) {a : A} (ha : a ∈ J ^ m) :
    MvPolynomial.monomial d a - MvPolynomial.aeval (R := A) g (MvPolynomial.monomial d a) ∈
      Ideal.map MvPolynomial.C (J ^ (m + 1)) := by
  have hCa :
      MvPolynomial.C a ∈ Ideal.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) (J ^ m : Ideal A) := by
    -- The coefficient itself already sits in the `m`th layer.
    exact Ideal.mem_map_of_mem (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) ha
  have hbase :
      MvPolynomial.monomial d (1 : A) -
          MvPolynomial.aeval (R := A) g (MvPolynomial.monomial d (1 : A)) ∈
        Ideal.map MvPolynomial.C J := by
    -- The pure monomial factor only contributes the first-order substitution error.
    exact sub_aeval_mem_coeff_ideal (J := J) g hg (MvPolynomial.monomial d (1 : A))
  have hmul :
      MvPolynomial.C a *
          (MvPolynomial.monomial d (1 : A) -
            MvPolynomial.aeval (R := A) g (MvPolynomial.monomial d (1 : A))) ∈
        Ideal.map MvPolynomial.C (J ^ m : Ideal A) * Ideal.map MvPolynomial.C J := by
    exact Ideal.mul_mem_mul hCa hbase
  rw [coeff_ideal_mul_eq_succ (J := J) m] at hmul
  have hmonomial :
      MvPolynomial.monomial d a = MvPolynomial.C a * MvPolynomial.monomial d (1 : A) := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  -- Factor the coefficient out and use the multiplication rule for the filtration.
  have hfactor :
    MvPolynomial.monomial d a - MvPolynomial.aeval (R := A) g (MvPolynomial.monomial d a)
        = MvPolynomial.C a *
            (MvPolynomial.monomial d (1 : A) -
              MvPolynomial.aeval (R := A) g (MvPolynomial.monomial d (1 : A))) := by
                rw [hmonomial, map_mul]
                simp
                ring
  rw [hfactor]
  exact hmul

/-- Helper for Lemma 10.126.9: if all coefficients of a polynomial lie in `J^m`, then the
perturbed substitution changes it by an element of the next coefficient-ideal layer. -/
lemma sub_aeval_mem_next_coeff_ideal {A : Type*} [CommRing A] {n : ℕ} {J : Ideal A}
    (g : Fin n → MvPolynomial (Fin n) A)
    (hg : ∀ i, g i - MvPolynomial.X i ∈ Ideal.map MvPolynomial.C J)
    {m : ℕ} {p : MvPolynomial (Fin n) A}
    (hp : p ∈ Ideal.map MvPolynomial.C (J ^ m : Ideal A)) :
    p - MvPolynomial.aeval (R := A) g p ∈ Ideal.map MvPolynomial.C (J ^ (m + 1)) := by
  -- Expand once into monomials and treat each coefficient separately.
  rw [MvPolynomial.as_sum p, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ ?_
  intro d hd
  exact sub_aeval_monomial_mem_next_coeff_ideal (J := J) g hg d
    ((MvPolynomial.mem_map_C_iff.mp hp) d)

/-- Helper for Lemma 10.126.9: successive corrections move an arbitrary target polynomial into any
prescribed coefficient-ideal layer. -/
lemma exists_preimage_mod_coeff_filtration {A : Type*} [CommRing A] {n : ℕ} {J : Ideal A}
    (g : Fin n → MvPolynomial (Fin n) A)
    (hg : ∀ i, g i - MvPolynomial.X i ∈ Ideal.map MvPolynomial.C J) :
    ∀ m : ℕ, ∀ p : MvPolynomial (Fin n) A,
      ∃ q : MvPolynomial (Fin n) A,
        p - MvPolynomial.aeval (R := A) g q ∈ Ideal.map MvPolynomial.C (J ^ m : Ideal A) := by
  intro m
  induction m with
  | zero =>
      intro p
      refine ⟨0, ?_⟩
      -- At level `0` the coefficient ideal is the whole polynomial ring.
      rw [map_zero, pow_zero, Ideal.one_eq_top, Ideal.map_top]
      simp
  | succ m ih =>
      intro p
      rcases ih p with ⟨q, hq⟩
      refine ⟨q + (p - MvPolynomial.aeval (R := A) g q), ?_⟩
      -- Correcting by the current error pushes the new error one layer deeper.
      have hcorr :
        p - MvPolynomial.aeval (R := A) g (q + (p - MvPolynomial.aeval (R := A) g q))
            = (p - MvPolynomial.aeval (R := A) g q) -
                MvPolynomial.aeval (R := A) g (p - MvPolynomial.aeval (R := A) g q) := by
                  rw [map_add]
                  ring
      rw [hcorr]
      exact sub_aeval_mem_next_coeff_ideal (J := J) g hg hq

/-- Helper for Lemma 10.126.9: if each variable is perturbed by a polynomial with coefficients in
a nilpotent ideal, then the resulting substitution endomorphism of the polynomial ring is
surjective. -/
lemma aeval_surjective_of_nilpotent_variable_perturbation {A : Type*} [CommRing A]
    {n : ℕ} {J : Ideal A} (hJ : IsNilpotent J)
    (g : Fin n → MvPolynomial (Fin n) A)
    (hg : ∀ i, g i - MvPolynomial.X i ∈ Ideal.map MvPolynomial.C J) :
    Function.Surjective (MvPolynomial.aeval (R := A) g) := by
  obtain ⟨N, hN⟩ := hJ
  intro p
  obtain ⟨q, hq⟩ := exists_preimage_mod_coeff_filtration (J := J) g hg N p
  have hzero : p - MvPolynomial.aeval (R := A) g q = 0 := by
    -- At the nilpotence index the coefficient filtration vanishes.
    have hq' : p - MvPolynomial.aeval (R := A) g q ∈ (⊥ : Ideal (MvPolynomial (Fin n) A)) := by
      simpa [hN] using hq
    simpa [Ideal.mem_bot] using hq'
  -- The final correction therefore gives an actual preimage.
  refine ⟨q, ?_⟩
  exact (sub_eq_zero.mp hzero).symm

-- Proof sketch: choose finitely many generators of the finite type `R`-algebra `S'`; surjectivity
-- modulo `I S'` lifts each generator to an element of the image up to an error term in `I S'`.
-- Those error coefficients lie in a finitely generated `ℤ`-subalgebra of `R`, where Lemma
-- `10.32.5` upgrades local nilpotence to nilpotence. The resulting polynomial change of variables
-- is then an automorphism, forcing the generators themselves to lie in the image.
/-- Lemma 10.126.9: let `I` be a locally nilpotent ideal of `R`. If `f : S →ₐ[R] S'` becomes
surjective after quotienting `S'` by `I S'`, and `S'` is of finite type over `R`, then `f` is
surjective. -/
theorem surjective_of_surjective_quotient_of_finiteType_of_locallyNilpotent
    {I : Ideal R} (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] S')
    (hquot :
      Function.Surjective ((Ideal.Quotient.mkₐ R (I.map (algebraMap R S'))).comp f))
    [Algebra.FiniteType R S'] :
    Function.Surjective f := by
  classical
  obtain ⟨n, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := S')).mp
    inferInstance
  obtain ⟨s, g, hgπ, hgmem⟩ := exists_corrected_generator_lifts (I := I) f hquot π hπ
  intro z
  obtain ⟨p, hpz⟩ := hπ z
  let d : Fin n → MvPolynomial (Fin n) R := fun i ↦ g i - MvPolynomial.X i
  let A : Set R := (p.coeffs : Set R) ∪ ⋃ i, ((d i).coeffs : Set R)
  let R₀ : Subalgebra ℤ R := Algebra.adjoin ℤ A
  let J₀ : Ideal R₀ := Ideal.comap (algebraMap R₀ R) I
  have hAfinite : A.Finite := by
    refine p.coeffs.finite_toSet.union ?_
    exact Set.finite_iUnion fun i ↦ (d i).coeffs.finite_toSet
  have hJ₀ : IsNilpotent J₀ :=
    isNilpotent_comap_of_locallyNilpotent_on_adjoin_int (R := R) hI hAfinite
  have hpcoeffs : (p.coeffs : Set R) ⊆ Set.range (algebraMap R₀ R) := by
    intro x hx
    rw [Subalgebra.setRange_algebraMap]
    exact Algebra.subset_adjoin (Or.inl hx)
  have hdcoeffs : ∀ i : Fin n, ((d i).coeffs : Set R) ⊆ Set.range (algebraMap R₀ R) := by
    intro i x hx
    rw [Subalgebra.setRange_algebraMap]
    exact Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
  obtain ⟨p₀, hp₀⟩ := exists_mvPolynomial_lift_of_coeffs_subset (R := R) (φ := algebraMap R₀ R)
    p hpcoeffs
  choose d₀ hd₀ using fun i : Fin n ↦
    exists_mvPolynomial_lift_of_coeffs_subset (R := R) (φ := algebraMap R₀ R) (d i) (hdcoeffs i)
  let g₀ : Fin n → MvPolynomial (Fin n) R₀ := fun i ↦ MvPolynomial.X i + d₀ i
  have hg₀map : ∀ i : Fin n, MvPolynomial.map (algebraMap R₀ R) (g₀ i) = g i := by
    intro i
    -- The lifted perturbation reassembles the original corrected generator over `R`.
    simp [g₀, d, hd₀ i]
  have hg₀mem : ∀ i : Fin n, g₀ i - MvPolynomial.X i ∈ Ideal.map MvPolynomial.C J₀ := by
    intro i
    -- The lifted correction has coefficients in the pulled-back ideal `J₀`.
    rw [show g₀ i - MvPolynomial.X i = d₀ i by simp [g₀]]
    rw [MvPolynomial.mem_map_C_iff]
    intro m
    change (algebraMap R₀ R) ((d₀ i).coeff m) ∈ I
    rw [show (algebraMap R₀ R) ((d₀ i).coeff m) = (d i).coeff m by
      simpa using congrArg (MvPolynomial.coeff m) (hd₀ i)]
    simpa [d] using (MvPolynomial.mem_map_C_iff.mp (hgmem i)) m
  have hsurj₀ :
      Function.Surjective (MvPolynomial.aeval (R := R₀) g₀) :=
    aeval_surjective_of_nilpotent_variable_perturbation (A := R₀) hJ₀ g₀ hg₀mem
  obtain ⟨q₀, hq₀⟩ := hsurj₀ p₀
  let q : MvPolynomial (Fin n) R := MvPolynomial.map (algebraMap R₀ R) q₀
  have hp_eval : MvPolynomial.aeval g q = p := by
    -- Route correction: the source proof works over the smaller coefficient ring first, then maps
    -- back to `R`; `map_aeval` and `eval₂_map` implement that transport.
    calc
      MvPolynomial.aeval g q
          = MvPolynomial.eval₂Hom (algebraMap R₀ (MvPolynomial (Fin n) R)) g q₀ := by
              simpa [q, MvPolynomial.aeval_def] using
                (MvPolynomial.eval₂Hom_map_hom
                  (algebraMap R₀ R) g (algebraMap R (MvPolynomial (Fin n) R)) q₀)
      _ = MvPolynomial.map (algebraMap R₀ R) (MvPolynomial.aeval g₀ q₀) := by
            symm
            simpa [MvPolynomial.aeval_def, hg₀map] using
              (MvPolynomial.map_aeval g₀ (MvPolynomial.map (algebraMap R₀ R)) q₀)
      _ = p := by
            simpa [hp₀] using congrArg (MvPolynomial.map (algebraMap R₀ R)) hq₀
  refine ⟨MvPolynomial.aeval s q, ?_⟩
  calc
    f (MvPolynomial.aeval s q) = MvPolynomial.aeval (fun i ↦ f (s i)) q := by
      simpa using (MvPolynomial.comp_aeval_apply (f := s) f q)
    _ = MvPolynomial.aeval (fun i ↦ π (g i)) q := by simp [hgπ]
    _ = π (MvPolynomial.aeval g q) := by
      symm
      simpa using (MvPolynomial.comp_aeval_apply (f := g) π q)
    _ = π p := by rw [hp_eval]
    _ = z := hpz

end
