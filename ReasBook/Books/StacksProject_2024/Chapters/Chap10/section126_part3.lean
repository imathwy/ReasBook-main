import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Ideal.Over

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_126_7 (from Chap10) -/
universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
variable {S' : Type w} [CommRing S'] [Algebra R S'] [Algebra.FinitePresentation R S']

-- Proof sketch: choose a finite presentation of `S` and transport the images of finitely many
-- generators across the local `R`-algebra isomorphism `S_𝔮 ≃ S'_{𝔮'}`. After clearing the
-- denominators away from `𝔮'`, obtain an `R`-algebra map `S → S'_{g'}` inducing the given local
-- isomorphism. Lemma `10.6.2` keeps finite presentation after composing with this map, and Lemma
-- `10.126.6` then yields a product decomposition after shrinking once more, from which an open
-- neighborhood isomorphism `S_g ≃ S'_{g'}` follows.
/-- Lemma 10.126.7: if `S` and `S'` are finitely presented `R`-algebras and the local `R`-algebras
`S_𝔮` and `S'_𝔮'` are isomorphic at primes `𝔮 ∈ Spec(S)` and `𝔮' ∈ Spec(S')`, then after
shrinking to principal opens around those primes there is an `R`-algebra isomorphism
`S_g ≃ S'_{g'}`. -/
theorem exists_awayAlgEquiv_of_localizationAtPrime_algEquiv
    (q : PrimeSpectrum S) (q' : PrimeSpectrum S')
    (hlocal : Localization.AtPrime q.asIdeal ≃ₐ[R] Localization.AtPrime q'.asIdeal) :
    ∃ (g : S) (_ : g ∉ q.asIdeal) (g' : S') (_ : g' ∉ q'.asIdeal),
      Nonempty (Localization.Away g ≃ₐ[R] Localization.Away g') := sorry

end

/-! ### Lemma_10_126_8 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: choose lifts in `S` of a finite set of algebra generators of
-- `S ⧸ I.map (algebraMap R S)` over `R ⧸ I`, let `A ⊆ S` be the `R`-subalgebra they generate, and
-- apply Nakayama's lemma to the `R`-module cokernel of `A → S` using that `I` is nilpotent.
/-- Lemma 10.126.8: if `I` is a nilpotent ideal of `R` and the quotient algebra
`S ⧸ I.map (algebraMap R S)` is of finite type over `R ⧸ I`, then `S` is of finite type over
`R`. -/
theorem finiteType_of_quotient_finiteType_of_isNilpotent (I : Ideal R) (hI : IsNilpotent I)
    [Algebra.FiniteType (R ⧸ I) (S ⧸ I.map (algebraMap R S))] : Algebra.FiniteType R S := by
  classical
  let J : Ideal S := I.map (algebraMap R S)
  -- First regard the quotient algebra as a finite-type `R`-algebra via `R → R ⧸ I → S ⧸ J`.
  have hquot_ft : Algebra.FiniteType R (S ⧸ J) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R (R ⧸ I)) inferInstance
  obtain ⟨t, ht⟩ := hquot_ft.out
  -- Choose lifts in `S` of a finite generating set of the quotient algebra.
  choose l hl using fun x : t ↦ Ideal.Quotient.mkₐ_surjective R J x.1
  let A : Subalgebra R S := Algebra.adjoin R (Set.range l)
  let ψ : A →ₐ[R] S ⧸ J := (Ideal.Quotient.mkₐ R J).comp A.val
  have hψ : Function.Surjective ψ := by
    -- The range of `ψ` contains the chosen quotient generators, hence it is the whole quotient.
    have hgen : (t : Set (S ⧸ J)) ⊆ ψ.range := by
      intro x hx
      let xt : t := ⟨x, hx⟩
      exact (AlgHom.mem_range ψ).2 ⟨⟨l xt, Algebra.subset_adjoin (Set.mem_range_self xt)⟩, hl xt⟩
    have hrange : ψ.range = ⊤ := by
      apply top_unique
      rw [← ht]
      exact Algebra.adjoin_le_iff.mpr hgen
    exact (AlgHom.range_eq_top ψ).mp hrange
  -- Surjectivity modulo `I` says `A + IS = S`, so Nakayama upgrades `A` to all of `S`.
  have hsup : A.toSubmodule ⊔ I • (⊤ : Submodule R S) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro s
    obtain ⟨a, ha⟩ := hψ ((Ideal.Quotient.mkₐ R J) s)
    have hmk : (Ideal.Quotient.mkₐ R J) a.1 = (Ideal.Quotient.mkₐ R J) s := by
      simpa [ψ] using ha
    have hzero : (Ideal.Quotient.mkₐ R J) (s - a.1) = 0 := by
      rw [map_sub, hmk, sub_self]
    have hmemJ : s - a.1 ∈ J := (Ideal.Quotient.eq_zero_iff_mem).1 hzero
    have hmemSmul : s - a.1 ∈ I • (⊤ : Submodule R S) := by
      simpa [J, Ideal.smul_top_eq_map] using hmemJ
    have hsum : a.1 + (s - a.1) = s := by
      abel
    exact Submodule.mem_sup.2 ⟨a.1, a.2, s - a.1, hmemSmul, hsum⟩
  have hA_top_submodule : A.toSubmodule = ⊤ :=
    eq_top_of_sup_eq_top_of_isNilpotent I A.toSubmodule (⊤ : Submodule R S) hsup hI
  have hA_top : A = ⊤ := Subalgebra.toSubmodule_injective hA_top_submodule
  -- The lifted generators make `A` finite type, and `A = S` transfers this to `S`.
  have hA_ft : Algebra.FiniteType R A :=
    Algebra.FiniteType.adjoin_of_finite (R := R) (t := Set.range l) (Set.finite_range l)
  let e : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hA_top).trans Subalgebra.topEquiv
  exact Algebra.FiniteType.equiv hA_ft e

end

/-! ### Lemma_10_126_9 (from Chap10) -/
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

/-! ### Lemma_10_126_10 (from Chap10) -/
/-
Domain-style sampling:
* primary domain: localization of `R`-algebra maps at a prime complement and passage to quotients
  by extended ideals;
* sampled owner declarations:
  `IsLocalization.mapₐ`,
  `Ideal.quotientMapₐ`,
  `Ideal.map_le_iff_le_comap`,
  `Localization.awayMapₐ`;
* best owner abstraction:
  the canonical localized quotient comparison algebra map built from `IsLocalization.mapₐ`
  and `Ideal.quotientMapₐ`;
* layer:
  the main existence statement is `source-facing`, while the localized quotient map is a
  `bridge/view` built from the owner localization and quotient constructions;
* primitive data:
  `f`, `I`, `q`, and the finite type / finite presentation / flatness hypotheses;
* derived API:
  the induced quotient algebra map on localizations modulo `I`.
-/

section

universe u v w

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {S' : Type w} [CommRing S'] [Algebra R S']

variable (f : S →ₐ[R] S') (I : Ideal R) (q : Ideal S) [q.IsPrime]

local notation "Sq" => Localization q.primeCompl
local notation "Sqf" => Localization (Submonoid.map (f : S →+* S') q.primeCompl)

private theorem ideal_map_le_comap_map_of_algHom
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (I : Ideal R) :
    Ideal.map (algebraMap R A) I ≤ Ideal.comap f (Ideal.map (algebraMap R B) I) :=
  (Ideal.map_le_iff_le_comap).mp <| by
    calc
      Ideal.map (f : A →+* B) (Ideal.map (algebraMap R A) I) =
          Ideal.map ((f : A →+* B).comp (algebraMap R A)) I := by
            rw [Ideal.map_map]
      _ = Ideal.map (algebraMap R B) I := by
            congr 1
            ext r
            exact f.commutes r
      _ ≤ Ideal.map (algebraMap R B) I := le_rfl

/-- The quotient map modulo `I` induced by the localized map at `q.primeCompl`. -/
noncomputable abbrev localizedQuotientMapModIdealAtPrimeCompl (I : Ideal R) :
    Sq ⧸ Ideal.map (algebraMap R Sq) I →ₐ[R]
      Sqf ⧸ Ideal.map (algebraMap R Sqf) I := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  let localizedMap : Sq →ₐ[R] Localization (Algebra.algebraMapSubmonoid S' q.primeCompl) := by
    let g : Sq →ₐ[Sq] Localization (Algebra.algebraMapSubmonoid S' q.primeCompl) :=
      IsLocalization.mapₐ q.primeCompl Sq Sq
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
        (Algebra.ofId S S')
    exact
      { __ := g.toRingHom
        commutes' := fun r ↦ by
          simpa [IsScalarTower.algebraMap_eq R S Sq,
            IsScalarTower.algebraMap_eq R S
              (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))] using
            g.commutes ((algebraMap R Sq) r) }
  exact
    Ideal.quotientMapₐ
      (Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I)
      localizedMap
      (ideal_map_le_comap_map_of_algHom localizedMap I)

/-- Helper for Lemma 10.126.10: the kernel ideal of a surjective map from a finite-type algebra to
a finitely presented algebra is finitely generated over the source. -/
private theorem kernel_fg_of_surjective_of_finitePresentation_over_source
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hsurj : Function.Surjective f) :
    (RingHom.ker (f : S →+* S')).FG := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  have hfp : RingHom.FinitePresentation (f : S →+* S') :=
    RingHom.FinitePresentation.of_comp_finiteType
      (f := algebraMap R S)
      (g := (f : S →+* S'))
      (by
        simpa [RingHom.finitePresentation_algebraMap] using
          (inferInstance : Algebra.FinitePresentation R S'))
      (by
        simpa [RingHom.finiteType_algebraMap] using
          (inferInstance : Algebra.FiniteType R S))
  letI : Algebra.FinitePresentation S S' := hfp
  -- Finite presentation over the source identifies the kernel as a finitely generated ideal.
  simpa using Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId S S') hsurj

/-- Helper for Lemma 10.126.10: the kernel ideal is a finite `S`-module, which is the form needed
when the source proof localizes the kernel and later applies Nakayama. -/
private theorem kernel_finite_of_surjective_of_finitePresentation_over_source
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hsurj : Function.Surjective f) :
    Module.Finite S (RingHom.ker (f : S →+* S')) := by
  -- Package finite generation of the kernel ideal into the finite-module form used later.
  rw [Module.Finite.iff_fg]
  exact kernel_fg_of_surjective_of_finitePresentation_over_source
    (f := f) (R := R) hsurj

/-- Helper for Lemma 10.126.10: the localized kernel of `f` at `q.primeCompl` vanishes once the
comparison modulo `I` is bijective. -/
private theorem localized_kernel_subsingleton_at_prime_compl_of_bijective_quotient
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hIq : Ideal.map (algebraMap R S) I ≤ q)
    (hsurj : Function.Surjective f)
    [Module.Flat R Sqf]
    (hquot : Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I)) :
    Subsingleton (LocalizedModule q.primeCompl (RingHom.ker (f : S →+* S'))) := by
  let J : Ideal S := RingHom.ker (f : S →+* S')
  letI : Algebra S S' := f.toRingHom.toAlgebra
  letI : Module.Finite S J :=
    kernel_finite_of_surjective_of_finitePresentation_over_source (f := f) (R := R) hsurj
  -- Route correction: keep the source proof's single-object route `J_q → S_q → S'_q` and avoid
  -- switching to an unrelated recursion or ad hoc kernel argument.
  have hsub :
      Algebra.algebraMapSubmonoid S' q.primeCompl = Submonoid.map (f : S →+* S') q.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  -- The source exact sequence starts from `J = ker(f)` before localization.
  have hExact₀ : Function.Exact J.subtype (Algebra.ofId S S').toLinearMap := by
    simpa [J] using LinearMap.exact_subtype_ker_map ((Algebra.ofId S S').toLinearMap)
  -- TODO: localize the exact sequence `J → S → S'` to `J_q → S_q → S'_q`, identify the quotient
  -- map induced by `S_q → S'_q` with `localizedQuotientMapModIdealAtPrimeCompl f q I`, use
  -- `quotientMapByIdeal_injective_of_exact_of_flat` to deduce `J_q / I J_q = 0`, and then apply
  -- Nakayama over the local ring `Sq` using `hIq`.
  -- Current blocker: the canonical localized codomain for `IsLocalizedModule.map_exact` and the
  -- existing quotient comparison map live on propositionally equal localization submonoids, and
  -- the required `R → Sq → Sqf` tower does not normalize definitionally enough for the quotient
  -- bridge to elaborate without a dedicated coercion-stable lemma.
  sorry

-- Proof sketch: let `J = RingHom.ker f`. Finite presentation of `S'` and finite type of `S`
-- imply that `J` is finitely generated. Flatness of the localized target over `R` identifies the
-- kernel of `(S_q / I S_q) → (S'_q / I S'_q)` with `J_q / I J_q`; the assumed bijectivity forces
-- this quotient to vanish. Nakayama then gives `J_q = 0`, so `S_q → S'_q` is bijective, and the
-- finite-presentation spreading lemma upgrades this to `S_g → S'_g` for some `g ∉ q`.
/-- Lemma 10.126.10: let `R` be a ring, let `I ⊆ R` be an ideal, let `f : S →ₐ[R] S'` be a
surjective `R`-algebra map, and let `q` be a prime ideal of `S` containing `I S`. If `S` is of
finite type over `R`, `S'` is of finite presentation over `R`, the induced quotient algebra map on
the localizations at `q.primeCompl` modulo `I` is bijective, and the localized target `S'_q` is
flat over `R`,
then there exists `g ∉ q` such that `S_g → S'_g` is bijective. -/
lemma exists_notMem_and_awayMap_bijective_of_localizedQuotient_bijective
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hIq : Ideal.map (algebraMap R S) I ≤ q)
    (hsurj : Function.Surjective f)
    [Module.Flat R Sqf]
    (hquot : Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I)) :
    ∃ g : S, g ∉ q ∧ Function.Bijective (Localization.awayMapₐ f g) :=
  by
  let J : Ideal S := RingHom.ker (f : S →+* S')
  letI : Algebra S S' := f.toRingHom.toAlgebra
  letI : Module.Finite S J := kernel_finite_of_surjective_of_finitePresentation_over_source
    (f := f) (R := R) hsurj
  have hJq :
      Subsingleton (LocalizedModule q.primeCompl J) :=
    localized_kernel_subsingleton_at_prime_compl_of_bijective_quotient
      (f := f) (R := R) (I := I) (q := q) hIq hsurj hquot
  letI : Subsingleton (LocalizedModule q.primeCompl J) := hJq
  obtain ⟨g, hgq, hJaway⟩ := LocalizedModule.exists_subsingleton_away (M := J) q
  have hAwayInj : Function.Injective (Localization.awayMap (f := (f : S →+* S')) g) := by
    rw [Localization.awayMap_injective_iff]
    intro x hx
    obtain ⟨r, hr, hrx⟩ :=
      (LocalizedModule.subsingleton_iff (R := S) (M := J) (S := Submonoid.powers g)).1 hJaway
        ⟨x, hx⟩
    rcases hr with ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simpa [J, Algebra.smul_def, smul_eq_mul] using congrArg Subtype.val hrx
  have hAwaySurj : Function.Surjective (Localization.awayMap (f := (f : S →+* S')) g) := by
    rw [Localization.awayMap_surjective_iff]
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨y, 0, by simp⟩
  refine ⟨g, hgq, ?_⟩
  -- The algebra-valued away map is bijective exactly when the underlying ring map is.
  simpa using ⟨hAwayInj, hAwaySurj⟩

end

/-! ### Lemma_10_126_11 (from Chap10) -/
/-
Domain-style sampling:
* primary domain: commutative algebra of extended ideals and quotient algebra maps under an
  `R`-algebra morphism;
* sampled owner declarations:
  `Ideal.le_comap_map`,
  `Ideal.map_map`,
  `Ideal.quotientMapₐ`,
  `Ideal.IsLocallyNilpotent`;
* best owner abstraction: the induced quotient algebra map is the canonical `Ideal.quotientMapₐ`
  for the extended ideals, with containment supplied from `Ideal.le_comap_map` plus
  functoriality of `Ideal.map`;
* layer: the numbered item is `source-facing`, while the quotient map on extended ideals is only a
  `bridge/view` built directly from the owner quotient construction;
* primitive data: `I`, `f`, and the finite type / finite presentation / flatness hypotheses;
* derived API: the quotient map modulo the extended ideal.
-/

universe u v w

section

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S']

private theorem extendedIdeal_le_comap_extendedIdeal {I : Ideal R} (f : S →ₐ[R] S') :
    Ideal.map (algebraMap R S) I ≤
      Ideal.comap (f : S →+* S') (Ideal.map (algebraMap R S') I) := by
  simpa [Ideal.map_map] using
    (show Ideal.map (algebraMap R S) I ≤
        Ideal.comap (f : S →+* S')
          (Ideal.map (f : S →+* S') (Ideal.map (algebraMap R S) I)) from
      Ideal.le_comap_map)

/-- Helper for Lemma 10.126.11: localizing the extended ideal `I S` at `q.primeCompl`
agrees with extending `I` directly to `S_q`. -/
private theorem localized_extendedIdeal_eq
    {I : Ideal R} (q : Ideal S) [q.IsPrime] :
    Ideal.map (algebraMap S (Localization q.primeCompl)) (Ideal.map (algebraMap R S) I) =
      Ideal.map (algebraMap R (Localization q.primeCompl)) I := by
  -- Rewrite both sides as the image of `I` under the composed structure map `R → S → S_q`.
  rw [Ideal.map_map]
  congr 1

/-- Helper for Lemma 10.126.11: localizing the extended ideal `I S'` at the image of
`q.primeCompl` agrees with extending `I` directly to `S'_q`. -/
private theorem mapped_localized_extendedIdeal_eq
    {I : Ideal R} (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] :
    Ideal.map
        (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl)))
        (Ideal.map (algebraMap R S') I) =
      Ideal.map
        (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I := by
  -- Again, functoriality of `Ideal.map` reduces the statement to the scalar-tower identity.
  rw [Ideal.map_map]
  congr 1

/-- Helper for Lemma 10.126.11: the quotient map modulo `I` sends the source prime-complement
submonoid exactly to the target prime-complement submonoid. -/
private theorem quotient_map_sourceSub_map_eq_targetSub
    {I : Ideal R} (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] :
    Submonoid.map
        (Ideal.quotientMapₐ (Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal f)).toMonoidHom
        (Algebra.algebraMapSubmonoid (S ⧸ Ideal.map (algebraMap R S) I) q.primeCompl) =
      Algebra.algebraMapSubmonoid (S' ⧸ Ideal.map (algebraMap R S') I)
        (Submonoid.map (f : S →+* S') q.primeCompl) := by
  -- Compare both submonoids on generators coming from elements of `q.primeCompl`.
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨f z, ⟨z, hz, rfl⟩, ?_⟩
    simp [Ideal.quotient_map_mkₐ]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S) I) z, ⟨z, hz, rfl⟩, ?_⟩
    simp [Ideal.quotient_map_mkₐ]

/-- Helper for Lemma 10.126.11: under the canonical `S`-algebra structure induced by `f`, the
image of `q.primeCompl` is exactly the algebra-map submonoid on `S'`. -/
private theorem mapped_prime_compl_eq_algebraMapSubmonoid
    (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] :
    letI : Algebra S S' := f.toRingHom.toAlgebra
    Submonoid.map (f : S →+* S') q.primeCompl = Algebra.algebraMapSubmonoid S' q.primeCompl := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  -- Both submonoids consist of the same algebra-map images of elements of `q.primeCompl`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- Helper for Lemma 10.126.11: under the canonical `S`-algebra structure on `S'`, localizing the
extended ideal `I S'` at the owner prime-complement submonoid agrees with extending `I` directly
to the target localization. -/
private theorem owner_localized_extendedIdeal_eq
    {I : Ideal R} (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] :
    letI : Algebra S S' := f.toRingHom.toAlgebra
    Ideal.map
        (algebraMap S' (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)))
        (Ideal.map (algebraMap R S') I) =
      Ideal.map
        (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  -- Both sides are the image of `I` under the same composite `R → S' → S'_q`.
  rw [Ideal.map_map]
  congr 1

/-- Helper for Lemma 10.126.11: the public localized quotient map carries the class of `s / 1`
to the class of `f(s) / 1`. -/
private theorem localizedQuotientMapModIdealAtPrimeCompl_apply_algebraMap
    {I : Ideal R} (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] (s : S) :
    localizedQuotientMapModIdealAtPrimeCompl f q I
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
        (algebraMap S (Localization q.primeCompl) s)) =
      Ideal.Quotient.mk
        (Ideal.map
          (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I)
        (algebraMap S'
          (Localization (Submonoid.map (f : S →+* S') q.primeCompl))
          (f s)) := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  let localizedMap :
      Localization q.primeCompl →ₐ[R]
        Localization (Algebra.algebraMapSubmonoid S' q.primeCompl) := by
    let g :
        Localization q.primeCompl →ₐ[Localization q.primeCompl]
          Localization (Algebra.algebraMapSubmonoid S' q.primeCompl) :=
      IsLocalization.mapₐ q.primeCompl
        (Localization q.primeCompl)
        (Localization q.primeCompl)
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
        (Algebra.ofId S S')
    exact
      { __ := g.toRingHom
        commutes' := fun r ↦ by
          simpa [IsScalarTower.algebraMap_eq R S (Localization q.primeCompl),
            IsScalarTower.algebraMap_eq R S
              (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))] using
            g.commutes ((algebraMap R (Localization q.primeCompl)) r) }
  have hlocalizedMap_apply :
      localizedMap (algebraMap S (Localization q.primeCompl) s) =
        algebraMap S' (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)) (f s) := by
    -- The named localized map still sends `s / 1` to `f(s) / 1`.
    change
      (IsLocalization.mapₐ q.primeCompl
        (Localization q.primeCompl)
        (Localization q.primeCompl)
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
        (Algebra.ofId S S'))
        (algebraMap S (Localization q.primeCompl) s) =
          algebraMap S'
            (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
            (f s)
  -- The localized owner map commutes with the `S`-algebra structure induced by `f`.
    simpa [show (algebraMap S S') s = f s by rfl,
      IsScalarTower.algebraMap_eq S S'
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))]
  -- Re-express the public quotient map using the named localized map before taking the quotient.
  have hleLoc :
      Ideal.map (algebraMap R (Localization q.primeCompl)) I ≤
        Ideal.comap localizedMap.toRingHom
          (Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I) := by
    -- This is the same extended-ideal containment, now for the named localized map.
    have hcomp :
        (localizedMap : Localization q.primeCompl →+* Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)).comp
            (algebraMap R (Localization q.primeCompl)) =
          algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)) := by
      ext r
      exact localizedMap.commutes r
    have hmapeq :
        Ideal.map localizedMap.toRingHom (Ideal.map (algebraMap R (Localization q.primeCompl)) I) =
          Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I := by
      simpa [hcomp] using
        (Ideal.map_map (I := I)
          (f := algebraMap R (Localization q.primeCompl))
          (g := localizedMap.toRingHom))
    calc
      Ideal.map (algebraMap R (Localization q.primeCompl)) I ≤
          Ideal.comap localizedMap.toRingHom
            (Ideal.map localizedMap.toRingHom (Ideal.map (algebraMap R (Localization q.primeCompl)) I)) :=
        Ideal.le_comap_map
      _ = Ideal.comap localizedMap.toRingHom
            (Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I) := by
          rw [hmapeq]
  change
    Ideal.quotientMapₐ
      (Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I)
      localizedMap
      hleLoc
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
        (algebraMap S (Localization q.primeCompl) s)) =
      _
  rw [Ideal.quotient_map_mkₐ]
  simpa using congrArg
    (Ideal.Quotient.mk
      (Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I))
    hlocalizedMap_apply

/-- Helper for Lemma 10.126.11: localizing the global quotient comparison at `q.primeCompl`
identifies it with the localized quotient map used in Lemma `10.126.10`. -/
private theorem localized_quotient_bijective_of_bijective_mod_ideal
    {I : Ideal R} (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime]
    (hquot :
      Function.Bijective
        (Ideal.quotientMapₐ (Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal f))) :
    Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I) := by
  -- Route correction: the quotient isomorphism should first be viewed as an `S`-algebra
  -- equivalence, so the localization step uses the owner prime-complement submonoids directly.
  letI : Algebra S S' := f.toRingHom.toAlgebra
  let IS : Ideal S := Ideal.map (algebraMap R S) I
  let IS' : Ideal S' := Ideal.map (algebraMap R S') I
  let M : Submonoid (S ⧸ IS) := Algebra.algebraMapSubmonoid (S ⧸ IS) q.primeCompl
  let T : Submonoid (S' ⧸ IS') :=
    Algebra.algebraMapSubmonoid (S' ⧸ IS') (Submonoid.map (f : S →+* S') q.primeCompl)
  have hleS : IS ≤ Ideal.comap (Algebra.ofId S S') IS' := by
    -- This is the same containment of extended ideals, now viewed over the base ring `S`.
    simpa [IS, IS', Algebra.ofId_apply] using extendedIdeal_le_comap_extendedIdeal f
  let qmapS : (S ⧸ IS) →ₐ[S] (S' ⧸ IS') :=
    Ideal.quotientMapₐ (R₁ := S) IS' (Algebra.ofId S S') hleS
  have hquotS : Function.Bijective qmapS := by
    -- The `S`-algebra quotient map has the same underlying function as the original hypothesis.
    simpa [qmapS, IS, IS', Algebra.ofId_apply] using hquot
  let eQuot : (S ⧸ IS) ≃ₐ[S] (S' ⧸ IS') := AlgEquiv.ofBijective qmapS hquotS
  have hT : Submonoid.map eQuot.toMonoidHom M = T := by
    -- The quotient map modulo `I` sends the source prime-complement image to the public target
    -- prime-complement image, and `eQuot` has exactly that underlying map.
    simpa [M, T, eQuot, qmapS, IS, IS', Algebra.ofId_apply] using
      quotient_map_sourceSub_map_eq_targetSub (I := I) f q
  let eLocQuot : Localization M ≃ₐ[S] Localization T :=
    IsLocalization.algEquivOfAlgEquiv
      (A := S)
      (S := Localization M)
      (Q := Localization T)
      eQuot
      hT
  let eSrc :
      Localization M ≃+*
        (Localization q.primeCompl ⧸ Ideal.map (algebraMap R (Localization q.primeCompl)) I) :=
    (Localization.algEquiv M
      (Localization q.primeCompl ⧸ Ideal.map (algebraMap S (Localization q.primeCompl)) IS)
        : Localization M ≃ₐ[S ⧸ IS]
            (Localization q.primeCompl ⧸ Ideal.map (algebraMap S (Localization q.primeCompl)) IS)
      ).toRingEquiv.trans (Ideal.quotEquivOfEq (localized_extendedIdeal_eq (I := I) q))
  let eTgt :
      Localization T ≃+*
        (Localization (Submonoid.map (f : S →+* S') q.primeCompl) ⧸
          Ideal.map
            (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I) :=
    (Localization.algEquiv T
      (Localization (Submonoid.map (f : S →+* S') q.primeCompl) ⧸
        Ideal.map
          (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) IS')
        : Localization T ≃ₐ[S' ⧸ IS']
            (Localization (Submonoid.map (f : S →+* S') q.primeCompl) ⧸
              Ideal.map
                (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) IS')
      ).toRingEquiv.trans (Ideal.quotEquivOfEq (mapped_localized_extendedIdeal_eq f q))
  have hSrc_apply (s : S) :
      eSrc (algebraMap (S ⧸ IS) (Localization M) (Ideal.Quotient.mk IS s)) =
        Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
          (algebraMap S (Localization q.primeCompl) s) := by
    -- Unfold the source quotient/localization comparison on the generator represented by `s`.
    change
      Ideal.quotEquivOfEq (localized_extendedIdeal_eq (I := I) q)
          ((Localization.algEquiv M
            (Localization q.primeCompl ⧸
              Ideal.map (algebraMap S (Localization q.primeCompl)) IS))
            (algebraMap (S ⧸ IS) (Localization M) (Ideal.Quotient.mk IS s))) =
        _
    rw [← IsLocalization.mk'_one (M := M) (S := Localization M) (Ideal.Quotient.mk IS s)]
    rw [Localization.algEquiv_mk', IsLocalization.mk'_one]
    simpa [Ideal.Quotient.mk_algebraMap] using
      (Ideal.quotEquivOfEq_mk (localized_extendedIdeal_eq (I := I) q)
        (algebraMap S (Localization q.primeCompl) s))
  have hSrc_symm_apply (s : S) :
      eSrc.symm
          (Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
            (algebraMap S (Localization q.primeCompl) s)) =
        algebraMap (S ⧸ IS) (Localization M) (Ideal.Quotient.mk IS s) := by
    -- The inverse source transport is determined by the forward transport on generators.
    apply eSrc.injective
    rw [RingEquiv.apply_symm_apply, hSrc_apply]
  have hTgt_apply (s : S') :
      eTgt (algebraMap (S' ⧸ IS') (Localization T) (Ideal.Quotient.mk IS' s)) =
        Ideal.Quotient.mk
          (Ideal.map
            (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I)
          (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl)) s) := by
    -- Unfold the target quotient/localization comparison on the generator represented by `s`.
    change
      Ideal.quotEquivOfEq (mapped_localized_extendedIdeal_eq f q)
          ((Localization.algEquiv T
            (Localization (Submonoid.map (f : S →+* S') q.primeCompl) ⧸
              Ideal.map
                (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) IS'))
            (algebraMap (S' ⧸ IS') (Localization T) (Ideal.Quotient.mk IS' s))) =
        _
    rw [← IsLocalization.mk'_one (M := T) (S := Localization T) (Ideal.Quotient.mk IS' s)]
    rw [Localization.algEquiv_mk', IsLocalization.mk'_one]
    simpa [Ideal.Quotient.mk_algebraMap] using
      (Ideal.quotEquivOfEq_mk (mapped_localized_extendedIdeal_eq f q)
        (algebraMap S' (Localization (Submonoid.map (f : S →+* S') q.primeCompl)) s))
  have hQuot_apply (s : S) :
      eQuot (Ideal.Quotient.mk IS s) = Ideal.Quotient.mk IS' (f s) := by
    -- The quotient equivalence itself is induced by the global quotient map modulo `I`.
    simpa [IS, IS', Algebra.ofId_apply] using eQuot.commutes s
  have hLocQuot_apply (s : S) :
      eLocQuot (algebraMap (S ⧸ IS) (Localization M) (Ideal.Quotient.mk IS s)) =
        algebraMap (S' ⧸ IS') (Localization T) (Ideal.Quotient.mk IS' (f s)) := by
    -- The localization equivalence carries quotient generators according to `eQuot`.
    simpa [eLocQuot, hQuot_apply s] using
      (IsLocalization.algEquivOfAlgEquiv_eq
        (S := Localization M)
        (Q := Localization T)
        (h := eQuot)
        (H := hT)
        (x := Ideal.Quotient.mk IS s))
  let psi :
      Localization q.primeCompl ⧸ Ideal.map (algebraMap R (Localization q.primeCompl)) I →+*
        Localization (Submonoid.map (f : S →+* S') q.primeCompl) ⧸
          Ideal.map
            (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I :=
    eTgt.toRingHom.comp (eLocQuot.toRingEquiv.toRingHom.comp eSrc.symm.toRingHom)
  have hpsi_apply (s : S) :
      psi
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
            (algebraMap S (Localization q.primeCompl) s)) =
        Ideal.Quotient.mk
          (Ideal.map
            (algebraMap R (Localization (Submonoid.map (f : S →+* S') q.primeCompl))) I)
          (algebraMap S'
            (Localization (Submonoid.map (f : S →+* S') q.primeCompl))
            (f s)) := by
    -- Evaluate the conjugated comparison directly on the quotient class of `s / 1`.
    simp only [psi, RingHom.comp_apply]
    change
      eTgt (eLocQuot (eSrc.symm (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
        (algebraMap S (Localization q.primeCompl) s)))) = _
    rw [hSrc_symm_apply, hLocQuot_apply, hTgt_apply]
  have hconj :
      psi = localizedQuotientMapModIdealAtPrimeCompl f q I := by
    -- Compare both quotient maps on generators of the localization, then extend across the
    -- quotient and the localization by the standard extensionality lemmas.
    apply Ideal.Quotient.ringHom_ext
    apply IsLocalization.ringHom_ext q.primeCompl
    ext s
    change
      psi
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
            (algebraMap S (Localization q.primeCompl) s)) =
        localizedQuotientMapModIdealAtPrimeCompl f q I
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap R (Localization q.primeCompl)) I)
            (algebraMap S (Localization q.primeCompl) s))
    rw [hpsi_apply, localizedQuotientMapModIdealAtPrimeCompl_apply_algebraMap]
  have hbijPsi : Function.Bijective psi := by
    -- The conjugated map is bijective because it is a composite of three equivalences.
    have hbijPsi' : Function.Bijective (fun x ↦ eTgt (eLocQuot (eSrc.symm x))) := by
      exact Function.Bijective.comp (RingEquiv.bijective eTgt)
        (Function.Bijective.comp (AlgEquiv.bijective eLocQuot) (RingEquiv.bijective eSrc.symm))
    simpa only [psi, RingHom.comp_apply] using hbijPsi'
  have hbijPhi :
      Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I) := by
    -- Transport bijectivity across the direct comparison with the public localized quotient map.
    simpa [hconj] using hbijPsi
  -- Once the localized quotient map is identified with the conjugate of `eLocQuot`, bijectivity
  -- is immediate because conjugation preserves bijectivity.
  exact hbijPhi

/-- Helper for Lemma 10.126.11: if `g ∉ q`, then every power of `g` lies in `q.primeCompl`. -/
private theorem powers_le_prime_compl_of_not_mem
    (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Submonoid.powers g ≤ q.primeCompl :=
  Submonoid.powers_le.2 hgq

/-- Helper for Lemma 10.126.11: if `g ∉ q`, the prime localization `S_q` carries the canonical
`S_g`-algebra structure coming from the inclusion `powers g ≤ q.primeCompl`. -/
@[implicit_reducible] private noncomputable def prime_compl_away_algebra
    (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Algebra (Localization.Away g) (Localization q.primeCompl) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.Away g)
    (Localization q.primeCompl)
    (Submonoid.powers g)
    q.primeCompl
    (powers_le_prime_compl_of_not_mem q g hgq)

/-- Helper for Lemma 10.126.11: after applying `f`, every power of `f g` lies in the image of
`q.primeCompl`. -/
private theorem mapped_powers_le_mapped_prime_compl_of_not_mem
    (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Submonoid.powers (f g) ≤ Submonoid.map (f : S →+* S') q.primeCompl := by
  rw [← Submonoid.map_powers]
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, powers_le_prime_compl_of_not_mem q g hgq hy, rfl⟩

/-- Helper for Lemma 10.126.11: after mapping `g` to `S'`, the target prime localization carries
the canonical `S'_{f(g)}`-algebra structure coming from the image inclusion. -/
@[implicit_reducible] private noncomputable def mapped_prime_compl_away_algebra
    (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Algebra (Localization.Away (f g))
      (Localization (Submonoid.map (f : S →+* S') q.primeCompl)) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.Away (f g))
    (Localization (Submonoid.map (f : S →+* S') q.primeCompl))
    (Submonoid.powers (f g))
    (Submonoid.map (f : S →+* S') q.primeCompl)
    (mapped_powers_le_mapped_prime_compl_of_not_mem f q g hgq)

/-- Helper for Lemma 10.126.11: for the canonical `S`-algebra structure on `S'`, every power of
`algebraMap S S' g` lies in the prime-complement image. -/
private theorem algebraMap_powers_le_prime_compl_of_not_mem
    [Algebra S S'] (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Submonoid.powers (algebraMap S S' g) ≤ Algebra.algebraMapSubmonoid S' q.primeCompl := by
  rw [← Submonoid.map_powers]
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, powers_le_prime_compl_of_not_mem q g hgq hy, rfl⟩

/-- Helper for Lemma 10.126.11: with the canonical `S`-algebra structure on `S'`, the target
prime localization is naturally an algebra over `S'_{g}`. -/
@[implicit_reducible] private noncomputable def algebraMap_prime_compl_away_algebra
    [Algebra S S'] (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q) :
    Algebra (Localization.Away (algebraMap S S' g))
      (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.Away (algebraMap S S' g))
    (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
    (Submonoid.powers (algebraMap S S' g))
    (Algebra.algebraMapSubmonoid S' q.primeCompl)
    (algebraMap_powers_le_prime_compl_of_not_mem q g hgq)

/-- Helper for Lemma 10.126.11: once the away map `S_g → S'_g` is bijective and `g ∉ q`, the
induced map is already bijective at every prime in the basic open `D(g)`. -/
private theorem prime_localization_bijective_of_away_linear_bijective
    [Algebra S S'] (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q)
    (hawayLinear :
      Function.Bijective (LocalizedModule.map (Submonoid.powers g) (Algebra.linearMap S S'))) :
    Function.Bijective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')) := by
  let p : PrimeSpectrum S := ⟨q, inferInstance⟩
  have hp :
      Function.Bijective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')) := by
    have hbasic :
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
          { p : PrimeSpectrum S |
            Function.Bijective
              (LocalizedModule.map p.asIdeal.primeCompl (Algebra.linearMap S S')) } :=
      basicOpen_subset_moduleMapIsomorphismLocus_of_bijective_away
        (R := S) (M := S) (N := S') (φ := Algebra.linearMap S S') hawayLinear
    have hp_mem : p ∈ PrimeSpectrum.basicOpen g := by
      exact (PrimeSpectrum.mem_basicOpen g p).2 hgq
    simpa [p] using hbasic hp_mem
  exact hp

/-- Helper for Lemma 10.126.11: the away algebra map `S_g → S'_g` is the owner map whose
bijectivity is equivalent to bijectivity of the localized module map on `S`-modules. -/
private theorem away_localized_linear_bijective_of_away_alg_bijective
    [Algebra S S'] (g : S)
    (haway : Function.Bijective (Localization.awayMapₐ (Algebra.ofId S S') g)) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers g) (Algebra.linearMap S S')) := by
  let awayMapS : Localization.Away g →ₐ[S] Localization.Away (algebraMap S S' g) :=
    Localization.awayMapₐ (Algebra.ofId S S') g
  letI : Algebra (Localization.Away g) (Localization.Away (algebraMap S S' g)) :=
    awayMapS.toAlgebra
  letI : IsScalarTower S (Localization.Away g) (Localization.Away (algebraMap S S' g)) :=
    IsScalarTower.of_algebraMap_eq fun s ↦ by
      exact (awayMapS.commutes s).symm
  -- Rewrite the public localized module map into the owner `IsLocalizedModule.map`.
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Algebra.linearMap S (Localization.Away g))
    ((IsScalarTower.toAlgHom S S' (Localization.Away (algebraMap S S' g))).toLinearMap)]
  -- Then identify that owner map with the canonical away algebra map.
  rw [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ
    (M := Submonoid.powers g)
    (R := S)
    (A := S')
    (Rₚ := Localization.Away g)
    (Aₚ := Localization.Away (algebraMap S S' g))]
  simpa [awayMapS, Localization.awayMapₐ] using haway

/-- Helper for Lemma 10.126.11: once the away map `S_g → S'_g` is bijective and `g ∉ q`, the
induced map on the prime localizations at `q` is injective. -/
private theorem injective_prime_localization_of_away_bijective
    (f : S →ₐ[R] S') (q : Ideal S) [q.IsPrime] (g : S) (hgq : g ∉ q)
    (haway : Function.Bijective (Localization.awayMapₐ f g)) :
    letI : Algebra S S' := f.toRingHom.toAlgebra
    Function.Injective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')) := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  have hawayS :
      Function.Bijective (Localization.awayMapₐ (Algebra.ofId S S') g) := by
    -- Under the canonical `S`-algebra structure induced by `f`, both away maps are the same map.
    simpa [Algebra.ofId_apply] using haway
  have hawayLinear :
      Function.Bijective (LocalizedModule.map (Submonoid.powers g) (Algebra.linearMap S S')) :=
    away_localized_linear_bijective_of_away_alg_bijective
      (S := S) (S' := S') (g := g) hawayS
  -- Feed the away-localized bijectivity into the already-stable basic-open to prime-local step.
  exact (prime_localization_bijective_of_away_linear_bijective q g hgq hawayLinear).1

/-- Helper for Lemma 10.126.11: for every prime ideal `q ⊆ S`, the induced map on localizations
at `q` is injective. This is the prime-local core of the source proof. -/
private theorem prime_local_injective_of_bijective_mod_ideal
    {I : Ideal R} (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] S')
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.Flat R S']
    (hquot :
      Function.Bijective
        (Ideal.quotientMapₐ (Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal f)))
    (q : Ideal S) [q.IsPrime] :
    letI : Algebra S S' := f.toRingHom.toAlgebra
    Function.Injective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')) := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  have hquotSurj :
      Function.Surjective
        ((Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S') I)).comp f) := by
    intro z
    obtain ⟨zbar, hzbar⟩ := hquot.2 z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (Ideal.map (algebraMap R S) I) zbar
    exact ⟨s, by simpa using hzbar⟩
  -- First recover global surjectivity of `f` from the quotient-surjectivity hypothesis.
  have hsurj : Function.Surjective f :=
    surjective_of_surjective_quotient_of_finiteType_of_locallyNilpotent hI f hquotSurj
  have hIS :
      (Ideal.map (algebraMap R S) I).IsLocallyNilpotent :=
    Ideal.map_isLocallyNilpotent (algebraMap R S) hI
  have hIq : Ideal.map (algebraMap R S) I ≤ q := by
    -- Every prime ideal contains a locally nilpotent ideal.
    exact hIS.trans (nilradical_le_prime q)
  have hquotLoc :
      Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I) :=
    localized_quotient_bijective_of_bijective_mod_ideal f q hquot
  -- Lemma `10.126.10` produces a neighborhood on which the map is already bijective.
  obtain ⟨g, hgq, haway⟩ :=
    exists_notMem_and_awayMap_bijective_of_localizedQuotient_bijective
      (f := f) (I := I) (q := q) hIq hsurj hquotLoc
  -- A further localization from `S_g` to `S_q` preserves injectivity.
  simpa using injective_prime_localization_of_away_bijective f q g hgq haway

-- Proof sketch: Lemma `10.126.9` makes `f` surjective from the surjectivity of the quotient map.
-- By Lemma `10.32.3`, the extended ideals `I S` and `I S'` are locally nilpotent, so every prime
-- of `S` contains `I S`. Localizing at any prime `q ⊆ S`, the induced quotient map remains
-- bijective, and Lemma `10.126.10` yields a neighborhood on which `f` is bijective. Hence every
-- localization `S_q → S'_q` is an isomorphism, and Lemma `10.23.1` then gives injectivity of `f`.
/-- Lemma 10.126.11: let `I ⊆ R` be a locally nilpotent ideal and `f : S →ₐ[R] S'` an
`R`-algebra map. If the induced map `S / I S → S' / I S'` is bijective, `S` is of finite type
over `R`, `S'` is of finite presentation over `R`, and `S'` is flat over `R`, then `f` is
bijective. -/
theorem bijective_of_bijective_mod_ideal_of_locallyNilpotent_of_finiteType_of_finitePresentation_of_flat
    {I : Ideal R} (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] S')
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.Flat R S']
    (hquot :
      Function.Bijective
        (Ideal.quotientMapₐ (Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal f))) :
    Function.Bijective f := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  have hquotSurj :
      Function.Surjective
        ((Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S') I)).comp f) := by
    intro z
    obtain ⟨zbar, hzbar⟩ := hquot.2 z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (Ideal.map (algebraMap R S) I) zbar
    exact ⟨s, by simpa using hzbar⟩
  -- The source proof starts by recovering global surjectivity from the quotient comparison.
  have hsurj : Function.Surjective f :=
    surjective_of_surjective_quotient_of_finiteType_of_locallyNilpotent hI f hquotSurj
  have htfae :
      List.TFAE [
        Function.Injective (Algebra.linearMap S S'),
        ∀ (q : Ideal S) [q.IsPrime],
          Function.Injective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')),
        ∀ (q : Ideal S) [q.IsMaximal],
          Function.Injective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S'))
      ] :=
    injective_localization_tfae (Algebra.linearMap S S')
  have hprime :
      ∀ (q : Ideal S) [q.IsPrime],
        Function.Injective (LocalizedModule.map q.primeCompl (Algebra.linearMap S S')) := by
    intro q hq
    letI : q.IsPrime := hq
    simpa using prime_local_injective_of_bijective_mod_ideal hI f hquot q
  have hlininj : Function.Injective (Algebra.linearMap S S') :=
    (htfae.out 0 1).mpr hprime
  -- Injectivity of the `S`-linear map is exactly injectivity of the underlying algebra map.
  have hinj : Function.Injective f := by
    simpa using hlininj
  exact ⟨hinj, hsurj⟩

end
