import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.IntegerDivisibilityDescent
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.SmithDiagonal

noncomputable section

open scoped BigOperators

universe u v

namespace Representation

section IntegerLatticeSaturation

variable {ι : Type v}
variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
variable [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]

/-- Cast an integer-valued function on a finite index set to a `K`-valued function. This is the
pure lattice analogue of `regularIntegerFunctionCast`. -/
noncomputable def integerFunctionCast :
    (ι → ℤ) →+ (ι → K) where
  toFun f i := (f i : K)
  map_zero' := by
    ext i
    simp
  map_add' f g := by
    ext i
    simp

variable [Fintype ι] [DecidableEq ι]

/-- Extend an integer linear functional on `ι → ℤ` to the corresponding `A`-linear functional on
`ι → K`, using the standard coordinate basis. -/
noncomputable def intLinearFunctionalCast
    (l : (ι → ℤ) →ₗ[ℤ] ℤ) :
    (ι → K) →ₗ[A] K where
  toFun x := ∑ i : ι, (l (Pi.single i (1 : ℤ)) : K) * x i
  map_add' x y := by
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' a x := by
    simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm, Algebra.smul_def]

omit [IsLocalRing A] [IsDomain A] [IsFractionRing A K] [CharZero K] in
/-- The extended functional agrees with the original integer functional on cast integer-valued
functions. -/
theorem intLinearFunctionalCast_integerFunctionCast
    (l : (ι → ℤ) →ₗ[ℤ] ℤ) (f : ι → ℤ) :
    intLinearFunctionalCast (A := A) (K := K) l
        (integerFunctionCast (K := K) f) =
      (l f : K) := by
  classical
  have hsum : (∑ i : ι, f i • Pi.single i (1 : ℤ)) = f := by
    ext i
    simp [Pi.single_apply]
  calc
    intLinearFunctionalCast (A := A) (K := K) l
        (integerFunctionCast (K := K) f)
        = ∑ i : ι, (l (Pi.single i (1 : ℤ)) : K) * (f i : K) := by
          simp [intLinearFunctionalCast, integerFunctionCast]
    _ = ∑ i : ι, (f i : K) * (l (Pi.single i (1 : ℤ)) : K) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : ι, (l (f i • Pi.single i (1 : ℤ)) : K) := by
      apply Finset.sum_congr rfl
      intro i _
      have hli :
          l (f i • Pi.single i (1 : ℤ)) =
            f i * l (Pi.single i (1 : ℤ)) := by
        simpa using (l.map_smul (f i) (Pi.single i (1 : ℤ)))
      rw [hli]
      simp
    _ = ((∑ i : ι, l (f i • Pi.single i (1 : ℤ))) : ℤ) := by
      simp
    _ = (l (∑ i : ι, f i • Pi.single i (1 : ℤ)) : K) := by
      simp [map_sum]
    _ = (l f : K) := by
      rw [hsum]

omit [IsLocalRing A] [IsDomain A] [IsFractionRing A K] [CharZero K] in
/-- Applying an integer linear functional to a cast span member lands in the `A`-span of any
integer rank-one lattice containing that functional on the original lattice. -/
theorem intLinearFunctionalCast_mem_span_singleton_of_integerFunctionCast_mem_span
    (N : Submodule ℤ (ι → ℤ))
    (l : (ι → ℤ) →ₗ[ℤ] ℤ) (a : ℤ)
    (hlN :
      ∀ x : ι → ℤ, x ∈ N →
        l x ∈ Submodule.span ℤ ({a} : Set ℤ))
    {f : ι → ℤ}
    (hf :
      integerFunctionCast (K := K) f ∈
        Submodule.span A
          (integerFunctionCast (K := K) '' (N : Set (ι → ℤ)))) :
    (l f : K) ∈
      Submodule.span A ({algebraMap A K (a : A)} : Set K) := by
  classical
  let L : (ι → K) →ₗ[A] K := intLinearFunctionalCast (A := A) (K := K) l
  have hmap :
      L (integerFunctionCast (K := K) f) ∈
        (Submodule.span A
          (integerFunctionCast (K := K) '' (N : Set (ι → ℤ)))).map L := by
    exact Submodule.mem_map.mpr ⟨integerFunctionCast (K := K) f, hf, rfl⟩
  have hmap' :
      L (integerFunctionCast (K := K) f) ∈
        Submodule.span A
          (L '' (integerFunctionCast (K := K) '' (N : Set (ι → ℤ)))) := by
    rw [Submodule.map_span] at hmap
    exact hmap
  have hle :
      Submodule.span A
          (L '' (integerFunctionCast (K := K) '' (N : Set (ι → ℤ)))) ≤
        Submodule.span A ({algebraMap A K (a : A)} : Set K) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨z, ⟨x, hxN, rfl⟩, rfl⟩
    rw [intLinearFunctionalCast_integerFunctionCast (A := A) (K := K) l x]
    rcases Submodule.mem_span_singleton.mp (hlN x hxN) with ⟨c, hc⟩
    change (l x : K) ∈ Submodule.span A ({algebraMap A K (a : A)} : Set K)
    rw [Submodule.mem_span_singleton]
    refine ⟨(c : A), ?_⟩
    calc
      (c : A) • algebraMap A K (a : A) =
          algebraMap A K ((c : A) * (a : A)) := by
            rw [Algebra.smul_def, map_mul]
      _ = ((c * a : ℤ) : K) := by
            simp
      _ = (l x : K) := by
            have hcx : ((c * a : ℤ) : K) = (l x : K) :=
              congrArg (fun z : ℤ ↦ (z : K)) (by simpa [smul_eq_mul] using hc)
            exact hcx
  have hfL := hle hmap'
  simpa [L, intLinearFunctionalCast_integerFunctionCast (A := A) (K := K) l f] using hfL

/-- Rank-one prime-to-`p` denominator clearing. If an integer `m`, after casting to the fraction
field, is in the `A`-span of an integer generator `d`, then a prime-to-`p` multiple of `m` lies in
the integer span of `d`. -/
theorem exists_coprime_nsmul_mem_span_singleton_int_of_intCast_mem_span_algebraMap
    (d : ℤ) {m : ℤ}
    (hmem :
      (m : K) ∈ Submodule.span A ({algebraMap A K (d : A)} : Set K)) :
    ∃ n : ℕ,
      Nat.Coprime n p ∧ n • m ∈ Submodule.span ℤ ({d} : Set ℤ) := by
  classical
  by_cases hd0 : d = 0
  · subst d
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    refine ⟨1, Nat.coprime_one_left p, ?_⟩
    have hm0 : m = 0 := by
      have hK : (m : K) = 0 := by
        simpa using ha.symm
      exact Int.cast_injective (by simpa using hK)
    simp [hm0]
  · let dAbs : ℕ := Int.natAbs d
    let e : ℕ := Nat.factorization dAbs p
    let n : ℕ := ordCompl[p] dAbs
    have hdAbs_ne : dAbs ≠ 0 := by
      simpa [dAbs] using (Int.natAbs_ne_zero.mpr hd0)
    have hfactor : p ^ e * n = dAbs := by
      simpa [dAbs, e, n] using Nat.ordProj_mul_ordCompl_eq_self dAbs p
    have hmem_pow :
        (m : K) ∈
          Submodule.span A ({algebraMap A K ((p ^ e : ℕ) : A)} : Set K) := by
      rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
      rw [Submodule.mem_span_singleton]
      refine ⟨a * (Int.sign d : A) * (n : A), ?_⟩
      have hdK :
          algebraMap A K (d : A) =
            (Int.sign d : K) * (n : K) * ((p ^ e : ℕ) : K) := by
        calc
          algebraMap A K (d : A) = (d : K) := by simp
          _ = ((Int.sign d : K) * (dAbs : K)) := by
                dsimp [dAbs]
                have hsignZ :
                    d = (Int.sign d : ℤ) * ((Int.natAbs d : ℕ) : ℤ) :=
                  (Int.sign_mul_natAbs d).symm
                simpa using congrArg (fun z : ℤ ↦ (z : K)) hsignZ
          _ = ((Int.sign d : K) * ((p ^ e * n : ℕ) : K)) := by
                rw [hfactor]
          _ = ((Int.sign d : K) * (n : K) * ((p ^ e : ℕ) : K)) := by
                simp [Nat.cast_mul, mul_comm, mul_left_comm]
      calc
        (a * (Int.sign d : A) * (n : A)) •
            algebraMap A K ((p ^ e : ℕ) : A)
            = algebraMap A K a *
                ((Int.sign d : K) * (n : K) * ((p ^ e : ℕ) : K)) := by
                rw [Algebra.smul_def]
                simp [map_mul, mul_assoc, mul_comm, mul_left_comm]
        _ = a • algebraMap A K (d : A) := by
              rw [Algebra.smul_def, hdK]
        _ = (m : K) := ha
    have hpowe_dvd :
        ((p ^ e : ℕ) : ℤ) ∣ m :=
      int_prime_pow_dvd_of_intCast_mem_span_algebraMap
        (p := p) (A := A) (K := K) e hmem_pow
    rcases hpowe_dvd with ⟨q, hq⟩
    refine ⟨n, ?_, ?_⟩
    · exact (Nat.coprime_ordCompl (Fact.out : Nat.Prime p) hdAbs_ne).symm
    · rw [span_singleton_int_eq_natAbs d]
      rw [Submodule.mem_span_singleton]
      refine ⟨q, ?_⟩
      calc
        q • ((dAbs : ℕ) : ℤ) = q * ((dAbs : ℕ) : ℤ) := by
          simp
        _ = q * (((p ^ e * n : ℕ) : ℤ)) := by
          rw [hfactor]
        _ = n • m := by
          rw [hq]
          simp [mul_assoc, mul_comm]

/-- Coordinatewise prime-to-`p` denominator clearing for diagonal integer lattices. -/
theorem exists_coprime_nsmul_mem_pi_span_of_integerFunctionCast_mem_span_pi_span
    (d : ι → ℤ) {f : ι → ℤ}
    (hf :
      integerFunctionCast (K := K) f ∈
        Submodule.span A
          (integerFunctionCast (K := K) ''
            ((Submodule.pi Set.univ fun i : ι ↦
              Submodule.span ℤ ({d i} : Set ℤ)) : Set (ι → ℤ)))) :
    ∃ n : ℕ,
      Nat.Coprime n p ∧
        n • f ∈
          Submodule.pi Set.univ fun i : ι ↦
            Submodule.span ℤ ({d i} : Set ℤ) := by
  classical
  let D : Submodule ℤ (ι → ℤ) :=
    Submodule.pi Set.univ fun i : ι ↦ Submodule.span ℤ ({d i} : Set ℤ)
  have hcoord :
      ∀ i : ι,
        (f i : K) ∈ Submodule.span A ({algebraMap A K (d i : A)} : Set K) := by
    intro i
    let l : (ι → ℤ) →ₗ[ℤ] ℤ :=
      { toFun := fun x ↦ x i
        map_add' := by simp
        map_smul' := by simp }
    have hlD :
        ∀ x : ι → ℤ, x ∈ D →
          l x ∈ Submodule.span ℤ ({d i} : Set ℤ) := by
      intro x hx
      rw [Submodule.mem_pi] at hx
      exact hx i (Set.mem_univ i)
    simpa [l, D] using
      intLinearFunctionalCast_mem_span_singleton_of_integerFunctionCast_mem_span
        (A := A) (K := K) (N := D) (l := l) (a := d i) hlD hf
  have hclear :
      ∀ i : ι,
        ∃ n : ℕ, Nat.Coprime n p ∧
          n • f i ∈ Submodule.span ℤ ({d i} : Set ℤ) := by
    intro i
    exact
      exists_coprime_nsmul_mem_span_singleton_int_of_intCast_mem_span_algebraMap
        (p := p) (A := A) (K := K) (d := d i) (m := f i) (hcoord i)
  choose n hn using hclear
  refine ⟨∏ i : ι, n i, ?_, ?_⟩
  · exact Nat.Coprime.prod_left fun i _ ↦ (hn i).1
  · rw [Submodule.mem_pi]
    intro i _
    have hdiv : n i ∣ ∏ j : ι, n j := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    rcases hdiv with ⟨q, hq⟩
    have hbase : n i • f i ∈ Submodule.span ℤ ({d i} : Set ℤ) := (hn i).2
    have hscaled : q • (n i • f i) ∈ Submodule.span ℤ ({d i} : Set ℤ) :=
      nsmul_mem hbase q
    have hcoord_eq : (∏ j : ι, n j) • f i = q • (n i • f i) := by
      rw [hq]
      simp [Nat.cast_mul, mul_comm, mul_left_comm]
    change (∏ j : ι, n j) • f i ∈ Submodule.span ℤ ({d i} : Set ℤ)
    rw [hcoord_eq]
    exact hscaled

/-- Smith-normal-form prime-to-`p` denominator clearing. If an integer vector lies in the
`A`-span of the cast of a full-rank integer sublattice, then a prime-to-`p` multiple of that
vector lies in the original sublattice. -/
theorem exists_coprime_nsmul_mem_of_integerFunctionCast_mem_span
    (N : Submodule ℤ (ι → ℤ))
    (b : Module.Basis ι ℤ (ι → ℤ))
    (hfull : Module.finrank ℤ N = Module.finrank ℤ (ι → ℤ))
    {f : ι → ℤ}
    (hf :
      integerFunctionCast (K := K) f ∈
        Submodule.span A (integerFunctionCast (K := K) '' (N : Set (ι → ℤ)))) :
    ∃ n : ℕ, Nat.Coprime n p ∧ n • f ∈ N := by
  classical
  let a : ι → ℤ := Submodule.smithNormalFormCoeffs (N := N) b hfull
  let bTop : Module.Basis ι ℤ (ι → ℤ) :=
    Submodule.smithNormalFormTopBasis (N := N) b hfull
  let bBot : Module.Basis ι ℤ N :=
    Submodule.smithNormalFormBotBasis (N := N) b hfull
  have bBot_eq := Submodule.smithNormalFormBotBasis_def (N := N) b hfull
  have mem_I_iff : ∀ x, x ∈ N ↔ ∀ i, a i ∣ bTop.repr x i := by
    intro x
    simp_rw [bBot.mem_submodule_iff', bBot, bBot_eq]
    have hrepr :
        ∀ (c : ι → ℤ) (i),
          bTop.repr (∑ j : ι, c j • a j • bTop j) i = a i * c i := by
      intro c i
      simp only [← SemigroupAction.mul_smul, bTop.repr_sum_self, mul_comm]
    constructor
    · rintro ⟨c, rfl⟩ i
      exact ⟨c i, hrepr c i⟩
    · rintro ha
      choose c hc using ha
      exact ⟨c, bTop.ext_elem fun i => Eq.trans (hc i) (hrepr c i).symm⟩
  have hcoord :
      ∀ i : ι,
        (bTop.repr f i : K) ∈
          Submodule.span A ({algebraMap A K (a i : A)} : Set K) := by
    intro i
    let l : (ι → ℤ) →ₗ[ℤ] ℤ :=
      { toFun := fun x ↦ bTop.repr x i
        map_add' := by simp
        map_smul' := by
          intro m x
          exact congrArg (fun y : ι →₀ ℤ ↦ y i)
            ((bTop.repr : (ι → ℤ) →ₗ[ℤ] ι →₀ ℤ).map_smul m x) }
    have hlN :
        ∀ x : ι → ℤ, x ∈ N →
          l x ∈ Submodule.span ℤ ({a i} : Set ℤ) := by
      intro x hx
      rcases (mem_I_iff x).1 hx i with ⟨c, hc⟩
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      simpa [l, smul_eq_mul, mul_comm] using hc.symm
    simpa [l] using
      intLinearFunctionalCast_mem_span_singleton_of_integerFunctionCast_mem_span
        (A := A) (K := K) (N := N) (l := l) (a := a i) hlN hf
  have hclear :
      ∀ i : ι,
        ∃ n : ℕ, Nat.Coprime n p ∧
          n • bTop.repr f i ∈ Submodule.span ℤ ({a i} : Set ℤ) := by
    intro i
    exact
      exists_coprime_nsmul_mem_span_singleton_int_of_intCast_mem_span_algebraMap
        (p := p) (A := A) (K := K) (d := a i) (m := bTop.repr f i) (hcoord i)
  choose n hn using hclear
  let nAll : ℕ := ∏ i : ι, n i
  refine ⟨nAll, ?_, ?_⟩
  · exact Nat.Coprime.prod_left fun i _ ↦ (hn i).1
  · refine (mem_I_iff (nAll • f)).2 ?_
    intro i
    have hdiv : n i ∣ nAll := by
      exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    rcases hdiv with ⟨q, hq⟩
    have hbase :
        n i • bTop.repr f i ∈ Submodule.span ℤ ({a i} : Set ℤ) := (hn i).2
    have hscaled :
        q • (n i • bTop.repr f i) ∈ Submodule.span ℤ ({a i} : Set ℤ) :=
      nsmul_mem hbase q
    have hcoord_eq :
        bTop.repr (nAll • f) i = q • (n i • bTop.repr f i) := by
      rw [map_nsmul]
      simp only [Finsupp.nsmul_apply]
      rw [hq]
      simp [Nat.cast_mul, mul_assoc, mul_comm]
    rcases Submodule.mem_span_singleton.mp hscaled with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc
      bTop.repr (nAll • f) i = q • (n i • bTop.repr f i) := hcoord_eq
      _ = a i * c := by
            simpa [smul_eq_mul, mul_comm] using hc.symm

end IntegerLatticeSaturation

section CartanIntegerLatticeSaturation

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]

local instance cartanIntegerLatticeSaturationFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanIntegerLatticeSaturationDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HenselianLocalRing A] [IsDiscreteValuationRing A] in
/-- Cartan-range wrapper for Smith prime-to-`p` denominator clearing. A full-rank integer Cartan
coordinate range is prime-to-`p` saturated inside its mixed-characteristic `A`-span. -/
theorem
    cartanCoordinateAddHom_exists_coprime_nsmul_mem_range_of_regularIntegerFunctionCast_mem_span_of_full_rank
    (b :
      Module.Basis (PRegularConjClass G p) ℤ
        (PRegularConjClass G p → ℤ))
    (hfull :
      Module.finrank ℤ
          ((cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range.toIntSubmodule) =
        Module.finrank ℤ (PRegularConjClass G p → ℤ))
    {f : PRegularConjClass G p → ℤ}
    (hf :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K))) :
    ∃ n : ℕ,
      Nat.Coprime n p ∧
        n • f ∈
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range := by
  classical
  let N : Submodule ℤ (PRegularConjClass G p → ℤ) :=
    (cartanCoordinateAddHom
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range.toIntSubmodule
  have hf_regular :
      regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
        Submodule.span A
          (regularIntegerFunctionCast (p := p) (K := K) (G := G) ''
            (((cartanCoordinateAddHom
                (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
              Set (PRegularConjClass G p → ℤ))) := by
    rwa [projectiveCartanCoordinate_span_eq_span_regularIntegerFunctionCast_image
      (p := p) (A := A) (K := K) (G := G)] at hf
  have hf_integer :
      integerFunctionCast (ι := PRegularConjClass G p) (K := K) f ∈
        Submodule.span A
          (integerFunctionCast (ι := PRegularConjClass G p) (K := K) ''
            (N : Set (PRegularConjClass G p → ℤ))) := by
    simpa [N, integerFunctionCast, regularIntegerFunctionCast,
      AddSubgroup.coe_toIntSubmodule] using hf_regular
  rcases exists_coprime_nsmul_mem_of_integerFunctionCast_mem_span
      (p := p) (A := A) (K := K) (N := N) (b := b) hfull hf_integer with
    ⟨n, hn, hnmem⟩
  exact ⟨n, hn, by simpa [N, AddSubgroup.coe_toIntSubmodule] using hnmem⟩

end CartanIntegerLatticeSaturation

end Representation
