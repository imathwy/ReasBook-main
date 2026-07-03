import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Over
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

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
