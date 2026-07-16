import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.SmithDiagonal

noncomputable section

universe u x

namespace Representation

section SmithInvariantFactors

variable {ι : Type x}
variable {M : Type u} [AddCommGroup M]

/-- A quotient has the additive invariant-factor list `d`, indexed by `ι`, if every product
decomposition of the quotient into cyclic groups `ZMod (a i)` has moduli `a` equal to `d` after
reindexing.

This packages the uniqueness part of the finite-abelian-group invariant-factor theorem.  The
Smith-normal-form lemmas below are purely formal once this uniqueness certificate is available. -/
def AdditiveInvariantFactorList
    (Q : Type u) [AddCommGroup Q] {ι : Type x} (d : ι → ℕ) : Prop :=
  ∀ a : ι → ℕ,
    Nonempty (Q ≃+ ((i : ι) → ZMod (a i))) →
      ∃ σ : ι ≃ ι, ∀ i, a i = d (σ i)

variable [Finite ι]

/-- If a full quotient has known invariant factors, then the Smith coefficients attached to some
ambient basis are exactly those factors up to a permutation.

The hypothesis `AdditiveInvariantFactorList (M ⧸ N) d` is the only place where uniqueness of
finite abelian invariant factors enters.  The proof applies the canonical
`Submodule.quotientEquivPiZMod` decomposition to the Smith coefficients and then invokes that
uniqueness certificate. -/
theorem exists_smith_coeffs_natAbs_perm_of_invariantFactorList
    (N : Submodule ℤ M)
    (hbasis : Nonempty (Module.Basis ι ℤ M))
    [Finite (M ⧸ N)]
    (d : ι → ℕ)
    (hInv : AdditiveInvariantFactorList (M ⧸ N) d) :
    ∃ (b : Module.Basis ι ℤ M)
      (hfull : Module.finrank ℤ N = Module.finrank ℤ M)
      (σ : ι ≃ ι),
        ∀ i,
          Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b hfull i) =
            d (σ i) := by
  rcases hbasis with ⟨b⟩
  letI : Module.Free ℤ M := Module.Free.of_basis b
  letI : Module.Finite ℤ M := Module.Finite.of_basis b
  have hfull : Module.finrank ℤ N = Module.finrank ℤ M :=
    (Submodule.finiteQuotient_iff (M := M) N).mp inferInstance
  let a : ι → ℕ :=
    fun i ↦ Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b hfull i)
  have hquot : Nonempty (M ⧸ N ≃+ ((i : ι) → ZMod (a i))) := by
    exact ⟨by simpa [a] using (Submodule.quotientEquivPiZMod N b hfull)⟩
  rcases hInv a hquot with ⟨σ, hσ⟩
  exact ⟨b, hfull, σ, hσ⟩

/-- A quotient equivalence with a product of nonzero cyclic factors makes the quotient finite. -/
theorem finite_quotient_of_quotientEquivPiZMod
    (N : Submodule ℤ M)
    (d : ι → ℕ)
    (hd : ∀ i, d i ≠ 0)
    (hquot : Nonempty (M ⧸ N ≃+ ((i : ι) → ZMod (d i)))) :
    Finite (M ⧸ N) := by
  letI : Fintype ι := Fintype.ofFinite ι
  haveI : ∀ i, NeZero (d i) := fun i ↦ ⟨hd i⟩
  rcases hquot with ⟨e⟩
  exact Finite.of_equiv ((i : ι) → ZMod (d i)) e.symm.toEquiv

/-- Quotient-decomposition form of
`exists_smith_coeffs_natAbs_perm_of_invariantFactorList`.

Besides the explicit equivalence `M ⧸ N ≃+ Π i, ZMod (d i)`, the theorem asks for the same
uniqueness certificate transported to that product.  This is the minimal finite-abelian-group
input needed to identify the Smith moduli with the displayed factors. -/
theorem exists_smith_coeffs_natAbs_perm_of_quotientEquivPiZMod
    (N : Submodule ℤ M)
    (hbasis : Nonempty (Module.Basis ι ℤ M))
    (d : ι → ℕ)
    (hd : ∀ i, d i ≠ 0)
    (hquot : Nonempty (M ⧸ N ≃+ ((i : ι) → ZMod (d i))))
    (hunique :
      ∀ a : ι → ℕ,
        Nonempty (((i : ι) → ZMod (d i)) ≃+ ((i : ι) → ZMod (a i))) →
          ∃ σ : ι ≃ ι, ∀ i, a i = d (σ i)) :
    ∃ (b : Module.Basis ι ℤ M)
      (hfull : Module.finrank ℤ N = Module.finrank ℤ M)
      (σ : ι ≃ ι),
        ∀ i,
          Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b hfull i) =
            d (σ i) := by
  rcases hquot with ⟨e⟩
  have hquot' : Nonempty (M ⧸ N ≃+ ((i : ι) → ZMod (d i))) := ⟨e⟩
  haveI : Finite (M ⧸ N) :=
    finite_quotient_of_quotientEquivPiZMod (N := N) d hd hquot'
  refine
    exists_smith_coeffs_natAbs_perm_of_invariantFactorList
      (N := N) hbasis d ?_
  intro a ha
  rcases ha with ⟨ea⟩
  exact hunique a ⟨e.symm.trans ea⟩

/-- Additive-subgroup wrapper for
`exists_smith_coeffs_natAbs_perm_of_invariantFactorList`. -/
theorem addSubgroup_exists_smith_coeffs_natAbs_perm_of_invariantFactorList
    (N : AddSubgroup M)
    (hbasis : Nonempty (Module.Basis ι ℤ M))
    [Finite (M ⧸ N)]
    (d : ι → ℕ)
    (hInv : AdditiveInvariantFactorList (M ⧸ N) d) :
    ∃ (b : Module.Basis ι ℤ M)
      (hfull : Module.finrank ℤ N.toIntSubmodule = Module.finrank ℤ M)
      (σ : ι ≃ ι),
        ∀ i,
          Int.natAbs
              (Submodule.smithNormalFormCoeffs (N := N.toIntSubmodule) b hfull i) =
            d (σ i) := by
  rcases hbasis with ⟨b⟩
  letI : Module.Free ℤ M := Module.Free.of_basis b
  letI : Module.Finite ℤ M := Module.Finite.of_basis b
  haveI : Finite (M ⧸ N.toIntSubmodule) := by
    simpa using (inferInstance : Finite (M ⧸ N))
  have hfull :
      Module.finrank ℤ N.toIntSubmodule = Module.finrank ℤ M :=
    (Submodule.finiteQuotient_iff (M := M) N.toIntSubmodule).mp inferInstance
  let a : ι → ℕ :=
    fun i ↦
      Int.natAbs
        (Submodule.smithNormalFormCoeffs (N := N.toIntSubmodule) b hfull i)
  have hquot : Nonempty (M ⧸ N ≃+ ((i : ι) → ZMod (a i))) := by
    exact ⟨by
      simpa [a] using
        (Submodule.quotientEquivPiZMod N.toIntSubmodule b hfull)⟩
  rcases hInv a hquot with ⟨σ, hσ⟩
  exact ⟨b, hfull, σ, hσ⟩

/-- Additive-subgroup quotient-decomposition form of
`addSubgroup_exists_smith_coeffs_natAbs_perm_of_invariantFactorList`. -/
theorem addSubgroup_exists_smith_coeffs_natAbs_perm_of_quotientEquivPiZMod
    (N : AddSubgroup M)
    (hbasis : Nonempty (Module.Basis ι ℤ M))
    (d : ι → ℕ)
    (hd : ∀ i, d i ≠ 0)
    (hquot : Nonempty (M ⧸ N ≃+ ((i : ι) → ZMod (d i))))
    (hunique :
      ∀ a : ι → ℕ,
        Nonempty (((i : ι) → ZMod (d i)) ≃+ ((i : ι) → ZMod (a i))) →
          ∃ σ : ι ≃ ι, ∀ i, a i = d (σ i)) :
    ∃ (b : Module.Basis ι ℤ M)
      (hfull : Module.finrank ℤ N.toIntSubmodule = Module.finrank ℤ M)
      (σ : ι ≃ ι),
        ∀ i,
          Int.natAbs
              (Submodule.smithNormalFormCoeffs (N := N.toIntSubmodule) b hfull i) =
            d (σ i) := by
  rcases hquot with ⟨e⟩
  have hquot' : Nonempty (M ⧸ N ≃+ ((i : ι) → ZMod (d i))) := ⟨e⟩
  haveI : Finite (M ⧸ N) := by
    letI : Fintype ι := Fintype.ofFinite ι
    haveI : ∀ i, NeZero (d i) := fun i ↦ ⟨hd i⟩
    exact Finite.of_equiv ((i : ι) → ZMod (d i)) e.symm.toEquiv
  refine
    addSubgroup_exists_smith_coeffs_natAbs_perm_of_invariantFactorList
      (N := N) hbasis d ?_
  intro a ha
  rcases ha with ⟨ea⟩
  exact hunique a ⟨e.symm.trans ea⟩

end SmithInvariantFactors

end Representation
