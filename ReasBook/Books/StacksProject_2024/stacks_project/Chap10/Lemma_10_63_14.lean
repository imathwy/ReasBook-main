import StacksProject_2024.Chap10.Lemma_10_63_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
variable [IsScalarTower R (R ⧸ I) M]

/- Domain triage: this item lies in commutative algebra of associated primes under a quotient map.
* `source-facing`: the textbook exact-annihilator set `associatedPrimesOfModule`.
* `core/canonical`: mathlib's radical-based owner set `associatedPrimes`.
* `bridge/view`: contraction along the quotient map `Ideal.Quotient.mk I`.
The primitive data here are the annihilator ideals `Ideal.torsionOf ... m`; the quotient theorem is
derived from their canonical map/comap behavior, so the file keeps no extra public helper API.
-/

private lemma quotient_comap_torsionOf_eq_torsionOf (m : M) :
    Ideal.comap (Ideal.Quotient.mk I) (Ideal.torsionOf (R ⧸ I) M m) = Ideal.torsionOf R M m := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff,
    ← algebraMap_smul (R ⧸ I) r m]
  simp [Ideal.Quotient.algebraMap_eq]

private lemma quotient_comap_bot_le_torsionOf (m : M) :
    Ideal.comap (Ideal.Quotient.mk I) ⊥ ≤ Ideal.torsionOf R M m := by
  intro r hr
  rw [Ideal.mem_torsionOf_iff]
  rw [Ideal.mem_comap, Ideal.mem_bot] at hr
  rw [← algebraMap_smul (R ⧸ I) r m]
  change (Ideal.Quotient.mk I) r • m = 0
  simpa using congrArg (fun x : R ⧸ I ↦ x • m) hr

/-- Lemma 10.63.14: the textbook associated primes `Ass(M)` of an `R ⧸ I`-module `M`, viewed in
`Spec(R)` by contraction along `R → R ⧸ I`, are exactly the associated primes of `M` as an
`R`-module. Here the `R`-action on `M` is the one coming from restriction of scalars along the
quotient map. -/
theorem associatedPrimesOfModule_quotient_image_comap_eq :
    Ideal.comap (Ideal.Quotient.mk I) '' associatedPrimesOfModule (R ⧸ I) M =
      associatedPrimesOfModule R M := by
  refine Set.Subset.antisymm ?_ ?_
  · simpa [Ideal.Quotient.algebraMap_eq] using
      (associatedPrimesOfModule_image_comap_subset :
        Ideal.comap (algebraMap R (R ⧸ I)) '' associatedPrimesOfModule (R ⧸ I) M ⊆
          associatedPrimesOfModule R M)
  · intro p hp
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp
    rcases hp with ⟨hp, m, hm⟩
    have hIp : I ≤ p := by
      have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ p := by
        simpa [hm, RingHom.ker_eq_comap_bot] using quotient_comap_bot_le_torsionOf I m
      simpa [Ideal.mk_ker] using hker
    refine ⟨p.map (Ideal.Quotient.mk I), ?_, Ideal.comap_map_mk hIp⟩
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
    refine ⟨Ideal.isPrime_map_quotientMk_of_isPrime hIp, m, ?_⟩
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    rw [Ideal.comap_map_mk hIp, quotient_comap_torsionOf_eq_torsionOf I m, hm]

end
