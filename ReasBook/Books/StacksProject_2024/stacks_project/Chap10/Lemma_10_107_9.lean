import StacksProject_2024.stacks_project.Chap10.Lemma_10_107_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsEpi R S]

private theorem fiber_primeSpectrum_subsingleton (p : PrimeSpectrum R) :
    Subsingleton (PrimeSpectrum (p.asIdeal.Fiber S)) := sorry

-- Proof sketch: identify the fiber over `p` with `Spec (κ(p) ⊗[R] S)` using
-- `PrimeSpectrum.preimageEquivFiber`. Base change preserves `Algebra.IsEpi`, so Lemma `10.107.8`
-- applied to `κ(p) → κ(p) ⊗[R] S` shows that this fiber spectrum is subsingleton.
/-- Lemma 10.107.9 (1): if `R → S` is an epimorphism of commutative rings, then the induced map
`Spec(S) → Spec(R)` is injective. -/
theorem spec_comap_injective_of_isEpi :
    Function.Injective (comap (algebraMap R S)) := by
  intro q₁ q₂ hq
  let p : PrimeSpectrum R := comap (algebraMap R S) q₁
  let e := preimageEquivFiber R S p
  have hsub : Subsingleton (PrimeSpectrum (p.asIdeal.Fiber S)) :=
    fiber_primeSpectrum_subsingleton p
  have hfiber :
      Subsingleton (comap (algebraMap R S) ⁻¹' ({p} : Set (PrimeSpectrum R))) :=
    let _ := hsub
    e.injective.subsingleton
  have hq₁ : comap (algebraMap R S) q₁ = p := rfl
  have hq₂ : comap (algebraMap R S) q₂ = p := by
    simpa [p] using hq.symm
  exact congr_arg Subtype.val <| hfiber.elim ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩

-- Proof sketch: the induced map `(q ∩ R).ResidueField → q.ResidueField` is again an epimorphism
-- of `((q ∩ R).ResidueField)`-algebras. Since both source and target are fields, Lemma `10.107.8`
-- forces this map to be an algebra equivalence, hence bijective.
/-- Lemma 10.107.9 (2): for `q : Spec(S)`, the canonical map
`κ(q ∩ R) → κ(q)` is bijective. -/
theorem residueField_map_bijective_of_isEpi (q : PrimeSpectrum S) :
    Function.Bijective
      (Ideal.ResidueField.map (q.asIdeal.under R) q.asIdeal (algebraMap R S)
        (Ideal.over_def q.asIdeal (q.asIdeal.under R))) := sorry

end
