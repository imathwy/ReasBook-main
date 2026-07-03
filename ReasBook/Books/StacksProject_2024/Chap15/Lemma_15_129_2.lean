import StacksProject_2024.Chap15.Lemma_15_129_1_Eilenberg_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]

open LinearMap

/- Domain sampling:
- primary domain: projective modules, their canonical lift into a free module, and Eilenberg
  absorption for non-finitely generated free modules;
- sampled owner declarations: `Module.Projective.iff_split`,
  `nonfinitely_generated_free_absorption_of_split`, `Module.Free.of_equiv`, and `LinearMap.inl`;
- source-facing layer: existence of a free `R`-module `F` for which `P ⊕ F` is free;
- core/canonical layer: the retract data `i : P →ₗ[R] M`, `r : M →ₗ[R] P` with `r.comp i = id`
  supplied by `Module.Projective.iff_split`, together with the free ambient module
  `M × (ℕ →₀ R)` on which Eilenberg absorption acts;
- bridge/view: `Module.Projective.iff_split` is semiring-level and therefore returns only
  `AddCommMonoid` data on the free witness. Over a ring, the source statement is about honest
  modules, so the public witness here is refined to an `AddCommGroup`; this is derived canonically
  from the ring-module structure and should not remain hidden behind the weaker semimodule-level
  interface. -/

-- Proof sketch: use `Module.Projective.iff_split` to realize `P` as a retract of some free module
-- `M`. Stabilize `M` by the countable free module `ℕ →₀ R`, whose non-finite generation is forced
-- unless `R` is subsingleton. Then apply the split-data form of Eilenberg's lemma from Lemma
-- `15.129.1` and transport freeness back along the resulting equivalence.
namespace Module.Projective

/-- Lemma 15.129.2: for a projective `R`-module `P`, there exists a free `R`-module `F` such that
`P ⊕ F` is free; in Lean, the binary direct sum is modeled by the product module `P × F`. -/
theorem exists_free_prod_free :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F),
      Module.Free R (P × F) := by
  classical
  by_cases hR : Subsingleton R
  · letI : Subsingleton R := hR
    letI : Subsingleton P := Module.subsingleton R P
    exact ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance⟩
  · obtain ⟨M, _, _, _, i, r, hr⟩ := iff_split.mp (inferInstance : Module.Projective R P)
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    let G := ℕ →₀ R
    have hG_not_finite : ¬ Module.Finite R G := by
      intro hG
      rcases Module.finite_finsupp_self_iff.1 hG with hsub | hfin
      · exact hR hsub
      · letI : Finite ℕ := hfin
        exact (inferInstance : Infinite ℕ).false
    have hMG_not_finite : ¬ Module.Finite R (M × G) := by
      intro hMG
      letI : Module.Finite R (M × G) := hMG
      have hG_finite : Module.Finite R G :=
        Module.Finite.of_surjective (snd R M G) snd_surjective
      exact hG_not_finite hG_finite
    let i' : P →ₗ[R] M × G := inl R M G ∘ₗ i
    let r' : M × G →ₗ[R] P := r ∘ₗ fst R M G
    have hr' : r'.comp i' = LinearMap.id := by
      ext p
      simpa [i', r'] using LinearMap.congr_fun hr p
    obtain ⟨e⟩ := nonfinitely_generated_free_absorption_of_split hMG_not_finite i' r' hr'
    exact ⟨M × G, inferInstance, inferInstance, inferInstance, Module.Free.of_equiv e.symm⟩

end Module.Projective

end
