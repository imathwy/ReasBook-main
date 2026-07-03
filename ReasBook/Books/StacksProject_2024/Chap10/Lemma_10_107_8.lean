import StacksProject_2024.Chap10.Lemma_10_107_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

-- Proof sketch: split into the cases where `S` is subsingleton or nontrivial. In the nontrivial
-- case, `S` is faithfully flat as a `k`-module because `k` is a field, so the canonical
-- bijectivity theorem from Lemma `10.107.7` applies to `algebraMap k S`; then
-- `AlgEquiv.ofBijective (Algebra.ofId k S)` upgrades that bijection to a `k`-algebra equivalence.
/-- Lemma 10.107.8: if `k → S` is an epimorphism with `k` a field, then `S` is either the zero
ring or isomorphic to `k` as a `k`-algebra. -/
theorem epi_field_subsingleton_or_alg_equiv [Algebra.IsEpi k S] :
    Subsingleton S ∨ Nonempty (k ≃ₐ[k] S) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact .inl hS
  · right
    letI : Module.FaithfullyFlat k S := by
      exact
        { toFlat := inferInstance
          submodule_ne_top := by
            intro m hm
            have hm0 : m = ⊥ := by
              have hbot : (⊥ : Ideal k).IsMaximal := Ideal.bot_isMaximal
              simpa using (hbot.eq_of_le hm.ne_top bot_le).symm
            simp [hm0] }
    refine ⟨AlgEquiv.ofBijective (Algebra.ofId k S) ?_⟩
    exact faithfullyFlat_epi_bijective <| by
      rw [RingHom.faithfullyFlat_algebraMap_iff]
      infer_instance

end
