import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingTheory.Sequence

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage:
* primary domain: regular sequences on modules over commutative rings;
* sampled owner API: `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isWeaklyRegular_append_iff`,
  `Submodule.quotientQuotientEquivQuotientSup`,
  `Submodule.map_smul''`;
* core/canonical owner: `RingTheory.Sequence.IsRegular M rs`;
* layer split: regularity of sequences on `M` is primitive owner data, while
  the quotient-ring presentation for the self-module case is a derived view.
-/

-- Proof sketch: the weakly regular part is exactly
-- `RingTheory.Sequence.isWeaklyRegular_append_iff`. For the nontriviality
-- condition, map the equality `⊤ = (fs ++ gs)M` through the quotient map
-- `M → M / fsM`; the `fs`-part dies and the remaining image is exactly `gs`
-- acting on the quotient module.
/-- Lemma 10.68.7, in owner form: if `fs` is an `M`-regular sequence and `gs`
is regular on the quotient module `M ⧸ (Ideal.ofList fs • ⊤)`, then `fs ++ gs`
is `M`-regular. The textbook ring statement is the specialization `M = R`. -/
theorem isRegular_append_of_isRegular_of_quotient_isRegular
    {fs gs : List R} (hfs : IsRegular M fs)
    (hgs : IsRegular (M ⧸ (Ideal.ofList fs • (⊤ : Submodule R M))) gs) :
    IsRegular M (fs ++ gs) := by
  refine ⟨?_, ?_⟩
  · exact (isWeaklyRegular_append_iff M fs gs).mpr
      ⟨hfs.toIsWeaklyRegular, hgs.toIsWeaklyRegular⟩
  · intro htop
    let S : Submodule R M := Ideal.ofList fs • (⊤ : Submodule R M)
    let T : Submodule R M := Ideal.ofList gs • (⊤ : Submodule R M)
    have htopMap : (⊤ : Submodule R (M ⧸ S)) = (S ⊔ T).map S.mkQ := by
      have := congrArg (Submodule.map S.mkQ) htop
      simpa [S, T, Ideal.ofList_append, Submodule.sup_smul, Submodule.map_top,
        Submodule.range_mkQ] using this
    have htop' : (⊤ : Submodule R (M ⧸ S)) = Ideal.ofList gs • (⊤ : Submodule R (M ⧸ S)) := by
      calc
        (⊤ : Submodule R (M ⧸ S)) = (S ⊔ T).map S.mkQ := htopMap
        _ = S.map S.mkQ ⊔ T.map S.mkQ := by rw [Submodule.map_sup]
        _ = T.map S.mkQ := by rw [Submodule.mkQ_map_self, bot_sup_eq]
        _ = Ideal.ofList gs • (⊤ : Submodule R (M ⧸ S)) := by
          simp [S, T, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    exact hgs.top_ne_smul htop'

end

end RingTheory.Sequence
