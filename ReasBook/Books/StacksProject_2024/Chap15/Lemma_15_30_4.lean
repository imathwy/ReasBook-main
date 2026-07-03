import StacksProject_2024.Chap15.Definition_15_30_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/- Domain-style sampling for Lemma 15.30.4:
* primary domain: module-valued `H_1`- and Koszul-regularity of finite families via Koszul
  homology;
* sampled owner declarations: `IsH1RegularOn`, `IsKoszulRegularOn`,
  `koszulComplex_iso_homotopyCofiber_truncate_last`, and
  `koszulComplexOn_snoc_mul_exists_homotopyEquiv_homotopyCofiber`;
* source-facing layer: the two `Fin.snoc` closure statements below;
* core/canonical layer: the Koszul-complex owner `K^•(-)` together with the canonical
  homotopy-cofiber comparison from Lemma `15.28.11`;
* bridge/view layer: the long exact homology argument transporting the homotopy-cofiber model to
  vanishing statements for `IsH1RegularOn` and `IsKoszulRegularOn`;
* primitive vs derived API: the primitive public content here is exactly the `Fin.snoc` owner
  surface, while any list-based reformulation is derived transport across `List.ofFn` and should
  not survive as a parallel theorem.
-/

section

variable {r : ℕ} {fs : Fin r → R} {f g : R}

namespace IsH1RegularOn

-- Proof sketch: use the exact sequence from Lemma `15.28.11` after tensoring with `M` and take
-- homology in degree `1`; the first and third terms vanish by the two hypotheses, so the middle
-- term vanishes as well.
/-- Lemma 15.30.4, owner form: if `Fin.snoc fs f` and `Fin.snoc fs g` are `M`-`H_1`-regular, then
`Fin.snoc fs (f * g)` is also `M`-`H_1`-regular. -/
theorem snoc_mul (hf : IsH1RegularOn M (Fin.snoc fs f)) (hg : IsH1RegularOn M (Fin.snoc fs g)) :
    IsH1RegularOn M (Fin.snoc fs (f * g)) := sorry

end IsH1RegularOn

namespace IsKoszulRegularOn

-- Proof sketch: apply the long exact homology sequence coming from Lemma `15.28.11` in every
-- positive degree. The outer terms vanish because `Fin.snoc fs f` and `Fin.snoc fs g` are
-- `M`-Koszul-regular, so the middle term vanishes as well.
/-- Lemma 15.30.4, owner form: if `Fin.snoc fs f` and `Fin.snoc fs g` are `M`-Koszul-regular, then
`Fin.snoc fs (f * g)` is also `M`-Koszul-regular. -/
theorem snoc_mul
    (hf : IsKoszulRegularOn M (Fin.snoc fs f)) (hg : IsKoszulRegularOn M (Fin.snoc fs g)) :
    IsKoszulRegularOn M (Fin.snoc fs (f * g)) := sorry

end IsKoszulRegularOn

end

end RingTheory.Sequence
