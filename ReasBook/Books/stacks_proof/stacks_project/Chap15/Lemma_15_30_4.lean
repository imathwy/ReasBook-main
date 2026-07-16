import Mathlib.Algebra.Homology.ShortComplex.Abelian
import stacks_proof.stacks_project.Chap15.Definition_15_30_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open MonoidalCategory
open ModuleCat
open scoped KoszulComplex

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

/-- Helper for Lemma 15.30.4: the tensorized Koszul complex attached to a finite family. -/
private noncomputable abbrev tensor_koszul_complex {r : ℕ} (f : Fin r → R) :
    ChainComplex (ModuleCat R) ℕ :=
  ((tensorLeft (of R M)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (K^•(f))

/-- Helper for Lemma 15.30.4: homology vanishing transports across an isomorphism of chain
complexes. -/
private theorem isZero_homology_iff_of_iso
    {K L : ChainComplex (ModuleCat R) ℕ} (e : K ≅ L) (i : ℕ) :
    IsZero (K.homology i) ↔ IsZero (L.homology i) := by
  -- The canonical homology comparison of an isomorphism is itself an isomorphism.
  exact Iso.isZero_iff (HomologicalComplex.homologyMapIso e i)

/-- Helper for Lemma 15.30.4: in a short exact sequence of chain complexes, vanishing of the outer
degree-`i` homology objects forces vanishing of the middle degree-`i` homology object. -/
private theorem isZero_homology_middle_of_shortExact_outer
    {T : ShortComplex (ChainComplex (ModuleCat R) ℕ)} (hT : T.ShortExact) (i : ℕ)
    (hX₁ : IsZero (T.X₁.homology i)) (hX₃ : IsZero (T.X₃.homology i)) :
    IsZero (T.X₂.homology i) := by
  -- The long exact homology sequence kills the middle term once the adjacent maps are zero.
  refine (hT.homology_exact₂ i).isZero_X₂ ?_ ?_
  · simpa using hX₁.eq_of_src (HomologicalComplex.homologyMap T.f i) 0
  · simpa using hX₃.eq_of_tgt (HomologicalComplex.homologyMap T.g i) 0

/-- Helper for Lemma 15.30.4: the tensorized Koszul complexes on `Fin.snoc fs f`,
`Fin.snoc fs (f * g)`, and `Fin.snoc fs g` fit into the source-proof short exact row. -/
private theorem tensor_koszul_snoc_mul_shortExact
    {r : ℕ} (fs : Fin r → R) (f g : R) :
    ∃ T : ShortComplex (ChainComplex (ModuleCat R) ℕ),
      T.ShortExact ∧
        Nonempty (tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs f) ≅ T.X₁) ∧
        Nonempty (tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs (f * g)) ≅ T.X₂) ∧
        Nonempty (tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs g) ≅ T.X₃) := by
  -- TODO(Lemma 15.30.4): instantiate the source-faithful exact-sequence proof by tensoring the
  -- cone comparison from Lemma 15.28.11 with `M`, then package the canonical cone row as a short
  -- exact sequence of chain complexes. This is currently blocked because the needed prerequisite
  -- modules `Lemma_15_28_10` and `Lemma_15_28_11` do not have available `.olean` files in the
  -- present prefix state, so the tensorized cone comparison cannot be imported here.
  sorry

namespace IsH1RegularOn

-- Proof sketch: use the exact sequence from Lemma `15.28.11` after tensoring with `M` and take
-- homology in degree `1`; the first and third terms vanish by the two hypotheses, so the middle
-- term vanishes as well.
/-- Lemma 15.30.4, owner form: if `Fin.snoc fs f` and `Fin.snoc fs g` are `M`-`H_1`-regular, then
`Fin.snoc fs (f * g)` is also `M`-`H_1`-regular. -/
@[stacks 062G]
theorem snoc_mul (hf : IsH1RegularOn M (Fin.snoc fs f)) (hg : IsH1RegularOn M (Fin.snoc fs g)) :
    IsH1RegularOn M (Fin.snoc fs (f * g)) := by
  -- Route correction: reduce the owner statement to a single short exact row on the tensorized
  -- Koszul complexes, then invoke the middle-term vanishing lemma on degree `1` homology.
  have hses :
      ∃ T : ShortComplex (ChainComplex (ModuleCat R) ℕ),
        T.ShortExact ∧
          Nonempty (tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs f) ≅ T.X₁) ∧
          Nonempty (tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs (f * g)) ≅ T.X₂) ∧
          Nonempty (tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs g) ≅ T.X₃) :=
    tensor_koszul_snoc_mul_shortExact (R := R) (fs := fs) (f := f) (g := g)
  rcases hses with
    ⟨T, hT, ⟨ef⟩, ⟨efg⟩, ⟨eg⟩⟩
  have hf' : IsZero ((tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs f)).homology 1) := by
    -- Unfold the owner predicate back to the tensorized Koszul complex.
    simpa [IsH1RegularOn, tensor_koszul_complex] using hf
  have hg' : IsZero ((tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs g)).homology 1) := by
    -- The same normalization applies to the right-hand hypothesis.
    simpa [IsH1RegularOn, tensor_koszul_complex] using hg
  have hleft : IsZero (T.X₁.homology 1) := by
    -- Transport the left vanishing statement to the short exact row.
    exact (isZero_homology_iff_of_iso (e := ef) 1).mp hf'
  have hright : IsZero (T.X₃.homology 1) := by
    -- Transport the right vanishing statement to the short exact row.
    exact (isZero_homology_iff_of_iso (e := eg) 1).mp hg'
  have hmiddle : IsZero (T.X₂.homology 1) := by
    -- The long exact homology sequence now forces the middle homology object to vanish.
    exact isZero_homology_middle_of_shortExact_outer hT 1 hleft hright
  -- Transport the middle vanishing statement back to the target owner predicate.
  exact (isZero_homology_iff_of_iso (e := efg) 1).mpr hmiddle

end IsH1RegularOn

namespace IsKoszulRegularOn

-- Proof sketch: apply the long exact homology sequence coming from Lemma `15.28.11` in every
-- positive degree. The outer terms vanish because `Fin.snoc fs f` and `Fin.snoc fs g` are
-- `M`-Koszul-regular, so the middle term vanishes as well.
/-- Lemma 15.30.4, owner form: if `Fin.snoc fs f` and `Fin.snoc fs g` are `M`-Koszul-regular, then
`Fin.snoc fs (f * g)` is also `M`-Koszul-regular. -/
@[stacks 062G]
theorem snoc_mul
    (hf : IsKoszulRegularOn M (Fin.snoc fs f)) (hg : IsKoszulRegularOn M (Fin.snoc fs g)) :
    IsKoszulRegularOn M (Fin.snoc fs (f * g)) := by
  -- Route correction: the source proof is degreewise, so we reuse the same short exact row and
  -- apply the middle-term vanishing lemma in each positive degree.
  have hses :
      ∃ T : ShortComplex (ChainComplex (ModuleCat R) ℕ),
        T.ShortExact ∧
          Nonempty (tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs f) ≅ T.X₁) ∧
          Nonempty (tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs (f * g)) ≅ T.X₂) ∧
          Nonempty (tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs g) ≅ T.X₃) :=
    tensor_koszul_snoc_mul_shortExact (R := R) (fs := fs) (f := f) (g := g)
  rcases hses with
    ⟨T, hT, ⟨ef⟩, ⟨efg⟩, ⟨eg⟩⟩
  intro i hi
  have hf' : IsZero ((tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs f)).homology i) := by
    -- Unfold the owner predicate to the tensorized Koszul complex in degree `i`.
    simpa [IsKoszulRegularOn, tensor_koszul_complex] using hf i hi
  have hg' : IsZero ((tensor_koszul_complex (R := R) (M := M) (Fin.snoc fs g)).homology i) := by
    -- The right-hand hypothesis gives the same vanishing statement in degree `i`.
    simpa [IsKoszulRegularOn, tensor_koszul_complex] using hg i hi
  have hleft : IsZero (T.X₁.homology i) := by
    -- Transport the left vanishing statement to the short exact row.
    exact (isZero_homology_iff_of_iso (e := ef) i).mp hf'
  have hright : IsZero (T.X₃.homology i) := by
    -- Transport the right vanishing statement to the short exact row.
    exact (isZero_homology_iff_of_iso (e := eg) i).mp hg'
  have hmiddle : IsZero (T.X₂.homology i) := by
    -- The same long exact homology argument works in every positive degree.
    exact isZero_homology_middle_of_shortExact_outer hT i hleft hright
  -- Transport the middle vanishing statement back to the target tensorized Koszul complex.
  exact (isZero_homology_iff_of_iso (e := efg) i).mpr hmiddle

end IsKoszulRegularOn

end

end RingTheory.Sequence
