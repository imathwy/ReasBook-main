import stacks_proof.stacks_project.Chap19.Definition_19_10_1
import stacks_proof.stacks_project.Chap19.Lemma_19_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/-- Helper for Lemma 19.12.1: the pullback of a proper subobject along an epimorphism is again
proper. -/
lemma pullback_ne_top_of_ne_top
    {C : Type u} [Category.{v} C] [Abelian C] {M N : C}
    (π : M ⟶ N) [Epi π] (P : Subobject N) (hP : P ≠ ⊤) :
    ((Subobject.pullback π).obj P : Subobject M) ≠ ⊤ := by
  intro htop
  -- If the pullback is top, then `π` itself factors through `P`.
  have hTopFactors : ((Subobject.pullback π).obj P : Subobject M).Factors (𝟙 M) := by
    rw [htop]
    refine ⟨𝟙 M, ?_⟩
    simp
  have hFactors : P.Factors π := by
    simpa using (pullback_factors_iff π P (𝟙 M)).1 hTopFactors
  have hArrowEpi : Epi P.arrow := by
    have : Epi (P.factorThru π hFactors ≫ P.arrow) := by
      simpa [P.factorThru_arrow π hFactors] using (inferInstance : Epi π)
    exact epi_of_epi (P.factorThru π hFactors) P.arrow
  have hArrowIso : IsIso P.arrow := isIso_of_mono_of_epi P.arrow
  exact hP ((Subobject.isIso_arrow_iff_eq_top P).mp hArrowIso)

/-- Helper for Lemma 19.12.1: if the composite `f ≫ π` factors through a subobject of `N`, then
`f` factors through its pullback to `M`. -/
lemma factors_pullback_of_comp_factors
    {C : Type u} [Category.{v} C] [Abelian C] {U M N : C}
    (π : M ⟶ N) (P : Subobject N) (f : U ⟶ M)
    (h : P.Factors (f ≫ π)) :
    ((Subobject.pullback π).obj P).Factors f := by
  -- The pullback subobject is characterized by exactly this factorization criterion.
  exact (pullback_factors_iff π P f).2 h

/-- Helper for Lemma 19.12.1: once the image subobject of a morphism is the top subobject, the
morphism is an epimorphism. -/
lemma epi_of_imageSubobject_eq_top
    {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}
    (f : X ⟶ Y) (himage : imageSubobject f = (⊤ : Subobject Y)) :
    Epi f := by
  -- The image arrow is an isomorphism when the image subobject is top.
  have hIso : IsIso (imageSubobject f).arrow :=
    (Subobject.isIso_arrow_iff_eq_top (imageSubobject f)).2 himage
  letI : IsIso (imageSubobject f).arrow := hIso
  -- Then `f` is the composite of the epi image factor map with this isomorphism.
  letI : Epi (factorThruImageSubobject f ≫ (imageSubobject f).arrow) := by
    infer_instance
  simpa [imageSubobject_arrow_comp] using
    (inferInstance : Epi (factorThruImageSubobject f ≫ (imageSubobject f).arrow))

/-
Domain-style sampling for Lemma 19.12.1:
- primary domain: separators in abelian categories, together with shrink-indexed coproducts and
  subobject-cardinality bounds;
- sampled owner declarations:
  `IsSeparator`,
  `isSeparator_iff_exists_not_factors_subobject`,
  `HasCoproduct`,
  `subobject_cardinal_subobject_le_of_shortExact`,
  `Cardinal.mk (Subobject X)`;
- best owner abstraction: the generator input is canonically `IsSeparator U`, the smallness input
  is the local owner `Small.{w} (Subobject N)`, the coproduct input is the actual shrink-indexed
  family `fun _ : Shrink.{w} (Subobject N) ↦ U`, and the size bound is the canonical owner
  `Cardinal.mk (Subobject _)`;
- primitive data: a separator `U`, an epimorphism `π : M ⟶ N`, the proper subobjects of `N`, and
  a `w`-small model of `Subobject N` together with the coproduct of copies of `U` indexed by it;
- derived API: a subobject `M' : Subobject M` with `Epi (M'.arrow ≫ π)` and the induced
  subobject-cardinality bound coming from that canonical shrink-indexed coproduct.

Source/core/bridge triage:
- `source-facing`: the bounded subobject `M' ⊆ M` that still surjects onto `N`;
- `core/canonical`: `IsSeparator`, `Small.{w} (Subobject N)`,
  `HasCoproduct (fun _ : Shrink.{w} (Subobject N) ↦ U)`, `Shrink.{w} (Subobject _)`, and
  `Cardinal.mk (Subobject _)`;
- `bridge/view`: this theorem, which converts the generator-side owner abstractions into the
  Stacks-project bounded-subobject statement. -/

/-- Lemma 19.12.1: if `π : M ⟶ N` is an epimorphism in an abelian category and `U` is a
source-facing generator, formalized by `IsSeparator U`, then some subobject `M' ⊆ M` still
surjects onto `N`, and `Subobject M'` is bounded in cardinality by the subobject lattice of the
coproduct of copies of `U` indexed by the canonical shrink `Shrink.{w} (Subobject N)`. -/
-- Proof sketch: use the separator/strong-generator criterion to choose, for each proper
-- subobject `N' ⊊ N`, a map `U ⟶ M` whose composite with `π` does not factor through `N'`.
-- Assemble these maps into a morphism from the canonical coproduct indexed by
-- `Shrink.{w} (Subobject N)`, let `M'` be its image in `M`, and then use the Chapter 19
-- subobject-cardinality lemmas for subobjects and quotients to bound
-- `Cardinal.mk (Subobject (M' : C))` by the corresponding coproduct bound.
theorem exists_subobject_surjecting_onto_of_epi_le_generator_coproduct_size
    {C : Type u} [Category.{v} C] [Abelian C] {U M N : C}
    [Small.{w} (Subobject N)]
    [HasCoproduct fun _ : Shrink.{w} (Subobject N) ↦ U]
    (hU : IsSeparator U) (π : M ⟶ N) [Epi π] :
    ∃ M' : Subobject M,
      Epi (M'.arrow ≫ π) ∧
        Cardinal.mk (Subobject (M' : C)) ≤
          Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} (Subobject N) ↦ U)) := by
  classical
  let ι : Type w := Shrink.{w} (Subobject N)
  let F : ι → C := fun _ ↦ U
  let P : ι → Subobject N := fun i ↦ (equivShrink (Subobject N)).symm i
  -- For each proper subobject, choose a map from the generator missing its pullback to `M`.
  have hChoose :
      ∀ i : ι, P i ≠ (⊤ : Subobject N) →
        ∃ f : U ⟶ M, ¬ ((Subobject.pullback π).obj (P i)).Factors f := by
    intro i htop
    exact (isSeparator_iff_exists_not_factors_subobject C U).mp hU
      ((Subobject.pullback π).obj (P i))
      (pullback_ne_top_of_ne_top π (P i) htop)
  let φ : ι → (U ⟶ M) := fun i ↦
    if htop : P i = ⊤ then 0 else Classical.choose (hChoose i htop)
  have hφ :
      ∀ i : ι, P i ≠ (⊤ : Subobject N) →
        ¬ ((Subobject.pullback π).obj (P i)).Factors (φ i) := by
    intro i htop
    -- This is the defining property of the chosen map in the proper-subobject case.
    simpa [φ, htop] using Classical.choose_spec (hChoose i htop)
  let g : (∐ F) ⟶ M := Limits.Sigma.desc φ
  let M' : Subobject M := imageSubobject g
  have hImageTop : imageSubobject (M'.arrow ≫ π) = (⊤ : Subobject N) := by
    -- If the image of `M' ⟶ N` were proper, the chosen coproduct summand indexed by that image
    -- would factor through its pullback, contradicting the choice of that summand.
    by_contra htop
    let Q : Subobject N := imageSubobject (M'.arrow ≫ π)
    have hQ : Q ≠ (⊤ : Subobject N) := by
      simpa [Q] using htop
    let iQ : ι := equivShrink (Subobject N) Q
    have hQFactors : Q.Factors (φ iQ ≫ π) := by
      have hImageFactors :
          (imageSubobject (M'.arrow ≫ π)).Factors
            ((Sigma.ι F iQ ≫ factorThruImageSubobject g) ≫ (M'.arrow ≫ π)) := by
        simpa using
          imageSubobject_factors_comp_self (M'.arrow ≫ π)
            (Sigma.ι F iQ ≫ factorThruImageSubobject g)
      have hCompEq :
          ((Sigma.ι F iQ ≫ factorThruImageSubobject g) ≫ (M'.arrow ≫ π)) = φ iQ ≫ π := by
        calc
          ((Sigma.ι F iQ ≫ factorThruImageSubobject g) ≫ (M'.arrow ≫ π))
              = Sigma.ι F iQ ≫ g ≫ π := by
                  simp [M', g, Category.assoc]
          _ = φ iQ ≫ π := by
                change Sigma.ι F iQ ≫ Limits.Sigma.desc φ ≫ π = φ iQ ≫ π
                rw [← Category.assoc, Limits.Sigma.ι_desc]
      simpa [Q] using hCompEq ▸ hImageFactors
    have hPullbackFactors : ((Subobject.pullback π).obj Q).Factors (φ iQ) :=
      factors_pullback_of_comp_factors π Q (φ iQ) hQFactors
    have hPiQ : P iQ = Q := by
      simp [P, iQ]
    have hPiQNeTop : P iQ ≠ (⊤ : Subobject N) := by
      simpa [hPiQ] using hQ
    exact hφ iQ hPiQNeTop (by simpa [hPiQ] using hPullbackFactors)
  have hEpi : Epi (M'.arrow ≫ π) := epi_of_imageSubobject_eq_top (M'.arrow ≫ π) hImageTop
  have hCard :
      Cardinal.mk (Subobject (M' : C)) ≤ Cardinal.mk (Subobject (∐ F)) := by
    let e : (∐ F) ⟶ (M' : C) := factorThruImageSubobject g
    let S : ShortComplex C := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
    have hS : S.ShortExact := by
      -- The image quotient map sits in the standard short exact sequence `ker(e) → source → M'`.
      refine ShortComplex.ShortExact.mk ?_
      simpa [S, e] using ShortComplex.exact_kernel e
    simpa [S, e, M', g] using subobject_cardinal_quotient_le_of_shortExact hS
  refine ⟨M', hEpi, ?_⟩
  simpa [F] using hCard

end CategoryTheory
