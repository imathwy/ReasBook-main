import Mathlib
import StacksProject_2024.Chap13.Remark_13_33_2
import StacksProject_2024.Chap13.Lemma_13_33_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

section

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A]
variable (H : D ⥤ A)

/- Domain-style sampling for Lemma 13.33.8:
- primary domain: sequential homotopy colimits in triangulated categories and their images under a
  homological functor;
- sampled owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.IsHomotopyColimitOf.exists_presentation`,
  `CategoryTheory.telescopePresentation_compat`,
  `CategoryTheory.sequentialTelescope_shortExact`;
- best owner abstraction: the intrinsic homotopy-colimit predicate
  `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`;
- primitive-vs-derived split:
  the primitive data are the sequential diagram and the owner hypothesis that `Khocolim` is a
  homotopy colimit of it;
  after choosing a distinguished telescope triangle presenting that hypothesis, the induced image
  cocone and the comparison map from the sequential colimit are derived bridge-level API.

Source/core/bridge triage:
- `source-facing`: the statement that `H.obj Khocolim` computes the sequential colimit of the
  image system when `Khocolim` is a homotopy colimit of `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`;
- `core/canonical`: an `IsColimit` witness for a cocone with point `H.obj Khocolim`;
- `bridge/view`: the explicit cocone and comparison map built from a chosen distinguished
  telescope triangle witnessing `IsHomotopyColimitOf (Functor.ofSequence f) Khocolim`. -/

variable {K : ℕ → D} [HasCountableCoproducts D] (f : ∀ n, K n ⟶ K (n + 1))

private theorem homotopyColimitPresentation_compat
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) (n : ℕ) :
    f n ≫ Sigma.ι K (n + 1) ≫ g = Sigma.ι K n ≫ g := by
  let S : ℕ ⥤ D := Functor.ofSequence f
  let ι : ∀ n, S.obj n ⟶ Khocolim := fun n ↦ Sigma.ι K n ≫ g
  let c : Khocolim ⟶ ∐ fun n ↦ S.obj n⟦(1 : ℤ)⟧ :=
    h ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).hom
  have hdesc : Limits.Sigma.desc ι = g := by
    apply Limits.Sigma.hom_ext
    intro n
    simpa [S, ι] using Limits.Sigma.ι_desc ι n
  have hc :
      c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv = h := by
    dsimp [c]
    rw [← PreservesCoproduct.inv_hom]
    simpa [Category.assoc] using
      (congrArg (fun t ↦ h ≫ t)
          (Iso.hom_inv_id (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj))).trans
        (Category.comp_id h)
  have htriangle' :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) S.obj).inv) ∈
          distTriang D := by
    rw [hdesc, hc]
    simpa [S] using hKhocolim
  simpa [S, Functor.ofSequence_map_homOfLE_succ, ι, Category.assoc] using
    telescopePresentation_compat ι c htriangle' n

-- Proof sketch: the triangle compatibility of the structure maps is already provided by the
-- Chapter 13 presentation bridge `telescopePresentation_compat`; applying `H` to that relation
-- gives the cocone law for the image sequence.
private theorem homologicalFunctor_hocolim_cocone_naturality
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) (n : ℕ) :
    H.map (f n) ≫ H.map (Sigma.ι K (n + 1) ≫ g) = H.map (Sigma.ι K n ≫ g) := by
  simpa [Functor.map_comp, Category.assoc] using
    congrArg H.map (homotopyColimitPresentation_compat f g h hKhocolim n)

/-- Applying a functor to a distinguished telescope triangle gives a compatible cocone on the
image sequence. -/
private def homologicalFunctor_hocolim_cocone
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    Cocone (Functor.ofSequence (fun n ↦ H.map (f n))) :=
  Cocone.mk _ <|
    NatTrans.ofSequence
      (fun n ↦ H.map (Sigma.ι K n ≫ g))
      (fun n ↦ by
        simpa [Functor.ofSequence_map_homOfLE_succ] using
          homologicalFunctor_hocolim_cocone_naturality H f g h hKhocolim n)

section

variable [HasColimitsOfShape ℕ A]

/-- The canonical comparison morphism from the sequential colimit of the image system to the
image of an object presented by a distinguished telescope triangle. -/
def homologicalFunctor_hocolim_comparison
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    colimit (Functor.ofSequence (fun n ↦ H.map (f n))) ⟶ H.obj Khocolim :=
  colimit.desc _ (homologicalFunctor_hocolim_cocone H f g h hKhocolim)

end

section

variable [HasColimitsOfShape ℕ A]
variable [IsTriangulated D] [Abelian A] [Functor.IsHomological H]
variable [HasExactColimitsOfShape ℕ A] [PreservesColimitsOfShape (Discrete ℕ) H]

local instance : HasCountableCoproducts A := hasCountableCoproducts_of_sequentialColimits

/-- Helper for Lemma 13.33.8: preserving countable coproducts transports the telescope map of a
sequential diagram to the telescope map of its image sequence. -/
private theorem homologicalFunctor_coproduct_comparison_ι
    {S : ℕ ⥤ D} [HasCoproduct S.obj] (n : ℕ) :
    Sigma.ι (S ⋙ H).obj n ≫ (PreservesCoproduct.iso H S.obj).inv =
      H.map (Sigma.ι S.obj n) := by
  -- TODO: rewrite `PreservesCoproduct.iso` through `sigmaComparison` and then use
  -- `Limits.map_ι_comp_inv_sigmaComparison`.
  sorry

/-- Helper for Lemma 13.33.8: preserving countable coproducts transports the telescope map of a
sequential diagram to the telescope map of its image sequence. -/
private theorem homologicalFunctor_telescope_map_compat
    {S : ℕ ⥤ D} [HasCoproduct S.obj] :
    H.map (sequentialTelescopeMap S) ≫ (PreservesCoproduct.iso H S.obj).hom =
      (PreservesCoproduct.iso H S.obj).hom ≫ sequentialTelescopeMap (S ⋙ H) := by
  -- TODO: compute on each summand using `homologicalFunctor_coproduct_comparison_ι` and the
  -- explicit formula for `sequentialTelescopeMap`.
  sorry

/-- Helper for Lemma 13.33.8: the coproduct map built from the image structure maps is the
transport of `H.map g` along the coproduct comparison isomorphism. -/
private theorem homologicalFunctor_sigma_desc_eq
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) :
    Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) =
      (PreservesCoproduct.iso H K).inv ≫ H.map g := by
  -- TODO: apply `Limits.sigmaComparison_map_desc` to the family `n ↦ Sigma.ι K n ≫ g`.
  sorry

/-- Helper for Lemma 13.33.8: applying `H` to the first two morphisms of the distinguished
telescope triangle gives the exact image short complex on `∐ H(Kₙ)`. -/
private theorem homologicalFunctor_hocolim_sigma_desc_exact
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    (ShortComplex.mk
      (sequentialTelescopeMap (Functor.ofSequence (fun n ↦ H.map (f n))))
      (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)))
      (sequentialTelescopeMap_comp_sigmaDesc
        (Functor.ofSequence (fun n ↦ H.map (f n)))
        (fun n ↦ H.map (Sigma.ι K n ≫ g))
        (fun n ↦ by
          simpa [Functor.ofSequence_map_homOfLE_succ] using
            homologicalFunctor_hocolim_cocone_naturality H f g h hKhocolim n))).Exact := by
  -- TODO: transport `H.map_distinguished_exact` across `ShortComplex.isoMk` using
  -- `homologicalFunctor_telescope_map_compat` and `homologicalFunctor_sigma_desc_eq`.
  sorry

/-- Helper for Lemma 13.33.8: rotating the distinguished telescope triangle gives exactness of
the image map `∐ H(Kₙ) ⟶ H(K)` followed by `H.map h`. -/
private theorem homologicalFunctor_hocolim_sigma_desc_map_h_zero
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) ≫ H.map h = 0 := by
  -- TODO: rewrite the left map with `homologicalFunctor_sigma_desc_eq` and use
  -- `comp_distTriang_mor_zero₂₃`.
  sorry

/-- Helper for Lemma 13.33.8: rotating the distinguished telescope triangle gives exactness of
the image map `∐ H(Kₙ) ⟶ H(K)` followed by `H.map h`. -/
private theorem homologicalFunctor_hocolim_sigma_desc_map_h_exact
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    (ShortComplex.mk
      (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)))
      (H.map h)
      (homologicalFunctor_hocolim_sigma_desc_map_h_zero (H := H) (f := f) g h hKhocolim)).Exact := by
  -- TODO: apply `H.map_distinguished_exact` to the rotated triangle and transport the first map
  -- through `homologicalFunctor_sigma_desc_eq`.
  sorry

/-- Helper for Lemma 13.33.8: the map from `∐ H(Kₙ)` to `H(K)` induced by the telescope
presentation is epimorphic. -/
private theorem homologicalFunctor_hocolim_sigma_desc_epi
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    Epi (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g))) := by
  -- TODO: prove the shifted image telescope map is mono via Lemma 13.33.6, use the shifted
  -- coproduct comparison to deduce `H.map h = 0`, and then turn
  -- `homologicalFunctor_hocolim_sigma_desc_map_h_exact` into epicity.
  sorry

/-- Helper for Lemma 13.33.8: `H.obj Khocolim` is a cokernel of the image telescope map. -/
private theorem homologicalFunctor_hocolim_sigma_desc_cokernel
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    Nonempty
      (IsColimit
      (CokernelCofork.ofπ
        (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)))
        (sequentialTelescopeMap_comp_sigmaDesc
          (Functor.ofSequence (fun n ↦ H.map (f n)))
          (fun n ↦ H.map (Sigma.ι K n ≫ g))
          (fun n ↦ by
            simpa [Functor.ofSequence_map_homOfLE_succ] using
              homologicalFunctor_hocolim_cocone_naturality H f g h hKhocolim n)))) := by
  -- TODO: combine `homologicalFunctor_hocolim_sigma_desc_exact` and
  -- `homologicalFunctor_hocolim_sigma_desc_epi` via
  -- `ShortComplex.exact_and_epi_g_iff_g_is_cokernel`.
  sorry

-- Proof sketch: apply `H` to the distinguished telescope triangle defining `Khocolim`, use that
-- `H` preserves countable direct sums to identify the first two terms with the coproduct of the
-- sequence `H.obj (K n)`, and then invoke Lemma 13.33.6 to see that both the comparison morphism
-- below and the standard colimit map present cokernels of the same telescope morphism. The
-- comparison morphism is therefore an isomorphism.
/-- Bridge form of Lemma 13.33.8: for a chosen distinguished telescope triangle presenting a
homotopy colimit, the induced comparison morphism from `colim H(Kₙ)` to `H(Khocolim)` is an
isomorphism when `H` is homological and commutes with countable direct sums. -/
theorem homologicalFunctor_hocolim_comparison_is_iso
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    IsIso (homologicalFunctor_hocolim_comparison H f g h hKhocolim) := by
  -- TODO: compare the standard telescope cokernel from Lemma 13.33.6 with
  -- `homologicalFunctor_hocolim_sigma_desc_cokernel`, then identify the resulting isomorphism
  -- with `homologicalFunctor_hocolim_comparison` by checking the two composites with the
  -- canonical epimorphism `Sigma.desc (colimit.ι _)`.
  sorry

/-- Lemma 13.33.8: if `Khocolim` is a homotopy colimit of a sequential system
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`, then after applying a homological functor `H` that commutes with countable
direct sums, the resulting cocone on `H.obj (K n)` with point `H.obj Khocolim` is a colimit
cocone. This is the owner-level `IsHomotopyColimitOf` formulation of the lemma. -/
theorem homologicalFunctor_hocolim_exists_isColimit
    {Khocolim : D} (hKhocolim : IsHomotopyColimitOf (Functor.ofSequence f) Khocolim) :
    ∃ c : Cocone (Functor.ofSequence (fun n ↦ H.map (f n))),
      ∃ _ : IsColimit c, c.pt = H.obj Khocolim := by
  obtain ⟨g, h, htriangle⟩ := hKhocolim
  refine ⟨homologicalFunctor_hocolim_cocone H f g h htriangle, ?_, rfl⟩
  let _ : IsIso ((colimit.isColimit (Functor.ofSequence (fun n ↦ H.map (f n)))).desc
      (homologicalFunctor_hocolim_cocone H f g h htriangle)) := by
    simpa [homologicalFunctor_hocolim_comparison] using
      homologicalFunctor_hocolim_comparison_is_iso H f g h htriangle
  exact (colimit.isColimit _).ofPointIso

end

end

end CategoryTheory
