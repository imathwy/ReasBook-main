import Mathlib
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_33_8 (from Chap13) -/
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

/-! ### Lemma_13_33_9 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]

/- Domain-style sampling for Lemma 13.33.9:
- primary domain: represented Hom functors on triangulated categories and sequential homotopy
  colimits;
- sampled owner declarations:
  `CategoryTheory.homologicalFunctor_hocolim_comparison`,
  `CategoryTheory.homologicalFunctor_hocolim_comparison_is_iso`,
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.preadditiveCoyoneda.obj`;
- best owner abstraction: the Chapter 13 bridge owner
  `homologicalFunctor_hocolim_comparison`, specialized to the represented functor
  `preadditiveCoyoneda.obj (op K)`;
- primitive-vs-derived split:
  the primitive data are the sequential diagram `L₀ ⟶ L₁ ⟶ L₂ ⟶ ⋯` and a distinguished telescope
  triangle presenting `Lhocolim`;
  the Hom comparison map is derived API and should be reused from the generic homological-functor
  owner rather than redefined locally.

Source/core/bridge triage:
- `source-facing`: the specialization of the generic homological-functor comparison theorem to the
  represented functor `Hom_D(K,-)`;
- `core/canonical`: `homologicalFunctor_hocolim_comparison_is_iso`;
- `bridge/view`: substituting `H = preadditiveCoyoneda.obj (op K)`. -/

-- Proof sketch: this is exactly Lemma 13.33.8 applied to the canonical homological functor
-- `preadditiveCoyoneda.obj (op K)`, which is the mathematically correct owner for the comparison
-- morphism. The local file keeps only the source-facing specialization, not a duplicate cocone or
-- comparison-map API.
/-- Lemma 13.33.9: if the covariant Hom functor `Hom_D(K,-)` commutes with countable direct sums,
then for any sequential system presented by a distinguished telescope triangle, the canonical map
`colim Hom_D(K, L_n) ⟶ Hom_D(K, hocolim L_n)` is an isomorphism, hence a bijection. -/
theorem preadditiveCoyoneda_hocolim_comparison_is_iso
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {L : ℕ → D} [HasCountableCoproducts D] (f : ∀ n, L n ⟶ L (n + 1))
    {Lhocolim : D} (g : ∐ L ⟶ Lhocolim) (h : Lhocolim ⟶ (∐ L)⟦(1 : ℤ)⟧)
    (hLhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    IsIso
      (homologicalFunctor_hocolim_comparison (preadditiveCoyoneda.obj (op K))
        f g h hLhocolim) := by
  let _ : AB5OfSize.{0, 0} AddCommGrpCat.{v} := AB5OfSize_shrink AddCommGrpCat.{v}
  simpa using
    homologicalFunctor_hocolim_comparison_is_iso (preadditiveCoyoneda.obj (op K))
      f g h hLhocolim

end

end CategoryTheory
