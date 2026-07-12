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

/-- Helper for Lemma 13.33.8: the coproduct-preservation comparison is the inverse of the
canonical sigma comparison. -/
private theorem preservesCoproductIso_hom_eq_inv_sigmaComparison
    {S : ℕ ⥤ D} [HasCoproduct S.obj] :
    (PreservesCoproduct.iso H S.obj).hom =
      inv (sigmaComparison H S.obj) := by
  -- Proof comment: both comparison isomorphisms have the same inverse, so their forward maps
  -- agree by the usual inverse-cancellation criterion.
  apply IsIso.eq_inv_of_hom_inv_id
  simpa [PreservesCoproduct.inv_hom] using
    (Iso.inv_hom_id (PreservesCoproduct.iso H S.obj))

/-- Helper for Lemma 13.33.8: preserving countable coproducts transports the telescope map of a
sequential diagram to the telescope map of its image sequence. -/
private theorem homologicalFunctor_coproduct_comparison_ι
    {S : ℕ ⥤ D} [HasCoproduct S.obj] (n : ℕ) :
    Sigma.ι (S ⋙ H).obj n ≫ (PreservesCoproduct.iso H S.obj).inv =
      H.map (Sigma.ι S.obj n) := by
  -- Proof comment: rewrite the coproduct comparison through `sigmaComparison`, then cancel the
  -- inverse comparison on the right summand inclusion.
  have hhom := preservesCoproductIso_hom_eq_inv_sigmaComparison (H := H) (S := S)
  have hι :
      H.map (Sigma.ι S.obj n) ≫ (PreservesCoproduct.iso H S.obj).hom =
        Sigma.ι (S ⋙ H).obj n := by
    rw [hhom]
    change H.map (Sigma.ι S.obj n) ≫ inv (sigmaComparison H S.obj) =
      Sigma.ι (fun x ↦ H.obj (S.obj x)) n
    exact Limits.map_ι_comp_inv_sigmaComparison H S.obj n
  calc
    Sigma.ι (S ⋙ H).obj n ≫ (PreservesCoproduct.iso H S.obj).inv =
      (H.map (Sigma.ι S.obj n) ≫ (PreservesCoproduct.iso H S.obj).hom) ≫
        (PreservesCoproduct.iso H S.obj).inv := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ (PreservesCoproduct.iso H S.obj).inv) hι.symm
    _ = H.map (Sigma.ι S.obj n) := by
          rw [hhom]
          simp

/-- Helper for Lemma 13.33.8: preserving countable coproducts transports the telescope map of a
sequential diagram to the telescope map of its image sequence. -/
private theorem homologicalFunctor_telescope_map_compat_inv_ι
    {S : ℕ ⥤ D} [HasCoproduct S.obj] (n : ℕ) :
    Sigma.ι (S ⋙ H).obj n ≫ sequentialTelescopeMap (S ⋙ H) ≫
        (PreservesCoproduct.iso H S.obj).inv =
      Sigma.ι (S ⋙ H).obj n ≫ (PreservesCoproduct.iso H S.obj).inv ≫
        H.map (sequentialTelescopeMap S) := by
  -- Route correction: prove the transport first with the inverse coproduct comparison, since the
  -- summand formula matches `map_ι_comp_inv_sigmaComparison` in that orientation.
  rw [Sigma.ι_comp_sequentialTelescopeMap_assoc (K := S ⋙ H) n
    (h := (PreservesCoproduct.iso H S.obj).inv), Preadditive.sub_comp]
  rw [Category.assoc, homologicalFunctor_coproduct_comparison_ι (H := H) (S := S) (n := n)]
  rw [homologicalFunctor_coproduct_comparison_ι (H := H) (S := S) (n := n + 1)]
  rw [← Category.assoc, homologicalFunctor_coproduct_comparison_ι (H := H) (S := S) (n := n)]
  calc
    H.map (Sigma.ι S.obj n) - H.map (S.map (homOfLE (Nat.le_succ n))) ≫
        H.map (Sigma.ι S.obj (n + 1)) =
      H.map (Sigma.ι S.obj n) - H.map (S.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι S.obj (n + 1)) := by
          rw [← Functor.map_comp]
    _ = H.map (Sigma.ι S.obj n - S.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι S.obj (n + 1)) := by
          rw [← Functor.map_sub]
    _ = H.map (Sigma.ι S.obj n ≫ sequentialTelescopeMap S) := by
          have hSigma :
              Sigma.ι S.obj n - S.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι S.obj (n + 1) =
                Sigma.ι S.obj n ≫ sequentialTelescopeMap S := by
            simpa using (Sigma.ι_comp_sequentialTelescopeMap (K := S) n).symm
          rw [hSigma]
    _ = H.map (Sigma.ι S.obj n) ≫ H.map (sequentialTelescopeMap S) := by
          rw [Functor.map_comp]

/-- Helper for Lemma 13.33.8: preserving countable coproducts transports the telescope map of a
sequential diagram to the telescope map of its image sequence. -/
private theorem homologicalFunctor_telescope_map_compat_inv
    {S : ℕ ⥤ D} [HasCoproduct S.obj] :
    sequentialTelescopeMap (S ⋙ H) ≫ (PreservesCoproduct.iso H S.obj).inv =
      (PreservesCoproduct.iso H S.obj).inv ≫ H.map (sequentialTelescopeMap S) := by
  -- Proof comment: compare the two morphisms on each coproduct summand using the summandwise
  -- transport lemma, which packages the stable part of the coproduct-comparison bridge.
  apply Limits.Sigma.hom_ext
  intro n
  exact homologicalFunctor_telescope_map_compat_inv_ι (H := H) (S := S) n

/-- Helper for Lemma 13.33.8: the inverse coproduct-comparison square for the telescope map can
be stated directly in the `Functor.ofSequence (fun n ↦ H.map (f n))` normal form. -/
private theorem homologicalFunctor_ofSequence_telescope_map_compat_inv_ι
    (n : ℕ) :
    Sigma.ι (fun i ↦ H.obj (K i)) n ≫
        sequentialTelescopeMap (Functor.ofSequence (fun m ↦ H.map (f m))) ≫
          (PreservesCoproduct.iso H K).inv =
      Sigma.ι (fun i ↦ H.obj (K i)) n ≫ (PreservesCoproduct.iso H K).inv ≫
        H.map (sequentialTelescopeMap (Functor.ofSequence f)) := by
  -- Route correction: name the explicit image sequence so the telescope-map computation and the
  -- coproduct-leg rewrites all live in one syntactic spelling.
  let G : ℕ ⥤ A := Functor.ofSequence (fun m ↦ H.map (f m))
  change
    Sigma.ι G.obj n ≫ sequentialTelescopeMap G ≫ (PreservesCoproduct.iso H K).inv =
      Sigma.ι G.obj n ≫ (PreservesCoproduct.iso H K).inv ≫
        H.map (sequentialTelescopeMap (Functor.ofSequence f))
  have hCoproductLeg :
      ∀ m : ℕ,
        Sigma.ι G.obj m ≫ (PreservesCoproduct.iso H K).inv =
          H.map (Sigma.ι K m) := by
    intro m
    simpa [G] using
      (homologicalFunctor_coproduct_comparison_ι
        (H := H) (S := Functor.ofSequence f) m)
  have hMap :
      G.map (homOfLE (Nat.le_succ n)) = H.map (f n) := by
    simp [G, Functor.ofSequence_map_homOfLE_succ]
  rw [Sigma.ι_comp_sequentialTelescopeMap_assoc (K := G) n
      (h := (PreservesCoproduct.iso H K).inv), Preadditive.sub_comp]
  rw [Category.assoc, hCoproductLeg n]
  rw [hMap]
  rw [hCoproductLeg (n + 1)]
  rw [← Category.assoc, hCoproductLeg n]
  calc
    H.map (Sigma.ι K n) - H.map (f n) ≫ H.map (Sigma.ι K (n + 1)) =
      H.map (Sigma.ι K n) - H.map (f n ≫ Sigma.ι K (n + 1)) := by
        rw [← Functor.map_comp]
    _ = H.map (Sigma.ι K n - f n ≫ Sigma.ι K (n + 1)) := by
        rw [← Functor.map_sub]
    _ = H.map (Sigma.ι K n ≫ sequentialTelescopeMap (Functor.ofSequence f)) := by
        have hSigma :
            Sigma.ι K n - f n ≫ Sigma.ι K (n + 1) =
              Sigma.ι K n ≫ sequentialTelescopeMap (Functor.ofSequence f) := by
          simpa [Functor.ofSequence_map_homOfLE_succ] using
            (Sigma.ι_comp_sequentialTelescopeMap (K := Functor.ofSequence f) n).symm
        rw [hSigma]
        rfl
    _ = H.map (Sigma.ι K n) ≫ H.map (sequentialTelescopeMap (Functor.ofSequence f)) := by
        rw [Functor.map_comp]

/-- Helper for Lemma 13.33.8: the inverse coproduct-comparison square for the telescope map can
be stated directly in the `Functor.ofSequence (fun n ↦ H.map (f n))` normal form. -/
private theorem homologicalFunctor_ofSequence_telescope_map_compat_inv :
    sequentialTelescopeMap (Functor.ofSequence (fun n ↦ H.map (f n))) ≫
        (PreservesCoproduct.iso H K).inv =
      (PreservesCoproduct.iso H K).inv ≫
        H.map (sequentialTelescopeMap (Functor.ofSequence f)) := by
  -- Proof comment: compare the two telescope maps on each coproduct summand of `∐ H(Kₙ)`,
  -- using the explicit summandwise transport proved just above.
  apply Limits.Sigma.hom_ext
  intro n
  exact homologicalFunctor_ofSequence_telescope_map_compat_inv_ι (H := H) (K := K) (f := f) n

/-- Helper for Lemma 13.33.8: the coproduct map built from the image structure maps is the
transport of `H.map g` along the coproduct comparison isomorphism. -/
private theorem homologicalFunctor_sigma_desc_eq
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) :
    Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) =
      (PreservesCoproduct.iso H K).inv ≫ H.map g := by
  -- Proof comment: check both coproduct maps on each summand using the family-level inclusion
  -- transport, then conclude by coproduct extensionality.
  apply Limits.Sigma.hom_ext
  intro n
  have hι :
      Sigma.ι (fun i ↦ H.obj (K i)) n ≫ (PreservesCoproduct.iso H K).inv =
        H.map (Sigma.ι K n) := by
    simpa using
      (homologicalFunctor_coproduct_comparison_ι
        (H := H) (S := Functor.ofSequence f) (n := n))
  calc
    Sigma.ι (fun i ↦ H.obj (K i)) n ≫ Limits.Sigma.desc (fun i ↦ H.map (Sigma.ι K i ≫ g)) =
      H.map (Sigma.ι K n ≫ g) := by
        rw [Limits.Sigma.ι_desc]
    _ = H.map (Sigma.ι K n) ≫ H.map g := by
        rw [Functor.map_comp]
    _ = (Sigma.ι (fun i ↦ H.obj (K i)) n ≫ (PreservesCoproduct.iso H K).inv) ≫ H.map g := by
        rw [hι]
    _ = Sigma.ι (fun i ↦ H.obj (K i)) n ≫ ((PreservesCoproduct.iso H K).inv ≫ H.map g) := by
        rw [Category.assoc]

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
  -- Route correction: transport the mapped distinguished-triangle exactness using the inverse
  -- coproduct comparison, so the already-proved inverse telescope square applies directly.
  have hExact :
      ((shortComplexOfDistTriangle
        (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h) hKhocolim).map H).Exact := by
    simpa using H.map_distinguished_exact
      (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h) hKhocolim
  have e :
      ShortComplex.mk
          (sequentialTelescopeMap (Functor.ofSequence (fun n ↦ H.map (f n))))
          (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)))
          (sequentialTelescopeMap_comp_sigmaDesc
            (Functor.ofSequence (fun n ↦ H.map (f n)))
            (fun n ↦ H.map (Sigma.ι K n ≫ g))
            (fun n ↦ by
              simpa [Functor.ofSequence_map_homOfLE_succ] using
                homologicalFunctor_hocolim_cocone_naturality H f g h hKhocolim n)) ≅
        ((shortComplexOfDistTriangle
          (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h) hKhocolim).map H) := by
    refine ShortComplex.isoMk
      (PreservesCoproduct.iso H K).symm
      (PreservesCoproduct.iso H K).symm
      (Iso.refl _) ?_ ?_
    · -- The first square is exactly the inverse-oriented telescope comparison.
      simpa [Category.assoc] using
        (homologicalFunctor_ofSequence_telescope_map_compat_inv (H := H) (K := K) (f := f)).symm
    · -- The second square rewrites `H.map g` to the source-facing coproduct desc.
      simpa [Category.assoc] using
        (homologicalFunctor_sigma_desc_eq (H := H) (K := K) g).symm
  exact (ShortComplex.exact_iff_of_iso e).2 hExact

/-- Helper for Lemma 13.33.8: rotating the distinguished telescope triangle gives exactness of
the image map `∐ H(Kₙ) ⟶ H(K)` followed by `H.map h`. -/
private theorem homologicalFunctor_hocolim_sigma_desc_map_h_zero
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) ≫ H.map h = 0 := by
  -- Proof comment: rewrite the presentation map as the transported `H.map g`, then use the
  -- vanishing of the second and third maps in a distinguished triangle.
  rw [homologicalFunctor_sigma_desc_eq (H := H) g, Category.assoc, ← Functor.map_comp]
  rw [show g ≫ h = 0 by simpa using comp_distTriang_mor_zero₂₃ _ hKhocolim]
  simp

/-- Helper for Lemma 13.33.8: identity maps commute trivially with `H.map h`. -/
private theorem homologicalFunctor_map_h_identity
    {Khocolim : D} (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧) :
    𝟙 (H.obj Khocolim) ≫ H.map h = H.map h ≫ 𝟙 (H.obj ((∐ K)⟦(1 : ℤ)⟧)) := by
  -- Proof comment: the second transport square in the rotated short-complex comparison is the
  -- identity square on `H.map h`.
  simp

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
  -- Proof comment: rotate the distinguished triangle so that `g` and `h` become the first two
  -- maps, then transport only the source coproduct through the inverse comparison isomorphism.
  have hExact :
      ((shortComplexOfDistTriangle
        (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h).rotate
        (rot_of_distTriang _ hKhocolim)).map H).Exact := by
    simpa using H.map_distinguished_exact
      (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h).rotate
      (rot_of_distTriang _ hKhocolim)
  have e :
      ShortComplex.mk
          (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)))
          (H.map h)
          (homologicalFunctor_hocolim_sigma_desc_map_h_zero (H := H) (f := f) g h hKhocolim) ≅
        ((shortComplexOfDistTriangle
          (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h).rotate
          (rot_of_distTriang _ hKhocolim)).map H) := by
    refine ShortComplex.isoMk
      (PreservesCoproduct.iso H K).symm
      (Iso.refl _)
      (Iso.refl _)
      ?_
      ?_
    · -- The first square is the same coproduct comparison as for the unrotated triangle.
      simpa [Category.assoc] using
        (homologicalFunctor_sigma_desc_eq (H := H) (K := K) g).symm
    · -- The second square is unchanged after the rotation.
      change 𝟙 (H.obj Khocolim) ≫ H.map h = H.map h ≫ 𝟙 (H.obj ((∐ K)⟦(1 : ℤ)⟧))
      exact homologicalFunctor_map_h_identity (H := H) (K := K) h
  exact (ShortComplex.exact_iff_of_iso e).2 hExact

/-- Helper for Lemma 13.33.8: the connecting morphism in the mapped telescope triangle
vanishes because the shifted telescope map is mono. -/
private theorem shiftedFamily_coproduct_comparison_ι
    (n : ℕ) :
    Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) n ≫
        sigmaComparison (shiftFunctor D (1 : ℤ)) K =
      (Sigma.ι K n)⟦(1 : ℤ)⟧' := by
  -- Proof comment: the shift functor preserves countable coproducts, so the inverse comparison
  -- carries the shifted coproduct summand back to the shifted original summand inclusion.
  apply (cancel_mono (inv (sigmaComparison (shiftFunctor D (1 : ℤ)) K))).1
  simpa [Category.assoc] using
    (Limits.map_ι_comp_inv_sigmaComparison (shiftFunctor D (1 : ℤ)) K n).symm

/-- Helper for Lemma 13.33.8: after transporting the shifted coproduct back along the canonical
shift/coproduct comparison, the shifted telescope map becomes the shift of the original telescope
map. -/
private theorem shiftedTelescopeMap_compat_inv :
    sequentialTelescopeMap (Functor.ofSequence (fun n ↦ (f n)⟦(1 : ℤ)⟧')) ≫
        sigmaComparison (shiftFunctor D (1 : ℤ)) K =
      sigmaComparison (shiftFunctor D (1 : ℤ)) K ≫
        ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
  -- Route correction: use the sibling proof's association-stable summandwise normal form, so the
  -- shift/coproduct comparison is consumed only after the explicit telescope summand formula.
  apply Limits.Sigma.hom_ext
  intro n
  have hSigmaShift :
      Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) n ≫
          sequentialTelescopeMap (Functor.ofSequence (fun m ↦ (f m)⟦(1 : ℤ)⟧')) =
        Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) n -
          (f n)⟦(1 : ℤ)⟧' ≫ Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) (n + 1) := by
    simpa [Functor.ofSequence_map_homOfLE_succ] using
      (Sigma.ι_comp_sequentialTelescopeMap
        (K := Functor.ofSequence (fun m ↦ (f m)⟦(1 : ℤ)⟧')) n)
  have hSigma :
      Sigma.ι K n - f n ≫ Sigma.ι K (n + 1) =
        Sigma.ι K n ≫ sequentialTelescopeMap (Functor.ofSequence f) := by
    simpa [Functor.ofSequence_map_homOfLE_succ] using
      (Sigma.ι_comp_sequentialTelescopeMap (K := Functor.ofSequence f) n).symm
  calc
    Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) n ≫
        sequentialTelescopeMap (Functor.ofSequence (fun m ↦ (f m)⟦(1 : ℤ)⟧')) ≫
          sigmaComparison (shiftFunctor D (1 : ℤ)) K =
      (Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) n ≫
          sequentialTelescopeMap (Functor.ofSequence (fun m ↦ (f m)⟦(1 : ℤ)⟧'))) ≫
            sigmaComparison (shiftFunctor D (1 : ℤ)) K := by
          rw [Category.assoc]
    _ =
      (Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) n -
          (f n)⟦(1 : ℤ)⟧' ≫ Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) (n + 1)) ≫
            sigmaComparison (shiftFunctor D (1 : ℤ)) K := by
          exact congrArg (fun t ↦ t ≫ sigmaComparison (shiftFunctor D (1 : ℤ)) K) hSigmaShift
    _ =
      (Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) n ≫ sigmaComparison (shiftFunctor D (1 : ℤ)) K) -
        ((f n)⟦(1 : ℤ)⟧' ≫ Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) (n + 1) ≫
          sigmaComparison (shiftFunctor D (1 : ℤ)) K) := by
            simp [Preadditive.sub_comp, Category.assoc]
    _ =
      (Sigma.ι K n)⟦(1 : ℤ)⟧' -
        ((f n)⟦(1 : ℤ)⟧' ≫ (Sigma.ι K (n + 1))⟦(1 : ℤ)⟧') := by
            rw [shiftedFamily_coproduct_comparison_ι (K := K) (n := n)]
            have hNext :
                (f n)⟦(1 : ℤ)⟧' ≫ Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) (n + 1) ≫
                    sigmaComparison (shiftFunctor D (1 : ℤ)) K =
                  (f n)⟦(1 : ℤ)⟧' ≫ (Sigma.ι K (n + 1))⟦(1 : ℤ)⟧' := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ (f n)⟦(1 : ℤ)⟧' ≫ t)
                  (shiftedFamily_coproduct_comparison_ι (K := K) (n := n + 1))
            rw [hNext]
    _ =
      ((Sigma.ι K n - f n ≫ Sigma.ι K (n + 1))⟦(1 : ℤ)⟧') := by
          rw [Functor.map_sub, Functor.map_comp]
    _ = (Sigma.ι K n ≫ sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧' := by
          rw [hSigma]
          rfl
    _ =
      Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) n ≫
        (sigmaComparison (shiftFunctor D (1 : ℤ)) K ≫
          ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧')) := by
          calc
            (Sigma.ι K n ≫ sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧' =
              (Sigma.ι K n)⟦(1 : ℤ)⟧' ≫
                ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
                  rw [Functor.map_comp]
            _ =
              (Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) n ≫
                  sigmaComparison (shiftFunctor D (1 : ℤ)) K) ≫
                ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
                    exact congrArg
                      (fun t ↦ t ≫ ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧'))
                      (shiftedFamily_coproduct_comparison_ι (K := K) (n := n)).symm
            _ =
              Sigma.ι (fun i ↦ K i⟦(1 : ℤ)⟧) n ≫
                (sigmaComparison (shiftFunctor D (1 : ℤ)) K ≫
                  ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧')) := by
                    rw [Category.assoc]

/-- Helper for Lemma 13.33.8: after applying `H`, the shifted telescope map on `(∐ K)⟦1⟧`
is mono. -/
private theorem homologicalFunctor_shifted_telescope_map_mono :
    Mono (H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧')) := by
  -- Proof comment: identify the shifted telescope map after applying `H` with the ordinary
  -- telescope map of the shifted image sequence in `A`, then transport monomorphy back across the
  -- coproduct/shift comparison isomorphism.
  let S : ℕ ⥤ D := Functor.ofSequence (fun n ↦ (f n)⟦(1 : ℤ)⟧')
  let e : ∐ (S ⋙ H).obj ≅ H.obj ((∐ K)⟦(1 : ℤ)⟧) :=
    (PreservesCoproduct.iso H S.obj).symm ≪≫
      H.mapIso (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) K).symm
  have hMonoSeq : Mono (sequentialTelescopeMap (S ⋙ H)) := by
    simpa using (sequentialTelescope_shortExact (𝒜 := A) (S ⋙ H)).mono_f
  let _ : Mono (sequentialTelescopeMap (S ⋙ H)) := hMonoSeq
  have hCoproduct :
      sequentialTelescopeMap (S ⋙ H) ≫ (PreservesCoproduct.iso H S.obj).inv =
        (PreservesCoproduct.iso H S.obj).inv ≫ H.map (sequentialTelescopeMap S) := by
    simpa using
      (homologicalFunctor_telescope_map_compat_inv (H := H) (S := S))
  have hShiftIsoInv :
      (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) K).inv =
        sigmaComparison (shiftFunctor D (1 : ℤ)) K := by
    simpa [PreservesCoproduct.inv_hom]
  have heHom :
      e.hom =
        (PreservesCoproduct.iso H S.obj).inv ≫
          H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) := by
    rw [show e.hom =
        (PreservesCoproduct.iso H S.obj).inv ≫
          H.map ((PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) K).inv) by
        rfl]
    rw [hShiftIsoInv]
  have hShiftMap :
      H.map (sequentialTelescopeMap S) ≫ H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) =
        H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) ≫
          H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
    have hRaw :
        sequentialTelescopeMap S ≫ sigmaComparison (shiftFunctor D (1 : ℤ)) K =
          sigmaComparison (shiftFunctor D (1 : ℤ)) K ≫
            ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
      simpa [S] using shiftedTelescopeMap_compat_inv (K := K) (f := f)
    calc
      H.map (sequentialTelescopeMap S) ≫ H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) =
          H.map
            (sequentialTelescopeMap S ≫ sigmaComparison (shiftFunctor D (1 : ℤ)) K) := by
            rw [← Functor.map_comp]
      _ =
          H.map
            (sigmaComparison (shiftFunctor D (1 : ℤ)) K ≫
              ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧')) := by
                exact congrArg H.map hRaw
      _ = H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) ≫
            H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
            rw [Functor.map_comp]
  have hTransport :
      sequentialTelescopeMap (S ⋙ H) ≫ e.hom =
        e.hom ≫ H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
    have hCoproductAssoc :
        (sequentialTelescopeMap (S ⋙ H) ≫ (PreservesCoproduct.iso H S.obj).inv) ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) =
          ((PreservesCoproduct.iso H S.obj).inv ≫ H.map (sequentialTelescopeMap S)) ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) := by
      exact
        congrArg (fun t ↦ t ≫ H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K)) hCoproduct
    have hCoproduct' :
        sequentialTelescopeMap (S ⋙ H) ≫ (PreservesCoproduct.iso H S.obj).inv ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) =
          (PreservesCoproduct.iso H S.obj).inv ≫ H.map (sequentialTelescopeMap S) ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) := by
      simpa [Category.assoc] using hCoproductAssoc
    have hTransport' :
        sequentialTelescopeMap (S ⋙ H) ≫ (PreservesCoproduct.iso H S.obj).inv ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) =
          (PreservesCoproduct.iso H S.obj).inv ≫ H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) ≫
            H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
      have hShiftMapAssoc :
          (PreservesCoproduct.iso H S.obj).inv ≫
              (H.map (sequentialTelescopeMap S) ≫
                H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K)) =
            (PreservesCoproduct.iso H S.obj).inv ≫
              (H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) ≫
                H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧')) := by
        exact congrArg (fun t ↦ (PreservesCoproduct.iso H S.obj).inv ≫ t) hShiftMap
      have hShiftMap' :
          (PreservesCoproduct.iso H S.obj).inv ≫ H.map (sequentialTelescopeMap S) ≫
              H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) =
            (PreservesCoproduct.iso H S.obj).inv ≫ H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K) ≫
              H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
        simpa [Category.assoc] using hShiftMapAssoc
      exact hCoproduct'.trans hShiftMap'
    have hTransportExpanded :
        sequentialTelescopeMap (S ⋙ H) ≫
            ((PreservesCoproduct.iso H S.obj).inv ≫
              H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K)) =
          ((PreservesCoproduct.iso H S.obj).inv ≫
              H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K)) ≫
            H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
      simpa [Category.assoc] using hTransport'
    have hLeft :
        sequentialTelescopeMap (S ⋙ H) ≫ e.hom =
          sequentialTelescopeMap (S ⋙ H) ≫
            ((PreservesCoproduct.iso H S.obj).inv ≫
              H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K)) := by
      exact congrArg (fun t ↦ sequentialTelescopeMap (S ⋙ H) ≫ t) heHom
    have hRight :
        ((PreservesCoproduct.iso H S.obj).inv ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) K)) ≫
          H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') =
        e.hom ≫ H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
      exact congrArg
        (fun t ↦ t ≫ H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧'))
        heHom.symm
    exact hLeft.trans (hTransportExpanded.trans hRight)
  have hConj' :
      e.inv ≫ sequentialTelescopeMap (S ⋙ H) ≫ e.hom =
        H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ e.inv ≫ t) hTransport
  have hConj :
      H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') =
        e.inv ≫ sequentialTelescopeMap (S ⋙ H) ≫ e.hom := by
    simpa using hConj'.symm
  let _ : Mono e.inv := by
    infer_instance
  let _ : Mono e.hom := by
    infer_instance
  have hCompMonoLeft : Mono (e.inv ≫ sequentialTelescopeMap (S ⋙ H)) := by
    exact mono_comp e.inv (sequentialTelescopeMap (S ⋙ H))
  have hCompMono : Mono (e.inv ≫ sequentialTelescopeMap (S ⋙ H) ≫ e.hom) := by
    let _ : Mono (e.inv ≫ sequentialTelescopeMap (S ⋙ H)) := hCompMonoLeft
    simpa [Category.assoc] using
      (show Mono ((e.inv ≫ sequentialTelescopeMap (S ⋙ H)) ≫ e.hom) from
        mono_comp (e.inv ≫ sequentialTelescopeMap (S ⋙ H)) e.hom)
  simpa only [hConj] using hCompMono

/-- Helper for Lemma 13.33.8: applying `H` to the negative shifted telescope map simply negates
the mapped shifted telescope map. -/
private theorem homologicalFunctor_shifted_telescope_map_neg :
    H.map (-((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧')) =
      -H.map ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧') := by
  -- Proof comment: `H` is additive, so it sends the unique minus sign in the twice-rotated
  -- telescope map to the corresponding minus sign in `A`.
  rw [Functor.map_neg]

/-- Helper for Lemma 13.33.8: the connecting morphism in the mapped telescope triangle
vanishes because the shifted telescope map is mono. -/
private theorem homologicalFunctor_hocolim_map_h_zero
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    H.map h = 0 := by
  -- Proof comment: on the twice-rotated telescope triangle the second morphism is the negative
  -- shifted telescope map, so exactness of the mapped twice-rotated triangle forces `H.map h`
  -- itself to vanish.
  let T : Triangle D := Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h
  have hTrotrot : T.rotate.rotate ∈ distTriang D := by
    exact rot_of_distTriang _ (rot_of_distTriang _ hKhocolim)
  let shiftedMap := ((sequentialTelescopeMap (Functor.ofSequence f))⟦(1 : ℤ)⟧')
  let _ : Mono (H.map shiftedMap) := by
    simpa [shiftedMap] using
      (homologicalFunctor_shifted_telescope_map_mono (H := H) (K := K) (f := f))
  have hMonoNeg :
      Mono (H.map (-shiftedMap)) := by
    rw [show H.map (-shiftedMap) = -H.map shiftedMap by
      simpa [shiftedMap] using
        (homologicalFunctor_shifted_telescope_map_neg (H := H) (K := K) (f := f))]
    infer_instance
  have hExact :
      ((shortComplexOfDistTriangle T.rotate.rotate hTrotrot).map H).Exact := by
    simpa using H.map_distinguished_exact T.rotate.rotate hTrotrot
  have hMonoG : Mono (((shortComplexOfDistTriangle T.rotate.rotate hTrotrot).map H).g) := by
    change Mono (H.map (-shiftedMap))
    exact hMonoNeg
  exact hExact.mono_g_iff.1 hMonoG

/-- Helper for Lemma 13.33.8: the map from `∐ H(Kₙ)` to `H(K)` induced by the telescope
presentation is epimorphic. -/
private theorem homologicalFunctor_hocolim_sigma_desc_epi
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    Epi (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g))) := by
  -- Proof comment: exactness of the rotated triangle identifies epicity of the `Sigma.desc` map
  -- with vanishing of the following morphism, which is exactly `H.map h`.
  exact
    (homologicalFunctor_hocolim_sigma_desc_map_h_exact
      (H := H) (K := K) (f := f) g h hKhocolim).epi_f_iff.2
      (homologicalFunctor_hocolim_map_h_zero
        (H := H) (K := K) (f := f) g h hKhocolim)

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
  -- Proof comment: once the source-facing `Sigma.desc` is epi, the exact image short complex
  -- packages directly into the required cokernel cofork.
  let S : ShortComplex A :=
    ShortComplex.mk
      (sequentialTelescopeMap (Functor.ofSequence (fun n ↦ H.map (f n))))
      (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)))
      (sequentialTelescopeMap_comp_sigmaDesc
        (Functor.ofSequence (fun n ↦ H.map (f n)))
        (fun n ↦ H.map (Sigma.ι K n ≫ g))
        (fun n ↦ by
          simpa [Functor.ofSequence_map_homOfLE_succ] using
            homologicalFunctor_hocolim_cocone_naturality H f g h hKhocolim n))
  have hExact : S.Exact := by
    simpa [S] using
      homologicalFunctor_hocolim_sigma_desc_exact (H := H) (K := K) (f := f) g h hKhocolim
  letI : Epi S.g :=
    homologicalFunctor_hocolim_sigma_desc_epi (H := H) (K := K) (f := f) g h hKhocolim
  simpa [S] using (show Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero)) from ⟨hExact.gIsCokernel⟩)

/-- Helper for Lemma 13.33.8: the explicit cocone on `H.obj Khocolim` is a colimit cocone for
the image sequence. -/
private theorem homologicalFunctor_targetCocone_sigma_desc_zero
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (_hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D)
    (s : Cocone (Functor.ofSequence (fun n ↦ H.map (f n)))) :
    sequentialTelescopeMap (Functor.ofSequence (fun n ↦ H.map (f n))) ≫
        Limits.Sigma.desc (fun n ↦ s.ι.app n) = 0 := by
  -- Proof comment: every cocone on the sequential image diagram kills the telescope map by the
  -- defining cocone relation on successive stages.
  simpa [Functor.ofSequence_map_homOfLE_succ] using
    sequentialTelescopeMap_comp_sigmaDesc
      (Functor.ofSequence (fun n ↦ H.map (f n)))
      (fun n ↦ s.ι.app n)
      (fun n ↦ s.w (homOfLE (Nat.le_succ n)))

/-- Helper for Lemma 13.33.8: the cokernel witness on the source-facing `Sigma.desc` map gives
the universal morphism from `H.obj Khocolim` to any cocone point on the image sequence. -/
private noncomputable def homologicalFunctor_hocolim_coconeDesc
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D)
    (s : Cocone (Functor.ofSequence (fun n ↦ H.map (f n)))) :
    H.obj Khocolim ⟶ s.pt :=
  let hCok := Classical.choice
    (homologicalFunctor_hocolim_sigma_desc_cokernel (H := H) (K := K) (f := f) g h hKhocolim)
  hCok.desc
    (CokernelCofork.ofπ
      (Limits.Sigma.desc (fun n ↦ s.ι.app n))
      (homologicalFunctor_targetCocone_sigma_desc_zero
        (H := H) (K := K) (f := f) g h hKhocolim s))

/-- Helper for Lemma 13.33.8: the morphism obtained from the cokernel witness satisfies the cocone
leg equations. -/
private theorem homologicalFunctor_hocolim_coconeDesc_fac
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D)
    (s : Cocone (Functor.ofSequence (fun n ↦ H.map (f n)))) (n : ℕ) :
    (homologicalFunctor_hocolim_cocone H f g h hKhocolim).ι.app n ≫
        homologicalFunctor_hocolim_coconeDesc (H := H) (K := K) (f := f) g h hKhocolim s =
      s.ι.app n := by
  -- Proof comment: the chosen cokernel witness identifies the source-facing `Sigma.desc` map with
  -- the universal cocone factorization; precomposing that equality with the `n`th summand yields
  -- the desired cocone-leg formula.
  let hCok := Classical.choice
    (homologicalFunctor_hocolim_sigma_desc_cokernel (H := H) (K := K) (f := f) g h hKhocolim)
  have hfac :
      Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) ≫
          homologicalFunctor_hocolim_coconeDesc (H := H) (K := K) (f := f) g h hKhocolim s =
        Limits.Sigma.desc (fun n ↦ s.ι.app n) := by
    simpa [homologicalFunctor_hocolim_coconeDesc, hCok] using
      hCok.fac
        (CokernelCofork.ofπ
          (Limits.Sigma.desc (fun n ↦ s.ι.app n))
          (homologicalFunctor_targetCocone_sigma_desc_zero
            (H := H) (K := K) (f := f) g h hKhocolim s))
        WalkingParallelPair.one
  have hpre :
      Sigma.ι (fun i ↦ H.obj (K i)) n ≫
          (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) ≫
            homologicalFunctor_hocolim_coconeDesc
              (H := H) (K := K) (f := f) g h hKhocolim s) =
        Sigma.ι (fun i ↦ H.obj (K i)) n ≫ Limits.Sigma.desc (fun n ↦ s.ι.app n) := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ Sigma.ι (fun i ↦ H.obj (K i)) n ≫ t) hfac
  have hιg :
      Sigma.ι (fun i ↦ H.obj (K i)) n ≫
          Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) =
        H.map (Sigma.ι K n) ≫ H.map g := by
    rw [Limits.Sigma.ι_desc, Functor.map_comp]
  have hleft :
      (homologicalFunctor_hocolim_cocone H f g h hKhocolim).ι.app n ≫
          homologicalFunctor_hocolim_coconeDesc (H := H) (K := K) (f := f) g h hKhocolim s =
        H.map (Sigma.ι K n) ≫ H.map g ≫
          homologicalFunctor_hocolim_coconeDesc (H := H) (K := K) (f := f) g h hKhocolim s := by
    simpa [homologicalFunctor_hocolim_cocone, Functor.map_comp, Category.assoc]
  have hright :
      H.map (Sigma.ι K n) ≫ H.map g ≫
          homologicalFunctor_hocolim_coconeDesc (H := H) (K := K) (f := f) g h hKhocolim s =
        Sigma.ι (fun i ↦ H.obj (K i)) n ≫
          Limits.Sigma.desc (fun n ↦ s.ι.app n) := by
    calc
      H.map (Sigma.ι K n) ≫ H.map g ≫
          homologicalFunctor_hocolim_coconeDesc (H := H) (K := K) (f := f) g h hKhocolim s =
        Sigma.ι (fun i ↦ H.obj (K i)) n ≫
          (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) ≫
            homologicalFunctor_hocolim_coconeDesc
              (H := H) (K := K) (f := f) g h hKhocolim s) := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ t ≫ homologicalFunctor_hocolim_coconeDesc
                    (H := H) (K := K) (f := f) g h hKhocolim s)
                  hιg.symm
      _ = Sigma.ι (fun i ↦ H.obj (K i)) n ≫ Limits.Sigma.desc (fun n ↦ s.ι.app n) := hpre
  exact hleft.trans (hright.trans (by rw [Limits.Sigma.ι_desc]))

/-- Helper for Lemma 13.33.8: the cokernel-descended morphism to a target cocone point is unique. -/
private theorem homologicalFunctor_hocolim_coconeDesc_uniq
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D)
    (s : Cocone (Functor.ofSequence (fun n ↦ H.map (f n))))
    (m : H.obj Khocolim ⟶ s.pt)
    (hm :
      ∀ n : ℕ,
        (homologicalFunctor_hocolim_cocone H f g h hKhocolim).ι.app n ≫ m = s.ι.app n) :
    m = homologicalFunctor_hocolim_coconeDesc (H := H) (K := K) (f := f) g h hKhocolim s := by
  -- Proof comment: cokernel-descended maps are unique once they agree after precomposition with
  -- the source-facing cokernel map, and that agreement is checked summandwise on `∐ H(Kₙ)`.
  let hCok := Classical.choice
    (homologicalFunctor_hocolim_sigma_desc_cokernel (H := H) (K := K) (f := f) g h hKhocolim)
  apply Cofork.IsColimit.hom_ext hCok
  apply Limits.Sigma.hom_ext
  intro n
  have hm' :
      Sigma.ι (fun i ↦ H.obj (K i)) n ≫
          (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) ≫ m) =
        s.ι.app n := by
    have hιg :
        Sigma.ι (fun i ↦ H.obj (K i)) n ≫
            Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) =
          H.map (Sigma.ι K n) ≫ H.map g := by
      rw [Limits.Sigma.ι_desc, Functor.map_comp]
    calc
      Sigma.ι (fun i ↦ H.obj (K i)) n ≫
          (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) ≫ m) =
        H.map (Sigma.ι K n) ≫ H.map g ≫ m := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ m) hιg
      _ = s.ι.app n := by
            simpa [homologicalFunctor_hocolim_cocone, Functor.map_comp, Category.assoc] using hm n
  have hdesc' :
      Sigma.ι (fun i ↦ H.obj (K i)) n ≫
          (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) ≫
            homologicalFunctor_hocolim_coconeDesc
              (H := H) (K := K) (f := f) g h hKhocolim s) =
        s.ι.app n := by
    have hιg :
        Sigma.ι (fun i ↦ H.obj (K i)) n ≫
            Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) =
          H.map (Sigma.ι K n) ≫ H.map g := by
      rw [Limits.Sigma.ι_desc, Functor.map_comp]
    calc
      Sigma.ι (fun i ↦ H.obj (K i)) n ≫
          (Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι K n ≫ g)) ≫
            homologicalFunctor_hocolim_coconeDesc
              (H := H) (K := K) (f := f) g h hKhocolim s) =
        H.map (Sigma.ι K n) ≫ H.map g ≫
          homologicalFunctor_hocolim_coconeDesc
            (H := H) (K := K) (f := f) g h hKhocolim s := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ t ≫ homologicalFunctor_hocolim_coconeDesc
                    (H := H) (K := K) (f := f) g h hKhocolim s)
                  hιg
      _ = s.ι.app n := by
            simpa [homologicalFunctor_hocolim_cocone, Functor.map_comp, Category.assoc] using
              homologicalFunctor_hocolim_coconeDesc_fac
              (H := H) (K := K) (f := f) g h hKhocolim s n
  exact hm'.trans hdesc'.symm

/-- Helper for Lemma 13.33.8: the explicit cocone on `H.obj Khocolim` is a colimit cocone for
the image sequence. -/
private noncomputable def homologicalFunctor_hocolim_cocone_isColimit
    {Khocolim : D} (g : ∐ K ⟶ Khocolim) (h : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g h ∈ distTriang D) :
    IsColimit (homologicalFunctor_hocolim_cocone H f g h hKhocolim) :=
  IsColimit.mk
    (homologicalFunctor_hocolim_coconeDesc (H := H) (K := K) (f := f) g h hKhocolim)
    (homologicalFunctor_hocolim_coconeDesc_fac (H := H) (K := K) (f := f) g h hKhocolim)
    (homologicalFunctor_hocolim_coconeDesc_uniq (H := H) (K := K) (f := f) g h hKhocolim)

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
  -- Proof comment: both the standard colimit cocone and the explicit cocone on `H.obj Khocolim`
  -- are colimiting, so the comparison map is the unique cocone-point isomorphism between them.
  let hColim :=
    homologicalFunctor_hocolim_cocone_isColimit (H := H) (K := K) (f := f) g h hKhocolim
  let e :
      colimit (Functor.ofSequence (fun n ↦ H.map (f n))) ≅ H.obj Khocolim :=
    (colimit.isColimit (Functor.ofSequence (fun n ↦ H.map (f n)))).coconePointUniqueUpToIso hColim
  have hcomparison :
      homologicalFunctor_hocolim_comparison H f g h hKhocolim = e.hom := by
    apply colimit.hom_ext
    intro n
    have hleft :
        colimit.ι (Functor.ofSequence (fun n ↦ H.map (f n))) n ≫
            homologicalFunctor_hocolim_comparison H f g h hKhocolim =
          (homologicalFunctor_hocolim_cocone H f g h hKhocolim).ι.app n := by
      simpa [homologicalFunctor_hocolim_comparison] using
        colimit.ι_desc (homologicalFunctor_hocolim_cocone H f g h hKhocolim) (j := n)
    have hright :
        colimit.ι (Functor.ofSequence (fun n ↦ H.map (f n))) n ≫ e.hom =
          (homologicalFunctor_hocolim_cocone H f g h hKhocolim).ι.app n := by
      simpa [e] using
        IsColimit.comp_coconePointUniqueUpToIso_hom
          (colimit.isColimit (Functor.ofSequence (fun n ↦ H.map (f n)))) hColim n
    exact hleft.trans hright.symm
  rw [hcomparison]
  infer_instance

/-- Lemma 13.33.8: if `Khocolim` is a homotopy colimit of a sequential system
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`, then after applying a homological functor `H` that commutes with countable
direct sums, the resulting cocone on `H.obj (K n)` with point `H.obj Khocolim` is a colimit
cocone. This is the owner-level `IsHomotopyColimitOf` formulation of the lemma. -/
@[stacks 0CRK]
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
