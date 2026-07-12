import Mathlib
import StacksProject_2024.Chap29.Definition_29_21_1
import StacksProject_2024.Chap29.Lemma_29_14_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}}

namespace Scheme.Hom

/- Semantic recall / source-core-bridge check:
- mathlib's canonical owner is `AlgebraicGeometry.LocallyOfFinitePresentation`, with direct recall
  theorem `AlgebraicGeometry.locallyOfFinitePresentation_iff` and the restriction instance
  `AlgebraicGeometry.instLocallyOfFinitePresentationMorphismRestrict`;
- `Chap29/Definition_29_21_1.lean` already identifies this owner with the chapter-local
  affine-neighborhood owner `LocallyOfType RingHom.FinitePresentation`;
- `Chap29/Lemma_29_14_4.lean` already provides the reusable open-cover and affine-open-cover
  criteria for `LocallyOfType`, so this file should specialize that canonical cover API rather
  than introduce new wrapper structures.
-/

/-- Lemma 29.21.2 (1): a morphism of schemes is locally of finite presentation if and only if for
every affine opens `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`, the induced ring map on sections is of
finite presentation. -/
@[stacks 01TQ]
theorem locallyOfFinitePresentation_iff_forall_affineOpen_appLE
    (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      ∀ ⦃V : S.Opens⦄, IsAffineOpen V →
        ∀ ⦃U : X.Opens⦄, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          RingHom.FinitePresentation ((f.appLE V U e).hom) := by
  have h :
      LocallyOfType RingHom.FinitePresentation f ↔
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V →
          ∀ ⦃U : X.Opens⦄, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.FinitePresentation ((f.appLE V U e).hom) :=
    locallyOfType_iff_forall_affineOpen_appLE
      RingHom.FinitePresentation RingHom.finitePresentation_isLocal
  simpa [Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType f] using
    h

/-- Lemma 29.21.2 (2): a morphism of schemes is locally of finite presentation if and only if
there is an open cover of the base and open covers of the corresponding preimages such that each
restricted morphism is locally of finite presentation. -/
@[stacks 01TQ]
theorem locallyOfFinitePresentation_iff_exists_openCover
    (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, LocallyOfFinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j) := by
  constructor
  · intro hf
    have hf' : LocallyOfType RingHom.FinitePresentation f :=
      (Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType f).1 hf
    rcases (locallyOfType_iff_exists_openCover
      RingHom.FinitePresentation RingHom.finitePresentation_isLocal).1 hf' with
      ⟨𝒱, h𝒱⟩
    refine ⟨𝒱, ?_⟩
    intro j
    rcases h𝒱 j with ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, ?_⟩
    intro i
    have h :
        LocallyOfFinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j) ↔
          LocallyOfType RingHom.FinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j) :=
      Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType
        (𝒰.f i ≫ 𝒱.pullbackHom f j)
    exact
      h.2 (h𝒰 i)
  · rintro ⟨𝒱, h𝒱⟩
    have h𝒱' :
        ∃ 𝒰 : S.OpenCover, ∀ j : 𝒰.I₀,
          ∃ 𝒲 : ((𝒰.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒲.I₀,
              LocallyOfType RingHom.FinitePresentation (𝒲.f i ≫ 𝒰.pullbackHom f j) := by
      refine ⟨𝒱, ?_⟩
      intro j
      rcases h𝒱 j with ⟨𝒰, h𝒰⟩
      refine ⟨𝒰, ?_⟩
      intro i
      have h :
          LocallyOfFinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j) ↔
            LocallyOfType RingHom.FinitePresentation (𝒰.f i ≫ 𝒱.pullbackHom f j) :=
        Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType
          (𝒰.f i ≫ 𝒱.pullbackHom f j)
      exact
        h.1 (h𝒰 i)
    exact
      (Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType f).2 <|
        (locallyOfType_iff_exists_openCover
          RingHom.FinitePresentation RingHom.finitePresentation_isLocal).2 h𝒱'

/-- Lemma 29.21.2 (3): a morphism of schemes is locally of finite presentation if and only if
there are affine open covers `V_j` of `S` and `U_i` of each `f^{-1}(V_j)` such that the induced
ring maps on sections are of finite presentation. -/
@[stacks 01TQ]
theorem locallyOfFinitePresentation_iff_exists_affineOpenCover
    (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            RingHom.FinitePresentation (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) := by
  have h :
      LocallyOfType RingHom.FinitePresentation f ↔
        ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.FinitePresentation (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) :=
    locallyOfType_iff_exists_affineOpenCover
      RingHom.FinitePresentation RingHom.finitePresentation_isLocal
  simpa [Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType f] using
    h

/-- Lemma 29.21.2 (4): if `f : X ⟶ S` is locally of finite presentation, then for any open
subschemes `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`, the restricted morphism `U ⟶ V` is still
locally of finite presentation. -/
@[stacks 01TQ]
theorem locallyOfFinitePresentation_resLE
    {f : X ⟶ S} (hf : LocallyOfFinitePresentation f)
    {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    LocallyOfFinitePresentation (f.resLE V U e) := by
  have hf' : LocallyOfType RingHom.FinitePresentation f :=
    (Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType f).1 hf
  have hres : LocallyOfType RingHom.FinitePresentation (f.resLE V U e) :=
    locallyOfType_resLE RingHom.FinitePresentation RingHom.finitePresentation_isLocal hf' e
  have hiff :
      LocallyOfFinitePresentation (f.resLE V U e) ↔
        LocallyOfType RingHom.FinitePresentation (f.resLE V U e) :=
    Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType (f.resLE V U e)
  exact
    hiff.2 hres

end Scheme.Hom

end

end AlgebraicGeometry
