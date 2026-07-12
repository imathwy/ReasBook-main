import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.LeftExact
import StacksProject_2024.Chap07.Definition_7_15_1_Topoi
import StacksProject_2024.Chap07.Lemma_7_17_6

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

namespace Sheaf

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}

/-- Helper for Lemma 7.41.1: the singleton coproduct desc map built from identity morphisms is an
isomorphism. -/
private theorem singleton_sigma_desc_identity_isIso
    {A : Sheaf J (Type w)} :
    IsIso (Limits.Sigma.desc (fun _ : PUnit ↦ 𝟙 A)) := by
  -- The singleton coproduct injection is a two-sided inverse to the desc of identities.
  refine ⟨⟨Limits.Sigma.ι (fun _ : PUnit ↦ A) PUnit.unit, ?_, ?_⟩⟩
  · -- Compare the two endomorphisms after precomposing with the unique coproduct injection.
    apply Limits.Sigma.hom_ext
    intro i
    cases i
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ t ≫ Limits.Sigma.ι (fun _ : PUnit ↦ A) PUnit.unit)
        (Limits.Sigma.ι_desc (fun _ : PUnit ↦ 𝟙 A) PUnit.unit)
  · -- The reverse composite is exactly the standard singleton `Sigma.ι_desc` identity.
    simpa using Limits.Sigma.ι_desc (fun _ : PUnit ↦ 𝟙 A) PUnit.unit

/-- Helper for Lemma 7.41.1: for a singleton source family, the associated sigma-desc map is
locally surjective exactly when the unique component map is locally surjective. -/
theorem isLocallySurjective_singleton_sigma_desc_iff
    {A Z : Sheaf J (Type w)} (φ : A ⟶ Z) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun _ : PUnit ↦ φ)) ↔
      Sheaf.IsLocallySurjective φ := by
  let e : (∐ fun _ : PUnit ↦ A) ⟶ A := Limits.Sigma.desc (fun _ : PUnit ↦ 𝟙 A)
  letI : IsIso e := singleton_sigma_desc_identity_isIso (J := J) (A := A)
  have hcomp : e ≫ φ = Limits.Sigma.desc (fun _ : PUnit ↦ φ) := by
    -- Compare the singleton coproduct map componentwise on the unique summand.
    apply Limits.Sigma.hom_ext
    intro i
    cases i
    calc
      Limits.Sigma.ι (fun _ : PUnit ↦ A) PUnit.unit ≫ e ≫ φ
          = (𝟙 A) ≫ φ := by
              simpa [e, Category.assoc] using
                congrArg (fun t ↦ t ≫ φ)
                  (Limits.Sigma.ι_desc (fun _ : PUnit ↦ 𝟙 A) PUnit.unit)
      _ = φ := by simp
      _ = Limits.Sigma.ι (fun _ : PUnit ↦ A) PUnit.unit ≫
            Limits.Sigma.desc (fun _ : PUnit ↦ φ) := by
              simpa [Category.assoc] using
                (Limits.Sigma.ι_desc (fun _ : PUnit ↦ φ) PUnit.unit).symm
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  have he :
      Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map e) := by
    infer_instance
  letI :
      Presheaf.IsLocallySurjective J ((sheafToPresheaf J (Type w)).map e) := he
  have hcomp_hom :
      ((sheafToPresheaf J (Type w)).map e) ≫
          ((sheafToPresheaf J (Type w)).map φ) =
        (sheafToPresheaf J (Type w)).map (Limits.Sigma.desc (fun _ : PUnit ↦ φ)) := by
    simpa using congrArg (fun t ↦ (sheafToPresheaf J (Type w)).map t) hcomp
  rw [← hcomp_hom]
  exact Presheaf.comp_isLocallySurjective_iff J
    ((sheafToPresheaf J (Type w)).map e)
    ((sheafToPresheaf J (Type w)).map φ)

end

end Sheaf

namespace MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : MorphismOfTopoiIn J K)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Surjections onto inverse images lift along a surjective cover in the target topos. -/
def surjectionLiftingAlongInverseImage : Prop :=
  ∀ {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)} (φ : ℱ ⟶ f⁻¹.obj 𝒢),
    Sheaf.IsLocallySurjective φ →
      ∃ (𝒢' : Sheaf J (Type w)) (π : 𝒢' ⟶ 𝒢),
        Sheaf.IsLocallySurjective π ∧
          ∃ ι : (f⁻¹).obj 𝒢' ⟶ ℱ,
            ι ≫ φ = (f⁻¹).map π

/-- Helper for Lemma 7.41.1: pullbacks of locally surjective morphisms of sheaves of sets are
again locally surjective. -/
theorem sheaf_pullback_snd_isLocallySurjective
    {A B Z : Sheaf J (Type w)} (φ : A ⟶ Z) (q : B ⟶ Z)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Sheaf.IsLocallySurjective (pullback.snd φ q) := by
  let Fsh := sheafToPresheaf J (Type w)
  -- Move to the underlying presheaf pullback, where the local preimage is explicit.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  letI : Presheaf.IsLocallySurjective J (Fsh.map φ) := by
    simpa [Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] using hφ
  have hpres_pullback :
      Presheaf.IsLocallySurjective J (pullback.snd (Fsh.map φ) (Fsh.map q)) := by
    refine ⟨?_⟩
    intro X b
    refine J.superset_covering ?_
      (Presheaf.imageSieve_mem J (Fsh.map φ) ((Fsh.map q).app (op X) b))
    intro Y g hg
    rcases hg with ⟨a, ha⟩
    have hqx :
        (Fsh.map φ).app (op Y) a =
          (Fsh.map q).app (op Y) ((Fsh.obj B).map g.op b) := by
      calc
        (Fsh.map φ).app (op Y) a = (Fsh.obj Z).map g.op ((Fsh.map q).app (op X) b) := ha
        _ = (Fsh.map q).app (op Y) ((Fsh.obj B).map g.op b) := by
          symm
          simpa using congrFun ((Fsh.map q).naturality g.op) b
    let t' :
        Types.PullbackObj ((Fsh.map φ).app (op Y)) ((Fsh.map q).app (op Y)) :=
      ⟨⟨a, (Fsh.obj B).map g.op b⟩, hqx⟩
    let t : (pullback (Fsh.map φ) (Fsh.map q)).obj (op Y) :=
      (Limits.pullbackObjIso (Fsh.map φ) (Fsh.map q) (op Y)).inv
        ((Types.pullbackIsoPullback _ _).inv t')
    refine ⟨t, ?_⟩
    -- The second projection of the pullback element is the chosen local section of `B`.
    dsimp [t]
    simpa [t'] using
      congrFun (Limits.pullbackObjIso_inv_comp_snd (Fsh.map φ) (Fsh.map q) (op Y))
        ((Types.pullbackIsoPullback ((Fsh.map φ).app (op Y)) ((Fsh.map q).app (op Y))).inv t')
  let sourceMap : Fsh.obj (pullback φ q) ⟶ pullback (Fsh.map φ) (Fsh.map q) :=
    Limits.pullbackComparison Fsh φ q
  letI : Presheaf.IsLocallySurjective J sourceMap := by
    infer_instance
  have hcomp :
      Presheaf.IsLocallySurjective J
        (sourceMap ≫ pullback.snd (Fsh.map φ) (Fsh.map q)) := by
    exact (Presheaf.comp_isLocallySurjective_iff
      J sourceMap (pullback.snd (Fsh.map φ) (Fsh.map q))).2 hpres_pullback
  have hfac :
      sourceMap ≫ pullback.snd (Fsh.map φ) (Fsh.map q) =
        Fsh.map (pullback.snd φ q) := by
    simpa [sourceMap] using Limits.pullbackComparison_comp_snd Fsh φ q
  exact hfac ▸ hcomp

end

end MorphismOfTopoiIn

end CategoryTheory
