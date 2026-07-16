import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part16.ReconstructionTransport

universe u v

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8 Part16: the local zero section on a chosen gerbe-cover arrow,
transported back from the slicewise additive lift to the reconstructed `Type` sheaf. -/
noncomputable def reconstructedLocalZeroSection
    (hGerbe : IsGerbe J 𝒮.p)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    {U : C} (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (absolute_glueing_reconstruction (J := J) F).1.obj (op I.Y) :=
  let xI := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I
  let eI := reconstructed_over_to_lifted_underlying_iso
    (𝒮 := 𝒮) (J := J) F lifted forgetIso xI
  eI.inv.app (op (Over.mk (𝟙 I.Y))) 0

/-- Helper for Lemma 8.11.8 Part16: the local sum of two global reconstructed sections on a
chosen gerbe-cover arrow, transported through the chosen slicewise additive lift. -/
noncomputable def reconstructedLocalAddSection
    (hGerbe : IsGerbe J 𝒮.p)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    {U : C} (a b : (absolute_glueing_reconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (absolute_glueing_reconstruction (J := J) F).1.obj (op I.Y) :=
  let xI := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I
  let eI := reconstructed_over_to_lifted_underlying_iso
    (𝒮 := 𝒮) (J := J) F lifted forgetIso xI
  eI.inv.app (op (Over.mk (𝟙 I.Y)))
    (eI.hom.app (op (Over.mk (𝟙 I.Y)))
        ((absolute_glueing_reconstruction (J := J) F).1.map I.f.op a) +
      eI.hom.app (op (Over.mk (𝟙 I.Y)))
        ((absolute_glueing_reconstruction (J := J) F).1.map I.f.op b))

/-- Helper for Lemma 8.11.8 Part16: the local inverse of a global reconstructed section on a
chosen gerbe-cover arrow, transported through the chosen slicewise additive lift. -/
noncomputable def reconstructedLocalNegSection
    (hGerbe : IsGerbe J 𝒮.p)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    {U : C} (a : (absolute_glueing_reconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (absolute_glueing_reconstruction (J := J) F).1.obj (op I.Y) :=
  let xI := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I
  let eI := reconstructed_over_to_lifted_underlying_iso
    (𝒮 := 𝒮) (J := J) F lifted forgetIso xI
  eI.inv.app (op (Over.mk (𝟙 I.Y)))
    (-eI.hom.app (op (Over.mk (𝟙 I.Y)))
      ((absolute_glueing_reconstruction (J := J) F).1.map I.f.op a))

end CategoryTheory
