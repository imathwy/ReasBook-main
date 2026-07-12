import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w t s

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {U : C}
variable {I : Type t} {J : Type s}
variable (Ui : I → C) (π : ∀ i, Ui i ⟶ U)
variable (Vj : J → C) (ψ : ∀ j, Vj j ⟶ U)
variable (F : Cᵒᵖ ⥤ Type w)

namespace SemiRepresentableFamily
namespace Over

/- Domain-style sampling for Lemma 7.8.4:
- primary domain: fixed-target families of arrows, the canonical presieves/sieves they generate,
  and invariance of the sheaf condition under tautological equivalence;
- inspected declarations:
  `SemiRepresentableFamily.Over.toPresieve`,
  `SemiRepresentableFamily.Over.toSieve`,
  `SemiRepresentableFamily.Over.TautologicallyEquivalent`,
  `Presieve.isSheafFor_iff_generate`;
- best owner abstraction: `SemiRepresentableFamily.Over U`, with `toPresieve` and `toSieve` as the
  canonical bridge/view API to presieves and sieves;
- primitive data: a tautological equivalence between owner-level families;
- derived API here: invariance of the presieve sheaf condition, and the indexed-arrow corollary via
  `ofArrows`.

Source/core/bridge triage:
- `source-facing`: the indexed-family formulation of Lemma 7.8.4;
- `core/canonical`: `SemiRepresentableFamily.Over U`, `TautologicallyEquivalent`, and the canonical
  sieve equality `toSieve_eq_of_tautologicallyEquivalent`;
- `bridge/view`: `ofArrows`, turning indexed families into owner objects.
-/

/-- Tautologically equivalent fixed-target families impose equivalent sheaf conditions on any
presheaf. -/
theorem isSheafFor_iff_of_tautologicallyEquivalent
    {𝒰 𝒱 : Over U} (h : TautologicallyEquivalent 𝒰 𝒱) :
    𝒰.toPresieve.IsSheafFor F ↔ 𝒱.toPresieve.IsSheafFor F := by
  calc
    𝒰.toPresieve.IsSheafFor F ↔ (𝒰.toSieve : Presieve U).IsSheafFor F := by
      simpa [toSieve] using Presieve.isSheafFor_iff_generate 𝒰.toPresieve
    _ ↔ (𝒱.toSieve : Presieve U).IsSheafFor F := by
      rw [toSieve_eq_of_tautologicallyEquivalent h]
    _ ↔ 𝒱.toPresieve.IsSheafFor F := by
      simpa [toSieve] using (Presieve.isSheafFor_iff_generate 𝒱.toPresieve).symm

end Over
end SemiRepresentableFamily

open SemiRepresentableFamily.Over

private theorem tautologicallyEquivalent_ofArrows_ulift
    (α : I → J) (β : J → I)
    (hα : ∀ i, Over.mk (π i) ≅ Over.mk (ψ (α i)))
    (hβ : ∀ j, Over.mk (ψ j) ≅ Over.mk (π (β j))) :
    TautologicallyEquivalent
      (ofArrows (fun i : ULift.{max t s} I ↦ Ui i.down) fun i ↦ π i.down)
      (ofArrows (fun j : ULift.{max t s} J ↦ Vj j.down) fun j ↦ ψ j.down) := by
  refine ⟨
    { f := fun i ↦ ⟨α i.down⟩
      φ := fun i ↦ (hα i.down).hom },
    { f := fun j ↦ ⟨β j.down⟩
      φ := fun j ↦ (hβ j.down).hom },
    ?_,
    ?_⟩
  · intro i
    infer_instance
  · intro j
    infer_instance

/-- Lemma 7.8.4: tautologically equivalent indexed families of morphisms with the same fixed
target impose equivalent sheaf conditions on any presheaf. -/
-- Proof sketch: package the two indexed arrow families as objects of `SemiRepresentableFamily.Over
-- U`, note that the supplied componentwise slice isomorphisms give a tautological equivalence, and
-- then invoke `SemiRepresentableFamily.Over.isSheafFor_iff_of_tautologicallyEquivalent`.
theorem isSheafFor_ofArrows_iff_of_tautological_equivalence
    (α : I → J) (β : J → I)
    (hα : ∀ i, Over.mk (π i) ≅ Over.mk (ψ (α i)))
    (hβ : ∀ j, Over.mk (ψ j) ≅ Over.mk (π (β j))) :
    (Presieve.ofArrows Ui π).IsSheafFor F ↔ (Presieve.ofArrows Vj ψ).IsSheafFor F := by
  have h𝒰 :
      (ofArrows (fun i : ULift.{max t s} I ↦ Ui i.down) fun i ↦ π i.down).toPresieve =
        Presieve.ofArrows Ui π := by
    simpa using toPresieve_ofArrows_ulift Ui π
  have h𝒱 :
      (ofArrows (fun j : ULift.{max t s} J ↦ Vj j.down) fun j ↦ ψ j.down).toPresieve =
        Presieve.ofArrows Vj ψ := by
    simpa using toPresieve_ofArrows_ulift Vj ψ
  simpa [h𝒰, h𝒱] using
    isSheafFor_iff_of_tautologicallyEquivalent F
      (tautologicallyEquivalent_ofArrows_ulift Ui π Vj ψ α β hα hβ)

end CategoryTheory
