import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open Algebra.TensorProduct
open scoped TensorProduct

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- Lemma 10.127.7 (1): if `B` is of finite type over `A` and two `A`-algebra maps
`u, u' : B → C` induce the same map from `B` into the colimit base change `C ⊗[A] colimit F`,
then they already induce the same map into `C ⊗[A] F.obj j` for some stage `j`. -/
-- Proof sketch: this is the injectivity half of the canonical filtered-colimit Hom comparison for
-- finite-type `A`-algebras, applied to the filtered diagram `j ↦ C ⊗[A] F.obj j` in `Under A`.
theorem finite_type_map_equality_descends
    [Algebra.FiniteType A B]
    (u u' : B →ₐ[A] C)
    (h :
      (includeLeft : C →ₐ[A] C ⊗[A] ↑(colimit F)).comp u =
        (includeLeft : C →ₐ[A] C ⊗[A] ↑(colimit F)).comp u') :
    ∃ j : J,
      (includeLeft : C →ₐ[A] C ⊗[A] ↑(F.obj j)).comp u =
        (includeLeft : C →ₐ[A] C ⊗[A] ↑(F.obj j)).comp u' := sorry

/-- Lemma 10.127.7 (2): if `C` is of finite type over `A` and the base change of
`u : B → C` to the filtered colimit algebra `colimit F` is surjective, then the base change of
`u` to some stage `F.obj j` is already surjective. -/
-- Proof sketch: choose finitely many algebra generators of `C`; surjectivity after tensoring to
-- the colimit gives preimages for those generators in the colimit tensor product, and filtered
-- finiteness allows those preimages to be realized simultaneously at one stage, yielding
-- surjectivity there.
theorem finite_type_surjectivity_descends
    [Algebra.FiniteType A C]
    (u : B →ₐ[A] C)
    (h : Function.Surjective (Algebra.TensorProduct.map u (AlgHom.id A ↑(colimit F)))) :
    ∃ j : J, Function.Surjective (Algebra.TensorProduct.map u (AlgHom.id A ↑(F.obj j))) := sorry

/-- Lemma 10.127.7 (3): if `C` is finitely presented over `A`, then every `A`-algebra map
`v : C → B ⊗[A] colimit F` descends to some stage `F.obj j`. -/
-- Proof sketch: this is the surjectivity half of the canonical filtered-colimit Hom comparison for
-- the finitely presented `A`-algebra `C`, specialized to the filtered diagram
-- `j ↦ B ⊗[A] F.obj j` in `Under A`.
theorem finite_presentation_hom_descends
    [Algebra.FinitePresentation A C]
    (v : C →ₐ[A] B ⊗[A] ↑(colimit F)) :
    ∃ (j : J) (v_j : C →ₐ[A] B ⊗[A] ↑(F.obj j)),
      (Algebra.TensorProduct.map (AlgHom.id A B) (colimit.ι F j).hom).comp v_j = v := sorry

/-- Lemma 10.127.7 (4): if `B` is of finite type over `A`, `C` is finitely presented over `A`,
and the base change of `u : B → C` to the filtered colimit algebra `colimit F` is bijective, then
the base change of `u` to some stage `F.obj j` is already bijective. -/
-- Proof sketch: descend a colimit-stage inverse in the owner form `C → B ⊗[A] colimit F` by part
-- (3), then apply part (1) to the two resulting composite maps to enlarge to a stage where both
-- inverse identities already hold, forcing bijectivity there.
theorem finite_type_finite_presentation_bijective_descends
    [Algebra.FiniteType A B] [Algebra.FinitePresentation A C]
    (u : B →ₐ[A] C)
    (h : Function.Bijective (Algebra.TensorProduct.map u (AlgHom.id A ↑(colimit F)))) :
    ∃ j : J, Function.Bijective (Algebra.TensorProduct.map u (AlgHom.id A ↑(F.obj j))) := sorry

end
