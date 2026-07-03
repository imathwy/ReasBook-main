import Mathlib
import stacks_project.Chap12.Definition_12_18_3
import stacks_project.Chap12.Lemma_12_14_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomologicalComplex HomotopyCategory
open HomologicalComplex₂
open scoped HomologicalComplex₂

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Domain-style sampling for Remark 12.18.7:
- primary domain: total complexes of cohomological double complexes, homotopies, and degreewise
  split short complexes;
- relevant owner declarations inspected:
  `HomologicalComplex₂.total`,
  `HomologicalComplex₂.totalFunctor`,
  `cochainComplex_self_homotopy_equiv_hom_to_shift`,
  `ShortComplex.Splitting`,
  `ShortComplex.Splitting.map`,
  `CochainComplex.homOfDegreewiseSplit`;
- best owner abstraction: totalization is the functor `totalFunctor`, and the connecting morphism
  is the owner construction `CochainComplex.homOfDegreewiseSplit` on the mapped short complex;
  self-homotopies in the first direction are compared to maps into the shifted bicomplex by the
  owner equivalence `cochainComplex_self_homotopy_equiv_hom_to_shift`;
- primitive data: a short complex `S` of double complexes, a degreewise splitting family `σ`, and
  a homotopy between bicomplex morphisms;
- derived API: the induced homotopy and equality in the homotopy category, the degreewise
  splitting on the totalized short complex, and the comparison of connecting morphisms.

Source/core/bridge triage:
- `source-facing`: the first-direction totalization statements of Remark 12.18.7;
- `core/canonical`: `totalFunctor`, `ShortComplex.Splitting`, and
  `CochainComplex.homOfDegreewiseSplit`;
- `bridge/view`: the totalized splitting data and the equality in the homotopy category.

The short complex of total complexes is canonically the image of `S` under the owner totalization
functor `S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))`; this file should use that mapped owner
directly instead of introducing a parallel public alias.

The helper `ShortComplex.Splitting.map` was also checked, but it is not the right owner for the
totalized splitting here: the retraction and section on `Tot(S)` are assembled from the whole
degreewise family `σ`, rather than obtained by applying one additive functor to a single splitting.
-/

/- Companion recall: the shift compatibility from the first part of the remark is the canonical
isomorphism `K.totalShift₁Iso 1 : Tot((shiftFunctor₁ C 1).obj K) ≅ Tot(K)⟦1⟧`.
-/
#check HomologicalComplex₂.totalShift₁Iso

section FirstDirectionHomotopy

variable {A B : HomologicalComplex₂ C (up ℤ) (up ℤ)} [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]

/-- Remark 12.18.7: a homotopy between morphisms of cohomological double complexes induces a
canonical homotopy between the associated total-complex maps. -/
noncomputable def totalHomotopyOfHomotopy₁
    {f g : A ⟶ B} (h : Homotopy f g) :
    Homotopy (total.map f (up ℤ)) (total.map g (up ℤ)) where
  hom i j :=
    if hij : (up ℤ).Rel j i then
      A.totalDesc fun p q hpq ↦
        ((h.hom p (p - 1)).f q) ≫
          B.ιTotal (up ℤ) (p - 1) q j (by
            dsimp at hpq hij ⊢
            lia)
    else
      0
  zero i j hij := by
    dsimp
    split_ifs with hrel
    · exact (hij hrel).elim
    · rfl
  comm i := by
    sorry

/-- Remark 12.18.7: a homotopy between morphisms of cohomological double complexes induces a
homotopy between the associated total-complex maps. -/
theorem total_homotopic_of_homotopy₁
    {f g : A ⟶ B} (h : Homotopy f g) :
    homotopic C (up ℤ) (total.map f (up ℤ)) (total.map g (up ℤ)) :=
  ⟨totalHomotopyOfHomotopy₁ h⟩

/-- Remark 12.18.7: homotopic morphisms of cohomological double complexes induce the same
morphism between the associated total complexes in the homotopy category. -/
lemma total_map_eq_in_homotopyCategory_of_homotopy₁
    {f g : A ⟶ B} (h : Homotopy f g) :
    (HomotopyCategory.quotient C (up ℤ)).map (total.map f (up ℤ)) =
      (HomotopyCategory.quotient C (up ℤ)).map (total.map g (up ℤ)) := by
  exact HomotopyCategory.eq_of_homotopy _ _ (totalHomotopyOfHomotopy₁ h)

-- Proof sketch: both sides encode the same degree `-1` cochain on the total complexes. Expanding
-- `cochainComplex_self_homotopy_equiv_hom_to_shift` and `totalHomotopyOfHomotopy₁`, the component
-- on the summand indexed by `(p, q)` is `((h.hom p (p - 1)).f q)`, and the comparison with the
-- shifted total complex is the canonical first-direction shift isomorphism `B.totalShift₁Iso (-1)`.
/-- Remark 12.18.7: for a self-homotopy in the first direction, the morphism
`Tot(A) ⟶ Tot(B)[-1]` corresponding to the induced total homotopy via Lemma 12.14.9 agrees with
the totalization of the associated morphism `A ⟶ B[-1,0]`, followed by the canonical
first-direction shift comparison `B.totalShift₁Iso (-1)`. -/
theorem totalHomotopyOfHomotopy₁_hom_to_shift_eq
    {φ : A ⟶ B} (h : Homotopy φ φ) :
    cochainComplex_self_homotopy_equiv_hom_to_shift (total.map φ (up ℤ))
        (totalHomotopyOfHomotopy₁ h) =
      total.map (cochainComplex_self_homotopy_equiv_hom_to_shift φ h) (up ℤ) ≫
        (B.totalShift₁Iso (-1)).hom := by
  sorry

end FirstDirectionHomotopy

section DegreewiseSplit

variable [CategoryTheory.Limits.HasCountableCoproducts C]

local instance firstDirectionTotalFunctorAdditive :
    (totalFunctor C (up ℤ) (up ℤ) (up ℤ)).Additive where
  map_add := by
    intro K L f g
    ext n
    apply total.hom_ext
    intro p q h
    change K.ιTotal (up ℤ) p q n h ≫ (total.map (f + g) (up ℤ)).f n =
        K.ιTotal (up ℤ) p q n h ≫ ((total.map f (up ℤ)).f n + (total.map g (up ℤ)).f n)
    rw [Preadditive.comp_add, ιTotal_map, ιTotal_map]
    rw [show ((f + g).f p).f q = (f.f p).f q + (g.f p).f q by rfl]
    rw [Preadditive.add_comp, ιTotal_map]

variable (S : ShortComplex (HomologicalComplex₂ C (up ℤ) (up ℤ)))

variable (σ : ∀ p : ℤ, (S.map (eval (CochainComplex C ℤ) (up ℤ) p)).Splitting)

/-- The degree-`n` retraction on the totalized short complex induced by the degreewise retractions
of the outer split short complex. -/
private noncomputable def totalizedDegreewiseRetraction (n : ℤ) :
    ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).X₂ ⟶
      ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).X₁ := by
  simpa using
    (S.X₂.totalDesc fun p q h ↦ ((σ p).r).f q ≫ S.X₁.ιTotal (up ℤ) p q n h)

/-- The degree-`n` section on the totalized short complex induced by the degreewise sections of the
outer split short complex. -/
private noncomputable def totalizedDegreewiseSection (n : ℤ) :
    ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).X₃ ⟶
      ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).X₂ := by
  simpa using
    (S.X₃.totalDesc fun p q h ↦ ((σ p).s).f q ≫ S.X₂.ιTotal (up ℤ) p q n h)

-- Proof sketch: precompose with each summand inclusion `S.X₂.ιTotal (up ℤ) p q n h` and use the
-- identity `((σ p).f_r).f q` in bidegree `(p,q)`.
/-- The induced totalized retraction is a retraction of the first map in degree `n`. -/
private lemma totalizedDegreewiseRetraction_f_r (n : ℤ) :
    ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).f ≫
      totalizedDegreewiseRetraction S σ n = 𝟙 _ :=
  sorry

-- Proof sketch: precompose with each summand inclusion `S.X₃.ιTotal (up ℤ) p q n h` and use the
-- identity `((σ p).s_g).f q` in bidegree `(p,q)`.
/-- The induced totalized section is a section of the second map in degree `n`. -/
private lemma totalizedDegreewiseSection_s_g (n : ℤ) :
    totalizedDegreewiseSection S σ n ≫
      ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).g =
        𝟙 _ :=
  sorry

-- Proof sketch: verify the identity after precomposing with each summand inclusion and apply the
-- splitting identity `((σ p).id).f q` componentwise in bidegree `(p,q)`.
/-- The totalized retractions and sections satisfy the splitting identity in every total degree. -/
private lemma totalizedDegreewiseSplitting_id (n : ℤ) :
    totalizedDegreewiseRetraction S σ n ≫
        ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).f +
      ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).g ≫
        totalizedDegreewiseSection S σ n =
      𝟙 _ :=
  sorry

/-- The degreewise splitting on the totalized short complex induced by the outer degreewise
splittings of a short complex of cohomological double complexes. -/
noncomputable def totalizedDegreewiseSplitting (n : ℤ) :
    ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).Splitting where
  r := totalizedDegreewiseRetraction S σ n
  s := totalizedDegreewiseSection S σ n
  f_r := totalizedDegreewiseRetraction_f_r S σ n
  s_g := totalizedDegreewiseSection_s_g S σ n
  id := totalizedDegreewiseSplitting_id S σ n

-- Proof sketch: expand `CochainComplex.homOfDegreewiseSplit` on both sides. On the summand
-- `C^{p,q}`, both morphisms are given by `π^{p+1,q} ≫ d_1^{p,q} ≫ s^{p,q}`; the comparison with
-- the shifted total complex is exactly the canonical isomorphism `S.X₁.totalShift₁Iso 1`.
/-- The connecting morphism of a degreewise split short complex of cohomological double complexes
agrees, after totalization, with the connecting morphism of the induced degreewise split short
complex of total complexes. -/
lemma totalized_degreewiseSplitConnectingHom_eq
    :
    (totalFunctor C (up ℤ) (up ℤ) (up ℤ)).map (CochainComplex.homOfDegreewiseSplit S σ) ≫
        (S.X₁.totalShift₁Iso 1).hom =
      CochainComplex.homOfDegreewiseSplit
        (S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))) (totalizedDegreewiseSplitting S σ) :=
  sorry

end DegreewiseSplit
