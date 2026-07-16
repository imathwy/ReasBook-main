import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_18_3
import stacks_proof.stacks_project.Chap12.Lemma_12_14_9
import stacks_proof.stacks_project.Chap12.Remark_12_18_5

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

/-- Helper for Remark 12.18.7: when `m` is the predecessor of `n`, the summand indexed by
`(p,q)` in total degree `n` contributes to total degree `m` through `(p - 1, q)`. -/
private lemma totalHomotopyOfHomotopy₁_targetEq {p q n m : ℤ}
    (hpq : p + q = n) (hrel : (up ℤ).Rel m n) :
    (p - 1) + q = m := by
  have hm : m + 1 = n := by
    simpa [ComplexShape.up_Rel] using hrel
  omega

/-- Helper for Remark 12.18.7: the guarded predecessor component of the induced total homotopy is
the totalization of the degreewise homotopy components. -/
private noncomputable def totalHomotopyOfHomotopy₁Hom
    {f g : A ⟶ B} (h : Homotopy f g) (n m : ℤ) :
    (Tot(A)).X n ⟶ (Tot(B)).X m :=
  if hrel : (up ℤ).Rel m n then
    A.totalDesc fun p q hpq ↦
      (h.hom p (p - 1)).f q ≫
        B.ιTotal (up ℤ) (p - 1) q m (totalHomotopyOfHomotopy₁_targetEq hpq hrel)
  else
    0

/-- Helper for Remark 12.18.7: on a fixed antidiagonal summand, the guarded totalized homotopy
component is exactly the corresponding degreewise homotopy component. -/
private lemma ιTotal_totalHomotopyOfHomotopy₁Hom
    {f g : A ⟶ B} (h : Homotopy f g) (p q n m : ℤ) (hpq : p + q = n)
    (hrel : (up ℤ).Rel m n) :
    A.ιTotal (up ℤ) p q n hpq ≫ totalHomotopyOfHomotopy₁Hom h n m =
      (h.hom p (p - 1)).f q ≫
        B.ιTotal (up ℤ) (p - 1) q m (totalHomotopyOfHomotopy₁_targetEq hpq hrel) := by
  -- Expand the guarded `totalDesc` definition and read off the chosen summand.
  rw [totalHomotopyOfHomotopy₁Hom]
  simp only [dif_pos hrel, HomologicalComplex₂.ι_totalDesc]

/-- Helper for Remark 12.18.7: the guarded totalized homotopy vanishes away from predecessor
degrees. -/
private lemma totalHomotopyOfHomotopy₁Hom_zero
    {f g : A ⟶ B} (h : Homotopy f g) (n m : ℤ) (hrel : ¬ (up ℤ).Rel m n) :
    totalHomotopyOfHomotopy₁Hom h n m = 0 := by
  -- The guard forces the map to be zero whenever `m` is not the predecessor of `n`.
  rw [totalHomotopyOfHomotopy₁Hom]
  simp only [dif_neg hrel]

/-- Helper for Remark 12.18.7: the guarded totalized homotopy satisfies the homotopy commutator
identity on total complexes. -/
private lemma totalHomotopyOfHomotopy₁_comm
    {f g : A ⟶ B} (h : Homotopy f g) (n : ℤ) :
    (total.map f (up ℤ)).f n =
      dNext n (totalHomotopyOfHomotopy₁Hom h) +
        prevD n (totalHomotopyOfHomotopy₁Hom h) + (total.map g (up ℤ)).f n := by
  -- TODO: componentwise rewrite through `total_d`, `ι_D₁`, and `ι_D₂`, then combine the
  -- degreewise first-direction homotopy identity `h.comm p` with the chain-map commutativity of
  -- `h.hom p (p - 1)` on the second index.
  sorry

/-- Remark 12.18.7: a homotopy between morphisms of cohomological double complexes induces a
canonical homotopy between the associated total-complex maps. -/
@[stacks 0G6B]
noncomputable def totalHomotopyOfHomotopy₁
    {f g : A ⟶ B} (h : Homotopy f g) :
    Homotopy (total.map f (up ℤ)) (total.map g (up ℤ)) :=
  { hom := totalHomotopyOfHomotopy₁Hom h
    zero := totalHomotopyOfHomotopy₁Hom_zero h
    comm := totalHomotopyOfHomotopy₁_comm h }

/-- Remark 12.18.7: a homotopy between morphisms of cohomological double complexes induces a
homotopy between the associated total-complex maps. -/
@[stacks 0G6B]
theorem total_homotopic_of_homotopy₁
    {f g : A ⟶ B} (h : Homotopy f g) :
    homotopic C (up ℤ) (total.map f (up ℤ)) (total.map g (up ℤ)) :=
  ⟨totalHomotopyOfHomotopy₁ h⟩

/-- Remark 12.18.7: homotopic morphisms of cohomological double complexes induce the same
morphism between the associated total complexes in the homotopy category. -/
@[stacks 0G6B]
lemma total_map_eq_in_homotopyCategory_of_homotopy₁
    {f g : A ⟶ B} (h : Homotopy f g) :
    (HomotopyCategory.quotient C (up ℤ)).map (total.map f (up ℤ)) =
      (HomotopyCategory.quotient C (up ℤ)).map (total.map g (up ℤ)) := by
  exact HomotopyCategory.eq_of_homotopy _ _ (totalHomotopyOfHomotopy₁ h)

/-- Helper for Remark 12.18.7: the map into the `(-1)`-shift corresponding to a self-homotopy is
characterized componentwise by the degree-`(-1)` entry of the homotopy. -/
private lemma self_homotopy_to_shift_component
    {A B : CochainComplex C ℤ} {a : A ⟶ B} (h : Homotopy a a) (n : ℤ) :
    (cochainComplex_self_homotopy_equiv_hom_to_shift a h).f n ≫
        (B.shiftFunctorObjXIso (-1) n (n - 1) (by omega)).hom =
      h.hom n (n - 1) :=
  by
    -- TODO: reduce `cochainComplex_self_homotopy_equiv_hom_to_shift` to
    -- `Cocycle.equivHomShift.symm` and evaluate the resulting degree-`(-1)` component with
    -- `Cochain.rightShift_v`, cancelling the residual `shiftFunctorObjXIso` transport.
    sorry

-- Proof sketch: both sides encode the same degree `-1` cochain on the total complexes. Expanding
-- `cochainComplex_self_homotopy_equiv_hom_to_shift` and `totalHomotopyOfHomotopy₁`, the component
-- on the summand indexed by `(p, q)` is `((h.hom p (p - 1)).f q)`, and the comparison with the
-- shifted total complex is the canonical first-direction shift isomorphism `B.totalShift₁Iso (-1)`.
/-- Remark 12.18.7: for a self-homotopy in the first direction, the morphism
`Tot(A) ⟶ Tot(B)[-1]` corresponding to the induced total homotopy via Lemma 12.14.9 agrees with
the totalization of the associated morphism `A ⟶ B[-1,0]`, followed by the canonical
first-direction shift comparison `B.totalShift₁Iso (-1)`. -/
@[stacks 0G6B]
theorem totalHomotopyOfHomotopy₁_hom_to_shift_eq
    {φ : A ⟶ B} (h : Homotopy φ φ) :
    cochainComplex_self_homotopy_equiv_hom_to_shift (total.map φ (up ℤ))
        (totalHomotopyOfHomotopy₁ h) =
      total.map (cochainComplex_self_homotopy_equiv_hom_to_shift φ h) (up ℤ) ≫
        (B.totalShift₁Iso (-1)).hom :=
  by
    -- TODO: compare both maps on each summand `A.ιTotal (up ℤ) p q n hpq`, postcompose with the
    -- component shift isomorphism of `Tot(B)⟦-1⟧`, and use the explicit
    -- `ιTotal_totalHomotopyOfHomotopy₁Hom` formula together with
    -- `B.ι_totalShift₁Iso_hom_f_assoc (-1)`.
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

/-- Helper for Remark 12.18.7: on the summand `(p,q)` of `Tot(S.X₂)^n`, the totalized retraction
is exactly the degreewise retraction `((σ p).r).f q`. -/
private lemma ιTotal_totalizedDegreewiseRetraction
    (n p q : ℤ) (h : p + q = n) :
    S.X₂.ιTotal (up ℤ) p q n h ≫ totalizedDegreewiseRetraction S σ n =
      ((σ p).r).f q ≫ S.X₁.ιTotal (up ℤ) p q n h := by
  -- Unfold the totalized retraction and read off its value on the fixed antidiagonal summand.
  simpa [totalizedDegreewiseRetraction]

/-- Helper for Remark 12.18.7: on the summand `(p,q)` of `Tot(S.X₃)^n`, the totalized section is
exactly the degreewise section `((σ p).s).f q`. -/
private lemma ιTotal_totalizedDegreewiseSection
    (n p q : ℤ) (h : p + q = n) :
    S.X₃.ιTotal (up ℤ) p q n h ≫ totalizedDegreewiseSection S σ n =
      ((σ p).s).f q ≫ S.X₂.ιTotal (up ℤ) p q n h := by
  -- Unfold the totalized section and read off its value on the fixed antidiagonal summand.
  simpa [totalizedDegreewiseSection]

-- Proof sketch: precompose with each summand inclusion `S.X₂.ιTotal (up ℤ) p q n h` and use the
-- identity `((σ p).f_r).f q` in bidegree `(p,q)`.
/-- The induced totalized retraction is a retraction of the first map in degree `n`. -/
private lemma totalizedDegreewiseRetraction_f_r (n : ℤ) :
    ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).f ≫
      totalizedDegreewiseRetraction S σ n = 𝟙 _ :=
  by
    -- Check the identity on each `(p,q)` summand of the total complex.
    apply total.hom_ext
    intro p q h
    change S.X₁.ιTotal (up ℤ) p q n h ≫
        (((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).f ≫
          totalizedDegreewiseRetraction S σ n) =
      S.X₁.ιTotal (up ℤ) p q n h ≫ 𝟙 _
    change S.X₁.ιTotal (up ℤ) p q n h ≫ (total.map S.f (up ℤ)).f n ≫
        totalizedDegreewiseRetraction S σ n =
      S.X₁.ιTotal (up ℤ) p q n h ≫ 𝟙 _
    simpa [totalizedDegreewiseRetraction] using
      congrArg (fun m ↦ m ≫ S.X₁.ιTotal (up ℤ) p q n h)
        (congrArg (fun k ↦ k.f q) ((σ p).f_r))

-- Proof sketch: precompose with each summand inclusion `S.X₃.ιTotal (up ℤ) p q n h` and use the
-- identity `((σ p).s_g).f q` in bidegree `(p,q)`.
/-- The induced totalized section is a section of the second map in degree `n`. -/
private lemma totalizedDegreewiseSection_s_g (n : ℤ) :
    totalizedDegreewiseSection S σ n ≫
      ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).g =
        𝟙 _ :=
  by
    -- Check the identity on each `(p,q)` summand of the total complex.
    apply total.hom_ext
    intro p q h
    change S.X₃.ιTotal (up ℤ) p q n h ≫
        (totalizedDegreewiseSection S σ n ≫
          ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).g) =
      S.X₃.ιTotal (up ℤ) p q n h ≫ 𝟙 _
    change S.X₃.ιTotal (up ℤ) p q n h ≫ totalizedDegreewiseSection S σ n ≫
        (total.map S.g (up ℤ)).f n =
      S.X₃.ιTotal (up ℤ) p q n h ≫ 𝟙 _
    simpa [totalizedDegreewiseSection] using
      congrArg (fun m ↦ m ≫ S.X₃.ιTotal (up ℤ) p q n h)
        (congrArg (fun k ↦ k.f q) ((σ p).s_g))

-- Proof sketch: verify the identity after precomposing with each summand inclusion and apply the
-- splitting identity `((σ p).id).f q` componentwise in bidegree `(p,q)`.
/-- The totalized retractions and sections satisfy the splitting identity in every total degree. -/
private lemma totalizedDegreewiseSplitting_id (n : ℤ) :
    totalizedDegreewiseRetraction S σ n ≫
        ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).f +
      ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).g ≫
        totalizedDegreewiseSection S σ n =
      𝟙 _ :=
  by
    -- Check the splitting identity on each `(p,q)` summand of `Tot(S.X₂)^n`.
    apply total.hom_ext
    intro p q h
    change S.X₂.ιTotal (up ℤ) p q n h ≫
        (totalizedDegreewiseRetraction S σ n ≫
            ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).f +
          ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).g ≫
            totalizedDegreewiseSection S σ n) =
      S.X₂.ιTotal (up ℤ) p q n h ≫ 𝟙 _
    change (S.X₂.ιTotal (up ℤ) p q n h ≫ totalizedDegreewiseRetraction S σ n ≫
          (total.map S.f (up ℤ)).f n) +
        (S.X₂.ιTotal (up ℤ) p q n h ≫ (total.map S.g (up ℤ)).f n ≫
          totalizedDegreewiseSection S σ n) =
      S.X₂.ιTotal (up ℤ) p q n h ≫ 𝟙 _
    -- Rewrite the totalized retraction, section, and the totalized maps on the chosen summand.
    rw [Preadditive.comp_add, Category.assoc, ιTotal_totalizedDegreewiseRetraction,
      ιTotal_map, Category.assoc, Category.assoc, ιTotal_totalizedDegreewiseSection]
    -- The degreewise splitting identity on column `p` closes the component computation.
    simpa [Category.assoc] using congrArg (fun k ↦ k.f q) ((σ p).id)

/-- The degreewise splitting on the totalized short complex induced by the outer degreewise
splittings of a short complex of cohomological double complexes. -/
noncomputable def totalizedDegreewiseSplitting (n : ℤ) :
    ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).map (eval C (up ℤ) n)).Splitting where
  r := totalizedDegreewiseRetraction S σ n
  s := totalizedDegreewiseSection S σ n
  f_r := totalizedDegreewiseRetraction_f_r S σ n
  s_g := totalizedDegreewiseSection_s_g S σ n
  id := totalizedDegreewiseSplitting_id S σ n

/-- Helper for Remark 12.18.7: the vertical contribution in the totalized connecting morphism
vanishes because each degreewise section is a morphism of complexes and its composite with the
corresponding retraction is zero. -/
private lemma first_direction_vertical_term_vanishes (p q : ℤ) :
    ((σ p).s).f q ≫ (S.X₂.X p).d q (q + 1) ≫ ((σ p).r).f (q + 1) = 0 := by
  have hs :
      ((σ p).s).f q ≫ (S.X₂.X p).d q (q + 1) =
        (S.X₃.X p).d q (q + 1) ≫ ((σ p).s).f (q + 1) := by
    -- Each degreewise section is a cochain map in the second index.
    simpa using ((σ p).s).comm q (q + 1)
  have hz :
      (S.X₃.X p).d q (q + 1) ≫ ((σ p).s).f (q + 1) ≫ ((σ p).r).f (q + 1) =
        (S.X₃.X p).d q (q + 1) ≫ 0 := by
    have hs_r_comp : ((σ p).s).f (q + 1) ≫ ((σ p).r).f (q + 1) = 0 := by
      -- Read off the `(q+1)`-component of the identity `s ≫ r = 0`.
      simpa using congrArg (fun m ↦ m.f (q + 1)) ((σ p).s_r)
    -- The `(q+1)`-component of `s ≫ r = 0` kills the section-retraction composite.
    simpa [Category.assoc] using
      congrArg (fun m ↦ (S.X₃.X p).d q (q + 1) ≫ m) hs_r_comp
  calc
    ((σ p).s).f q ≫ (S.X₂.X p).d q (q + 1) ≫ ((σ p).r).f (q + 1) =
        (S.X₃.X p).d q (q + 1) ≫ ((σ p).s).f (q + 1) ≫ ((σ p).r).f (q + 1) := by
      simpa [Category.assoc] using congrArg (fun m ↦ m ≫ ((σ p).r).f (q + 1)) hs
    _ = (S.X₃.X p).d q (q + 1) ≫ 0 := hz
    _ = 0 := by
      exact CategoryTheory.Limits.comp_zero (f := (S.X₃.X p).d q (q + 1))

/-- Helper for Remark 12.18.7: the degree-`n` component of the owner connecting morphism on the
totalized short complex is the textbook composite `s'ⁿ ≫ d_Tot(B)ⁿ ≫ π'ⁿ⁺¹`. -/
private theorem totalized_homOfDegreewiseSplit_component (n : ℤ) :
    (CochainComplex.homOfDegreewiseSplit
        (S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))) (totalizedDegreewiseSplitting S σ)).f n =
      totalizedDegreewiseSection S σ n ≫
        ((S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))).X₂).d n (n + 1) ≫
        totalizedDegreewiseRetraction S σ (n + 1) := by
  -- Read the component directly from the owner cochain-level connecting morphism formula.
  simpa [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cochain.mk_v,
    totalizedDegreewiseSplitting, totalizedDegreewiseSection, totalizedDegreewiseRetraction,
    Category.assoc] using
    (CochainComplex.homOfDegreewiseSplit_f
      (S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))) (totalizedDegreewiseSplitting S σ) n)

/-- Helper for Remark 12.18.7: the degree-`p` component of the first-direction owner connecting
morphism is the textbook horizontal composite `sᵖ ≫ d₁ᵖ ≫ πᵖ⁺¹`. -/
private theorem first_direction_homOfDegreewiseSplit_component (p : ℤ) :
    (CochainComplex.homOfDegreewiseSplit S σ).f p =
      (σ p).s ≫ S.X₂.d p (p + 1) ≫ (σ (p + 1)).r := by
  -- Read the component directly from the owner cochain-level connecting morphism formula.
  simpa [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cochain.mk_v,
    Category.assoc] using (CochainComplex.homOfDegreewiseSplit_f S σ p)

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
        (S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))) (totalizedDegreewiseSplitting S σ) := by
  -- TODO: compare both connecting morphisms on each summand `S.X₃.ιTotal (up ℤ) p q n h`, use
  -- `first_direction_homOfDegreewiseSplit_component`, and rewrite the totalized owner map through
  -- `totalized_homOfDegreewiseSplit_component` plus the `D₁`/`D₂` decomposition of `S.X₂.total_d`.
  sorry

end DegreewiseSplit
