import Mathlib
import StacksProject_2024.Chap12.Definition_12_18_3
import StacksProject_2024.Chap12.Lemma_12_14_9
import StacksProject_2024.Chap12.Remark_12_18_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomologicalComplex HomologicalComplex₂ HomotopyCategory
open scoped HomologicalComplex₂

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-
Source/core/bridge triage:
- primary domain: cohomological bicomplexes, their total complexes, and second-direction
  homotopies / degreewise split short complexes.
- core/canonical owners already provided upstream:
  `HomologicalComplex₂.flipEquivalence`,
  `HomologicalComplex₂.totalFlipIso`,
  `HomologicalComplex₂.totalShift₂Iso`,
  `CochainComplex.homOfDegreewiseSplit`.
- target items here are bridge/view declarations: they express the second-direction variants by
  passing through those owner constructions after transporting along the flip equivalence and the
  canonical symmetry isomorphism of total complexes.

Primitive data:
- bicomplexes, bicomplex morphisms, and short complexes of bicomplexes,
- a homotopy after flipping in the second direction,
- degreewise splittings after flipping and evaluating.

Derived API:
- `HomologicalComplex₂.homToBidegreeShift₂OfFlip`,
- `totalHomotopyOfHomotopy`,
- `total_homotopic_of_homotopy`,
- `total_map_eq_in_homotopyCategory_of_homotopy₂`,
- `homOfDegreewiseSplit₂`,
- `totalizedShortComplex₂`,
- `totalizedDegreewiseSplitting₂`,
- `totalized_degreewiseSplitConnectingHom₂_eq`.
-/

/- Companion recall: the owner shift-total compatibility in the second variable is the canonical
isomorphism `K.totalShift₂Iso 1 : Tot((shiftFunctor₂ C 1).obj K) ≅ Tot(K)⟦1⟧`;
the orientation in Remark 12.18.6 is its inverse. -/
#check HomologicalComplex₂.totalShift₂Iso

namespace HomologicalComplex₂

/-- A morphism from the flipped bicomplex into the `n`-shift of a flipped bicomplex corresponds
canonically to a morphism into the bidegree shift `[0,n]` of the original bicomplex. -/
noncomputable def homToBidegreeShift₂OfFlip {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (n : ℤ)
    (f : K.flip ⟶ L.flip⟦n⟧) : K ⟶ L[0, n] :=
  (flipEquivalence C (up ℤ) (up ℤ)).functor.preimage
      (show K.flip ⟶ (flipFunctor C (up ℤ) (up ℤ)).obj ((shiftFunctor₂ C n).obj L) from
        by
          simpa [HomologicalComplex₂.shiftFunctor₁, HomologicalComplex₂.shiftFunctor₂] using f) ≫
    (CategoryTheory.shiftFunctorZero (HomologicalComplex₂ C (up ℤ) (up ℤ)) ℤ).inv.app
      ((shiftFunctor₂ C n).obj L)

/-- Helper for Remark 12.18.6: composing through the auxiliary zero first-direction shift and
back is the identity. -/
private theorem shiftFunctorZero_inv_hom_cancel
    {X Y : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : X ⟶ Y) :
    f ≫ (CategoryTheory.shiftFunctorZero (HomologicalComplex₂ C (up ℤ) (up ℤ)) ℤ).inv.app Y ≫
        (CategoryTheory.shiftFunctorZero (HomologicalComplex₂ C (up ℤ) (up ℤ)) ℤ).hom.app Y =
      f := by
  -- The auxiliary zero first-direction shift is an identity after `inv ≫ hom`.
  simpa [Category.assoc] using
    congrArg
      (fun m ↦ f ≫ m)
      ((CategoryTheory.shiftFunctorZero (HomologicalComplex₂ C (up ℤ) (up ℤ)) ℤ).inv_hom_id_app Y)

/-- Helper for Remark 12.18.6: after canceling the auxiliary zero first-direction shift,
`homToBidegreeShift₂OfFlip` is exactly the canonical preimage under the flip equivalence. -/
@[simp, reassoc]
lemma homToBidegreeShift₂OfFlip_hom_shiftFunctorZero
    {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (n : ℤ)
    (f : K.flip ⟶ L.flip⟦n⟧) :
    homToBidegreeShift₂OfFlip n f ≫
        (CategoryTheory.shiftFunctorZero (HomologicalComplex₂ C (up ℤ) (up ℤ)) ℤ).hom.app
          ((shiftFunctor₂ C n).obj L) =
      (flipEquivalence C (up ℤ) (up ℤ)).functor.preimage
        (show K.flip ⟶ (flipFunctor C (up ℤ) (up ℤ)).obj ((shiftFunctor₂ C n).obj L) from
          by
            simpa [HomologicalComplex₂.shiftFunctor₁, HomologicalComplex₂.shiftFunctor₂] using
              f) := by
  -- Cancel the auxiliary zero-shift isomorphism inserted to land in `L[0,n]`.
  simpa [homToBidegreeShift₂OfFlip] using
    shiftFunctorZero_inv_hom_cancel
      ((flipEquivalence C (up ℤ) (up ℤ)).functor.preimage
        (show K.flip ⟶ (flipFunctor C (up ℤ) (up ℤ)).obj ((shiftFunctor₂ C n).obj L) from
          by
            simpa [HomologicalComplex₂.shiftFunctor₁, HomologicalComplex₂.shiftFunctor₂] using
              f))

end HomologicalComplex₂

section SecondDirectionHomotopy

variable {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)}
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)] {φ ψ : K ⟶ L}

private instance flipHasTotal (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] :
    ((flipFunctor C (up ℤ) (up ℤ)).obj K).HasTotal (up ℤ) := by
  change K.flip.HasTotal (up ℤ)
  infer_instance

-- Proof sketch: precompose the naturality square of `totalFlipIso` with
-- `(K.totalFlipIso (up ℤ)).inv`, then simplify using `Iso.inv_hom_id_assoc`.
private theorem totalFlipIso_inv_map_flip_eq
    (φ : K ⟶ L) :
    (K.totalFlipIso (up ℤ)).inv ≫ total.map ((flipFunctor C (up ℤ) (up ℤ)).map φ) (up ℤ) ≫
        (L.totalFlipIso (up ℤ)).hom =
      total.map φ (up ℤ) := by
  have hnat :
      total.map ((flipFunctor C (up ℤ) (up ℤ)).map φ) (up ℤ) ≫
          (L.totalFlipIso (up ℤ)).hom =
        (K.totalFlipIso (up ℤ)).hom ≫ total.map φ (up ℤ) := by
    -- Compare the two composites on each antidiagonal summand of `Tot(K.flip)`.
    ext n
    apply total.hom_ext
    intro q p h
    calc
      K.flip.ιTotal (up ℤ) q p n h ≫
          (total.map ((flipFunctor C (up ℤ) (up ℤ)).map φ) (up ℤ)).f n ≫
            (L.totalFlipIso (up ℤ)).hom.f n =
        (φ.f p).f q ≫
          (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
            L.ιTotal (up ℤ) p q n
              (by rw [← ComplexShape.π_symm (up ℤ) (up ℤ) (up ℤ) p q, h])) := by
        rw [ιTotal_map_assoc, ιTotal_totalFlipIso_f_hom]
        rfl
      _ =
          ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
            ((φ.f p).f q ≫
              L.ιTotal (up ℤ) p q n
                (by rw [← ComplexShape.π_symm (up ℤ) (up ℤ) (up ℤ) p q, h])) := by
        rw [Linear.comp_units_smul]
      _ =
          K.flip.ιTotal (up ℤ) q p n h ≫
            (K.totalFlipIso (up ℤ)).hom.f n ≫ (total.map φ (up ℤ)).f n := by
        rw [ιTotal_totalFlipIso_f_hom_assoc, ιTotal_map]
  -- Precompose the naturality square by the inverse flip symmetry.
  rw [Category.assoc, hnat, Category.assoc, Iso.inv_hom_id_assoc]

/-- Helper for Remark 12.18.6: transporting the owner totalized homotopy across the flip
symmetry yields the source-facing homotopy on total complexes. -/
private noncomputable def totalHomotopyOfHomotopy_aux
    (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map φ) ((flipFunctor C (up ℤ) (up ℤ)).map ψ)) :
    Homotopy (total.map φ (up ℤ)) (total.map ψ (up ℤ)) :=
  -- TODO: once `totalFlipIso_inv_map_flip_eq` is restored, this is the transported owner
  -- homotopy `((totalFunctor ...).mapHomotopy h)` across `totalFlipIso`.
  sorry

/-- Remark 12.18.6: if two morphisms of double complexes are homotopic when the double complexes
are viewed as complexes in the second index, then the induced morphisms of associated total
complexes are connected by a canonical homotopy. -/
@[stacks 0G6A]
noncomputable def totalHomotopyOfHomotopy
    (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map φ) ((flipFunctor C (up ℤ) (up ℤ)).map ψ)) :
    Homotopy (total.map φ (up ℤ)) (total.map ψ (up ℤ)) :=
  totalHomotopyOfHomotopy_aux (K := K) (L := L) (φ := φ) (ψ := ψ) h

/-- Remark 12.18.6: if two morphisms of double complexes are homotopic when the double complexes
are viewed as complexes in the second index, then the induced morphisms of associated total
complexes are homotopic. -/
@[stacks 0G6A]
theorem total_homotopic_of_homotopy
    (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map φ) ((flipFunctor C (up ℤ) (up ℤ)).map ψ)) :
    homotopic C (up ℤ) (total.map φ (up ℤ)) (total.map ψ (up ℤ)) :=
  ⟨totalHomotopyOfHomotopy h⟩

-- Proof sketch: pass to the homotopy category and apply `HomotopyCategory.eq_of_homotopy` to the
-- total-complex homotopy provided by `totalHomotopyOfHomotopy`.
/-- Homotopic morphisms in the second direction induce the same morphism between the associated
total complexes in the homotopy category. -/
theorem total_map_eq_in_homotopyCategory_of_homotopy₂
    (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map φ) ((flipFunctor C (up ℤ) (up ℤ)).map ψ)) :
    (HomotopyCategory.quotient C (up ℤ)).map (total.map φ (up ℤ)) =
      (HomotopyCategory.quotient C (up ℤ)).map (total.map ψ (up ℤ)) := by
  exact HomotopyCategory.eq_of_homotopy _ _ (totalHomotopyOfHomotopy h)

/-- Helper for Remark 12.18.6: the map into the `(-1)`-shift corresponding to a self-homotopy is
characterized componentwise by the degree-`(-1)` entry of the homotopy. -/
lemma cochainComplex_self_homotopy_equiv_hom_to_shift_component
    {A B : CochainComplex C ℤ} {a : A ⟶ B} (h : Homotopy a a) (n : ℤ) :
    (cochainComplex_self_homotopy_equiv_hom_to_shift a h).f n ≫
        (B.shiftFunctorObjXIso (-1) n (n - 1) (by omega)).hom =
      h.hom n (n - 1) := by
  -- TODO: normalize the hidden cast in `cochainComplex_self_homotopy_equiv_hom_to_shift` and
  -- then evaluate `Cocycle.equivHomShift.symm` via the degreewise `rightShift` formula.
  sorry

-- Proof sketch: both sides encode the same degree `-1` cochain on the total complexes. Expanding
-- `cochainComplex_self_homotopy_equiv_hom_to_shift` and `totalHomotopyOfHomotopy`, the component
-- on the summand indexed by `(p, q)` is the signed second-direction homotopy component
-- `(-1)^p h.hom q (q - 1)).f p`, and the comparison with the shifted total complex is the
-- inverse of the canonical bidegree-shift comparison `L.totalShiftBidegreeIso 0 (-1)`.
/-- Remark 12.18.6: for a self-homotopy in the second direction, the morphism
`Tot(K) ⟶ Tot(L)[-1]` corresponding to the induced total homotopy via Lemma 12.14.9 agrees with
the totalization of the associated morphism `K ⟶ L[0,-1]`, followed by the inverse of the
canonical bidegree-shift comparison `L.totalShiftBidegreeIso 0 (-1)`. -/
@[stacks 0G6A]
theorem totalHomotopyOfHomotopy_hom_to_shift_eq
    (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map φ) ((flipFunctor C (up ℤ) (up ℤ)).map φ)) :
    cochainComplex_self_homotopy_equiv_hom_to_shift (total.map φ (up ℤ))
        (totalHomotopyOfHomotopy h) =
      total.map
          (homToBidegreeShift₂OfFlip (-1)
            (cochainComplex_self_homotopy_equiv_hom_to_shift
              ((flipFunctor C (up ℤ) (up ℤ)).map φ) h))
          (up ℤ) ≫
        (L.totalShiftBidegreeIso 0 (-1)).inv := by
  -- Route correction: the source proof compares both maps on a fixed summand `K.ιTotal ... p q`
  -- and then invokes the `(a,b) = (0,-1)` component formula for `totalShiftBidegreeIso`.
  -- That comparison is still blocked upstream because `Remark_12_18_5` does not yet compile.
  -- TODO: compare both maps on each total summand `(p,q)`; the left-hand side exposes the
  -- `(-1)^p` component of `totalHomotopyOfHomotopy`, and the right-hand side should be reduced
  -- via `HomologicalComplex₂.ι_totalShiftBidegreeIso_hom_f` with `(a,b) = (0,-1)`.
  sorry

end SecondDirectionHomotopy

section DegreewiseSplit

variable [CategoryTheory.Limits.HasCountableCoproducts C]

local instance flipFunctorAdditive : (flipFunctor C (up ℤ) (up ℤ)).Additive where
  map_add := by
    intro K L f g
    ext i j
    rfl

local instance totalFunctorAdditive : (totalFunctor C (up ℤ) (up ℤ) (up ℤ)).Additive where
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
variable (σ : ∀ q : ℤ,
  (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
    HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).Splitting)

/-- The short complex of total complexes obtained from a short complex of bicomplexes by
totalization. -/
abbrev totalizedShortComplex₂ : ShortComplex (CochainComplex C ℤ) :=
  S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))

/-- Helper for Remark 12.18.6: the totalized short complex is definitionally the image of `S`
under the totalization functor. -/
private theorem totalizedShortComplex₂_eq :
    totalizedShortComplex₂ S = S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ)) :=
  rfl

/-- The connecting morphism attached to a degreewise split short complex in the second direction,
obtained by transporting the owner map `CochainComplex.homOfDegreewiseSplit` on the flipped short
complex back along the canonical flip equivalence. -/
noncomputable def homOfDegreewiseSplit₂ : S.X₃ ⟶ S.X₁[0, 1] :=
  homToBidegreeShift₂OfFlip 1 <|
    CochainComplex.homOfDegreewiseSplit (S.map (flipFunctor C (up ℤ) (up ℤ))) σ

/-- The degree-`n` retraction on the totalized short complex induced by the flipped degreewise
retractions. -/
noncomputable def totalizedDegreewiseRetraction₂ (n : ℤ) :
    ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).X₂ ⟶
      ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).X₁ := by
  simpa [totalizedShortComplex₂] using
    (S.X₂.totalDesc fun p q h ↦ ((σ q).r).f p ≫ S.X₁.ιTotal (up ℤ) p q n h)

/-- The degree-`n` section on the totalized short complex induced by the flipped degreewise
sections. -/
noncomputable def totalizedDegreewiseSection₂ (n : ℤ) :
    ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).X₃ ⟶
      ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).X₂ := by
  simpa [totalizedShortComplex₂] using
    (S.X₃.totalDesc fun p q h ↦ ((σ q).s).f p ≫ S.X₂.ιTotal (up ℤ) p q n h)

/-- Helper for Remark 12.18.6: on the summand `(p,q)` of `Tot(S.X₂)^n`, the totalized retraction
is exactly the degreewise retraction `((σ q).r).f p`. -/
private lemma ιTotal_totalizedDegreewiseRetraction₂
    (n p q : ℤ) (h : p + q = n) :
    S.X₂.ιTotal (up ℤ) p q n h ≫ totalizedDegreewiseRetraction₂ S σ n =
      ((σ q).r).f p ≫ S.X₁.ιTotal (up ℤ) p q n h := by
  -- Unfold the totalized retraction and read off its value on the fixed antidiagonal summand.
  simpa [totalizedDegreewiseRetraction₂, totalizedShortComplex₂]

/-- Helper for Remark 12.18.6: on the summand `(p,q)` of `Tot(S.X₃)^n`, the totalized section is
exactly the degreewise section `((σ q).s).f p`. -/
private lemma ιTotal_totalizedDegreewiseSection₂
    (n p q : ℤ) (h : p + q = n) :
    S.X₃.ιTotal (up ℤ) p q n h ≫ totalizedDegreewiseSection₂ S σ n =
      ((σ q).s).f p ≫ S.X₂.ιTotal (up ℤ) p q n h := by
  -- Unfold the totalized section and read off its value on the fixed antidiagonal summand.
  simpa [totalizedDegreewiseSection₂, totalizedShortComplex₂]

-- Proof sketch: precompose with each summand inclusion `S.X₂.ιTotal (up ℤ) p q n h` and use the
-- identity `((σ q).f_r).f p` in bidegree `(p,q)`.
/-- The induced totalized retraction is a retraction of the first map in degree `n`. -/
lemma totalizedDegreewiseRetraction_f_r₂ (n : ℤ) :
    ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).f ≫
      totalizedDegreewiseRetraction₂ S σ n = 𝟙 _ := by
  -- Check the identity on each `(p,q)` summand of the total complex.
  apply total.hom_ext
  intro p q h
  change S.X₁.ιTotal (up ℤ) p q n h ≫
      (((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).f ≫
        totalizedDegreewiseRetraction₂ S σ n) =
    S.X₁.ιTotal (up ℤ) p q n h ≫ 𝟙 _
  change S.X₁.ιTotal (up ℤ) p q n h ≫ (total.map S.f (up ℤ)).f n ≫
      totalizedDegreewiseRetraction₂ S σ n =
    S.X₁.ιTotal (up ℤ) p q n h ≫ 𝟙 _
  simpa [totalizedDegreewiseRetraction₂, totalizedShortComplex₂] using
    congrArg (fun m ↦ m ≫ S.X₁.ιTotal (up ℤ) p q n h)
      (congrArg (fun k ↦ k.f p) ((σ q).f_r))

-- Proof sketch: precompose with each summand inclusion `S.X₃.ιTotal (up ℤ) p q n h` and use the
-- identity `((σ q).s_g).f p` in bidegree `(p,q)`.
/-- The induced totalized section is a section of the second map in degree `n`. -/
lemma totalizedDegreewiseSection_s_g₂ (n : ℤ) :
    totalizedDegreewiseSection₂ S σ n ≫
      ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).g = 𝟙 _ := by
  -- Check the identity on each `(p,q)` summand of the total complex.
  apply total.hom_ext
  intro p q h
  change S.X₃.ιTotal (up ℤ) p q n h ≫
      (totalizedDegreewiseSection₂ S σ n ≫
        ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).g) =
    S.X₃.ιTotal (up ℤ) p q n h ≫ 𝟙 _
  change S.X₃.ιTotal (up ℤ) p q n h ≫ totalizedDegreewiseSection₂ S σ n ≫
      (total.map S.g (up ℤ)).f n =
    S.X₃.ιTotal (up ℤ) p q n h ≫ 𝟙 _
  simpa [totalizedDegreewiseSection₂, totalizedShortComplex₂] using
    congrArg (fun m ↦ m ≫ S.X₃.ιTotal (up ℤ) p q n h)
      (congrArg (fun k ↦ k.f p) ((σ q).s_g))

-- Proof sketch: verify the identity after precomposing with each summand inclusion and apply the
-- splitting identity `((σ q).id).f p` componentwise in bidegree `(p,q)`.
/-- The totalized retractions and sections satisfy the splitting identity in every total degree. -/
lemma totalizedDegreewiseSplitting_id₂ (n : ℤ) :
    totalizedDegreewiseRetraction₂ S σ n ≫
        ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).f +
      ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).g ≫
        totalizedDegreewiseSection₂ S σ n =
      𝟙 _ := by
  -- Check the splitting identity on each summand `S.X₂.ιTotal (up ℤ) p q n h`.
  apply total.hom_ext
  intro p q h
  change S.X₂.ιTotal (up ℤ) p q n h ≫
      (totalizedDegreewiseRetraction₂ S σ n ≫
          ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).f +
        ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).g ≫
          totalizedDegreewiseSection₂ S σ n) =
    S.X₂.ιTotal (up ℤ) p q n h ≫ 𝟙 _
  have hid :
      ((((σ q).r).f p ≫
            ((S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
              HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).f).f p) +
          ((S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
              HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).g).f p ≫
            ((σ q).s).f p) ≫
        S.X₂.ιTotal (up ℤ) p q n h =
      S.X₂.ιTotal (up ℤ) p q n h := by
    -- The degreewise splitting identity in row `q` becomes the totalized identity after
    -- postcomposing with the inclusion of the `(p,q)` summand.
    simpa [Preadditive.comp_add, Category.assoc] using
      congrArg
        (fun m ↦ m ≫ S.X₂.ιTotal (up ℤ) p q n h)
        (congrArg (fun k ↦ k.f p) ((σ q).id))
  -- Rewrite the totalized maps on this summand to the rowwise splitting identity.
  rw [Preadditive.comp_add]
  rw [ιTotal_totalizedDegreewiseRetraction₂, Category.assoc, ιTotal_map_assoc]
  rw [ιTotal_map_assoc, ιTotal_totalizedDegreewiseSection₂]
  simpa [Category.assoc, totalizedShortComplex₂] using hid

/-- The degreewise splitting on the totalized short complex induced by the flipped degreewise
splittings of a short complex of bicomplexes. -/
noncomputable def totalizedDegreewiseSplitting₂ (n : ℤ) :
    ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).Splitting where
  r := totalizedDegreewiseRetraction₂ S σ n
  s := totalizedDegreewiseSection₂ S σ n
  f_r := totalizedDegreewiseRetraction_f_r₂ S σ n
  s_g := totalizedDegreewiseSection_s_g₂ S σ n
  id := totalizedDegreewiseSplitting_id₂ S σ n

/-- Helper for Remark 12.18.6: the horizontal contribution in the totalized second-direction
connecting morphism vanishes because each degreewise section is a morphism of complexes and its
composite with the corresponding retraction is zero. -/
private lemma second_direction_horizontal_term_vanishes (p q : ℤ) :
    ((σ q).s).f p ≫
        (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
          HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).X₂.d p (p + 1) ≫
        ((σ q).r).f (p + 1) = 0 := by
  have hs :
      ((σ q).s).f p ≫
          (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
            HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).X₂.d p (p + 1) =
        (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
          HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).X₃.d p (p + 1) ≫
            ((σ q).s).f (p + 1) := by
    -- Each degreewise section is a chain map in the first index.
    simpa using ((σ q).s).comm p (p + 1)
  have hz :
      (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
        HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).X₃.d p (p + 1) ≫
          ((σ q).s).f (p + 1) ≫ ((σ q).r).f (p + 1) =
        (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
          HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).X₃.d p (p + 1) ≫ 0 := by
    have hs_r_comp : ((σ q).s).f (p + 1) ≫ ((σ q).r).f (p + 1) = 0 := by
      -- Read off the `(p+1)`-component of the identity `s ≫ r = 0`.
      simpa using congrArg (fun m ↦ m.f (p + 1)) ((σ q).s_r)
    -- The `(p+1)`-component of `s ≫ r = 0` kills the section-retraction composite.
    simpa [Category.assoc] using
      congrArg
        (fun m ↦
          (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
            HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).X₃.d p (p + 1) ≫ m)
        hs_r_comp
  calc
    ((σ q).s).f p ≫
        (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
          HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).X₂.d p (p + 1) ≫
        ((σ q).r).f (p + 1) =
      (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
        HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).X₃.d p (p + 1) ≫
          ((σ q).s).f (p + 1) ≫ ((σ q).r).f (p + 1) := by
      simpa [Category.assoc] using congrArg (fun m ↦ m ≫ ((σ q).r).f (p + 1)) hs
    _ =
        (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
          HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) q)).X₃.d p (p + 1) ≫ 0 := hz
    _ = 0 := by
      exact
        (CategoryTheory.Limits.comp_zero
          (f := (S.X₃.d p (p + 1)).f q))

/-- Helper for Remark 12.18.6: the degree-`n` component of the owner connecting morphism on the
totalized short complex is the textbook composite `s'ⁿ ≫ d_Tot(B)ⁿ ≫ π'ⁿ⁺¹`. -/
private theorem totalized_homOfDegreewiseSplit_component (n : ℤ) :
    (CochainComplex.homOfDegreewiseSplit
        (totalizedShortComplex₂ S) (totalizedDegreewiseSplitting₂ S σ)).f n =
      totalizedDegreewiseSection₂ S σ n ≫
        ((totalizedShortComplex₂ S).X₂).d n (n + 1) ≫
        totalizedDegreewiseRetraction₂ S σ (n + 1) := by
  -- Read the component directly from the owner cochain-level connecting morphism formula.
  simpa [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cochain.mk_v,
    totalizedDegreewiseSplitting₂, totalizedDegreewiseSection₂, totalizedDegreewiseRetraction₂,
    totalizedShortComplex₂, Category.assoc] using
    (CochainComplex.homOfDegreewiseSplit_f
      (totalizedShortComplex₂ S) (totalizedDegreewiseSplitting₂ S σ) n)

-- Proof sketch: after expressing the second-direction connecting morphism via
-- `homOfDegreewiseSplit₂`, expand both sides on a summand `C^{p,q}`. The resulting component is
-- the usual `π^{p,q+1} ≫ d_2^{p,q} ≫ s^{p,q}` and the comparison with the shifted total complex is
-- the inverse of the canonical bidegree-shift comparison `S.X₁.totalShiftBidegreeIso 0 1`.
/-- Totalization preserves degreewise split short complexes in the second direction, and the
resulting connecting morphism matches the canonical connecting morphism of the totalized short
complex after the canonical shift-total comparison. -/
lemma totalized_degreewiseSplitConnectingHom₂_eq :
    total.map (homOfDegreewiseSplit₂ S σ) (up ℤ) ≫
        (S.X₁.totalShiftBidegreeIso 0 1).inv =
      CochainComplex.homOfDegreewiseSplit
        (totalizedShortComplex₂ S) (totalizedDegreewiseSplitting₂ S σ) :=
  -- Route correction: the source proof is to compare both morphisms on the summand
  -- `S.X₃.ιTotal ... p q`, discard the horizontal term via
  -- `second_direction_horizontal_term_vanishes`, and then match the remaining vertical term with
  -- `HomologicalComplex₂.ι_totalShiftBidegreeIso_hom_f` at `(a,b) = (0,1)`.
  -- That last bridge is still blocked upstream because `Remark_12_18_5` does not yet compile.
  -- TODO: expand both connecting morphisms on a summand `C^{p,q}`; the horizontal term should
  -- vanish because each `s^q` is a chain map and `π ∘ s = 0`, and the remaining vertical term
  -- should match through `HomologicalComplex₂.ι_totalShiftBidegreeIso_hom_f` at `(0,1)`.
  sorry

end DegreewiseSplit
