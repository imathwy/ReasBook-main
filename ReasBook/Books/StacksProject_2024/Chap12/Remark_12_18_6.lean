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
  sorry

/-- Remark 12.18.6: if two morphisms of double complexes are homotopic when the double complexes
are viewed as complexes in the second index, then the induced morphisms of associated total
complexes are connected by a canonical homotopy. -/
noncomputable def totalHomotopyOfHomotopy
    (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map φ) ((flipFunctor C (up ℤ) (up ℤ)).map ψ)) :
    Homotopy (total.map φ (up ℤ)) (total.map ψ (up ℤ)) where
  hom i j :=
    if hij : (up ℤ).Rel j i then
      K.totalDesc fun p q hpq ↦
        p.negOnePow •
          (((h.hom q (q - 1)).f p) ≫
            L.ιTotal (up ℤ) p (q - 1) j (by
              dsimp at hpq hij ⊢
              lia))
    else
      0
  zero i j hij := by
    dsimp
    split_ifs with hrel
    · exact (hij hrel).elim
    · rfl
  comm i := by
    sorry

/-- Remark 12.18.6: if two morphisms of double complexes are homotopic when the double complexes
are viewed as complexes in the second index, then the induced morphisms of associated total
complexes are homotopic. -/
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

-- Proof sketch: both sides encode the same degree `-1` cochain on the total complexes. Expanding
-- `cochainComplex_self_homotopy_equiv_hom_to_shift` and `totalHomotopyOfHomotopy`, the component
-- on the summand indexed by `(p, q)` is the signed second-direction homotopy component
-- `(-1)^p h.hom q (q - 1)).f p`, and the comparison with the shifted total complex is the
-- inverse of the canonical bidegree-shift comparison `L.totalShiftBidegreeIso 0 (-1)`.
/-- Remark 12.18.6: for a self-homotopy in the second direction, the morphism
`Tot(K) ⟶ Tot(L)[-1]` corresponding to the induced total homotopy via Lemma 12.14.9 agrees with
the totalization of the associated morphism `K ⟶ L[0,-1]`, followed by the inverse of the
canonical bidegree-shift comparison `L.totalShiftBidegreeIso 0 (-1)`. -/
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

-- Proof sketch: precompose with each summand inclusion `S.X₂.ιTotal (up ℤ) p q n h` and use the
-- identity `((σ q).f_r).f p` in bidegree `(p,q)`.
/-- The induced totalized retraction is a retraction of the first map in degree `n`. -/
lemma totalizedDegreewiseRetraction_f_r₂ (n : ℤ) :
    ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).f ≫
      totalizedDegreewiseRetraction₂ S σ n = 𝟙 _ :=
  sorry

-- Proof sketch: precompose with each summand inclusion `S.X₃.ιTotal (up ℤ) p q n h` and use the
-- identity `((σ q).s_g).f p` in bidegree `(p,q)`.
/-- The induced totalized section is a section of the second map in degree `n`. -/
lemma totalizedDegreewiseSection_s_g₂ (n : ℤ) :
    totalizedDegreewiseSection₂ S σ n ≫
      ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).g = 𝟙 _ :=
  sorry

-- Proof sketch: verify the identity after precomposing with each summand inclusion and apply the
-- splitting identity `((σ q).id).f p` componentwise in bidegree `(p,q)`.
/-- The totalized retractions and sections satisfy the splitting identity in every total degree. -/
lemma totalizedDegreewiseSplitting_id₂ (n : ℤ) :
    totalizedDegreewiseRetraction₂ S σ n ≫
        ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).f +
      ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).g ≫
        totalizedDegreewiseSection₂ S σ n =
      𝟙 _ :=
  sorry

/-- The degreewise splitting on the totalized short complex induced by the flipped degreewise
splittings of a short complex of bicomplexes. -/
noncomputable def totalizedDegreewiseSplitting₂ (n : ℤ) :
    ((totalizedShortComplex₂ S).map (HomologicalComplex.eval C (up ℤ) n)).Splitting where
  r := totalizedDegreewiseRetraction₂ S σ n
  s := totalizedDegreewiseSection₂ S σ n
  f_r := totalizedDegreewiseRetraction_f_r₂ S σ n
  s_g := totalizedDegreewiseSection_s_g₂ S σ n
  id := totalizedDegreewiseSplitting_id₂ S σ n

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
  sorry

end DegreewiseSplit
