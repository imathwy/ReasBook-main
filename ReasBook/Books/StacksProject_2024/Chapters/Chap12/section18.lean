import Mathlib
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.BifunctorAssociator
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.TotalComplexShift
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_18_1 (from Chap12) -/
open CategoryTheory ComplexShape
open HomologicalComplex₂

universe v u

section

variable {V : Type u} [Category.{v} V] [Limits.HasZeroMorphisms V]

/- Definition 12.18.1 is a core/canonical recall item in the bicomplex domain. In the source's
additive setting, the owner abstraction is already the mathlib bicomplex type
`HomologicalComplex₂ V (up ℤ) (up ℤ)`, and it only needs zero morphisms. Its primitive data are
the objects `(K.X p).X q` with horizontal differentials `(K.d p (p + 1)).f q` and vertical
differentials `(K.X p).d q (q + 1)`. The square-zero and commutation relations are derived owner
API, recalled below. -/
#check (HomologicalComplex₂ V (up ℤ) (up ℤ))

/- Companion recall: the horizontal differential squares to zero by the owner lemma
`HomologicalComplex₂.d_f_comp_d_f`. -/
recall d_f_comp_d_f

/- Companion recall: for each fixed horizontal degree `p`, the vertical differential squares to
zero in the column complex `K.X p` by `HomologicalComplex.d_comp_d`. -/
recall HomologicalComplex.d_comp_d

/- Companion recall: the horizontal and vertical differentials commute on each elementary square
by the owner lemma `HomologicalComplex₂.d_comm`. -/
recall d_comm

end

/-! ### Example_12_18_2 (from Chap12) -/
open CategoryTheory Limits ComplexShape

universe v₁ v₂ v₃ u₁ u₂ u₃

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms C]
variable (tensor : A ⥤ B ⥤ C) [tensor.PreservesZeroMorphisms]
  [∀ X, (tensor.obj X).PreservesZeroMorphisms]
variable (X : CochainComplex A ℤ) (Y : CochainComplex B ℤ)

/- Domain-style sampling for Example 12.18.2:
- primary domain: bicomplexes produced by applying a bifunctor to cochain complexes;
- sampled core/canonical declarations:
  `Functor.mapBifunctorHomologicalComplex`,
  `Functor.mapBifunctorHomologicalComplex_obj_obj_X_X`,
  `Functor.mapBifunctorHomologicalComplex_obj_obj_d_f`,
  `Functor.mapBifunctorHomologicalComplex_obj_obj_X_d`;
- best owner abstraction: `Functor.mapBifunctorHomologicalComplex`;
- primitive data: the bifunctor `tensor : A ⥤ B ⥤ C`, its zero-morphism preservation in each
  variable, and the input cochain complexes `X` and `Y`;
- derived API: the resulting bicomplex and its `(p, q)`-terms together with the horizontal and
  vertical differentials;
- source/core/bridge triage:
  `source-facing`: the textbook bicomplex obtained from applying `tensor` degreewise to
    `X` and `Y`;
  `core/canonical`: `tensor.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)`;
  `bridge/view`: the componentwise computation rules recalled below.

No local wrapper should be introduced here: the source-facing bicomplex is already the direct
evaluation of the canonical owner bifunctor on `X` and `Y`. -/
/-
Example 12.18.2 is source-facing in the bicomplex domain: the textbook additive bifunctor
`\otimes : \mathcal A × \mathcal B ⥤ \mathcal C` is recalled through the owner bifunctor
`tensor.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)`, whose canonical API only needs
zero-morphism preservation in each variable.
-/
recall Functor.mapBifunctorHomologicalComplex

/- Evaluating that owner bifunctor at cochain complexes `X^\bullet` and `Y^\bullet` gives the
canonical bicomplex `((tensor.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj X).obj Y`. -/
#check ((tensor.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj X).obj Y

/- Companion recall: the `(p, q)`-term of this bicomplex is `(tensor.obj (X.X p)).obj (Y.X q)`. -/
recall Functor.mapBifunctorHomologicalComplex_obj_obj_X_X

/- Companion recall: the horizontal differential is induced by the differential of `X`. -/
recall Functor.mapBifunctorHomologicalComplex_obj_obj_d_f

/- Companion recall: the vertical differential is induced by the differential of `Y`. -/
recall Functor.mapBifunctorHomologicalComplex_obj_obj_X_d

end

/-! ### Definition_12_18_3 (from Chap12) -/
open CategoryTheory ComplexShape

namespace HomologicalComplex₂

scoped[HomologicalComplex₂] notation:max "Tot(" K ")" => HomologicalComplex₂.total K (up ℤ)

end HomologicalComplex₂

open scoped HomologicalComplex₂

section

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (A : HomologicalComplex₂ C (up ℤ) (up ℤ)) [A.HasTotal (up ℤ)]

/- Domain-style sampling for Definition 12.18.3:
- primary domain: total complexes of cohomological double complexes;
- sampled owner declarations:
  `HomologicalComplex₂.HasTotal`,
  `HomologicalComplex₂.total`,
  `HomologicalComplex₂.total_d`,
  `HomologicalComplex₂.totalFunctor`;
- source/core/bridge triage:
  `source-facing`: the simple complex `sA^• = Tot(A^{•, •})` attached to a cohomological double
    complex;
  `core/canonical`: `HomologicalComplex₂.total`;
  `bridge/view`: the differential formula `HomologicalComplex₂.total_d`.

Primitive data are the bicomplex objects and horizontal/vertical differentials already packaged by
`HomologicalComplex₂`. The existence predicate `HomologicalComplex₂.HasTotal` and the total
complex `HomologicalComplex₂.total` are derived owner API, so this file should recall those
canonical declarations directly rather than introduce a chapter-local `simpleComplex` alias or
wrapper.
-/

/- Companion recall: the finiteness/existence predicate needed to form the total complex of a
double complex is the canonical owner `HomologicalComplex₂.HasTotal`. -/
recall HomologicalComplex₂.HasTotal

/- Source-facing notation: in Chapter 12, the simple complex attached to a cohomological
bicomplex `A` is written `Tot(A)`. -/
#check Tot(A)

/- Definition 12.18.3: for a cohomological double complex `A`, the associated simple complex
`sA^• = Tot(A^{•, •})` is the canonical owner construction `HomologicalComplex₂.total`,
specialized in the Stacks setting to total degree shape `up ℤ`. -/
recall HomologicalComplex₂.total

/- Companion recall: the differential on the total complex is the canonical sum of the horizontal
and signed vertical parts, recorded by the owner lemma `HomologicalComplex₂.total_d`. -/
recall HomologicalComplex₂.total_d

end

/-! ### Remark_12_18_4 (from Chap12) -/
open ComplexShape

/- Domain-style sampling for Remark 12.18.4:
- primary domain: associativity of totalization for triple cochain complexes;
- sampled core/canonical declarations:
  `ComplexShape.Associative`,
  `HomologicalComplex.mapBifunctorAssociator`,
  `GradedObject.mapBifunctorAssociator`;
- best owner abstraction: the pair consisting of the shape-level associativity datum
  `ComplexShape.Associative` and the induced homological-complex isomorphism
  `HomologicalComplex.mapBifunctorAssociator`;
- primitive data: three cochain-complex shapes, the two intermediate total-complex shapes, the
  final total shape, and the canonical associativity witness between the two ways of summing the
  three indices;
- derived API: the resulting canonical `≅` between the two iterated totalizations, obtained from
  the upstream bifunctor-associator construction rather than from any local wrapper;
- source/core/bridge triage:
  `source-facing`: the textbook remark that the two iterated totalizations of a triple cochain
    complex are canonically isomorphic;
  `core/canonical`: `ComplexShape.Associative` and
    `HomologicalComplex.mapBifunctorAssociator`;
  `bridge/view`: the graded precursor `GradedObject.mapBifunctorAssociator`.

This file should therefore stay at direct canonical recall/use, not introduce a parallel local
`IsIsomorphic` API around the upstream isomorphism. -/
recall ComplexShape.Associative

/- For cochain complexes, the needed associativity datum is the canonical `add_assoc`-based
instance already provided by mathlib. -/
#check (inferInstance : ComplexShape.Associative (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ))

/- The owner `≅`-level construction for associativity of totalized homological-complex
constructions is `HomologicalComplex.mapBifunctorAssociator`; Remark 12.18.4 is the
triple-totalization specialization of this upstream API. -/
recall HomologicalComplex.mapBifunctorAssociator

/-! ### Remark_12_18_5 (from Chap12) -/
open CategoryTheory Category ComplexShape Limits
open HomologicalComplex₂
open scoped HomologicalComplex₂

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
variable (a b : ℤ) [K.HasTotal (up ℤ)]

/- Domain-style sampling for Remark 12.18.5:
- primary domain: compatibility of totalization with bidegree shifts of a cohomological
  bicomplex;
- sampled owner declarations:
  `HomologicalComplex₂.totalShift₁Iso`,
  `HomologicalComplex₂.totalShift₂Iso`,
  `HomologicalComplex₂.shiftFunctor₁₂CommIso`,
  `HomologicalComplex₂.totalShift₁Iso_trans_totalShift₂Iso`;
- best owner abstraction:
  `source-facing`: the bidegree-shifted bicomplex `K[a, b]`,
  `core/canonical`: mathlib's `shiftFunctor₁`, `shiftFunctor₂`, and their total-shift
    comparison isomorphisms,
  `bridge/view`: the totalization comparison `K.totalShiftBidegreeIso a b`;
- primitive data: the bicomplex `K`;
- derived API: the notation `K[a, b]` for the bicomplex shifted in bidegree `(a, b)` and the
  specific bridge/view comparison from `Tot(K)⟦a + b⟧` to `Tot(K[a, b])`.

This file should therefore expose the source-facing bidegree shift itself as a thin abbreviation
over the canonical shift functors, and state the totalization comparison using that notation. -/
#check HomologicalComplex₂.totalShift₁Iso_trans_totalShift₂Iso

namespace HomologicalComplex₂

/-- The bicomplex obtained from `K` by shifting bidegrees by `(a, b)`. -/
abbrev bidegreeShift (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (a b : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (shiftFunctor₁ C a).obj ((shiftFunctor₂ C b).obj K)

scoped[HomologicalComplex₂] notation:max K:max "[" a ", " b "]" =>
  HomologicalComplex₂.bidegreeShift K a b

open scoped HomologicalComplex₂

/-- The bridge/view comparison from the total complex shifted by `a + b` to the total complex of
the bidegree-shifted bicomplex `K[a, b]`. -/
noncomputable def totalShiftBidegreeIso :
    Tot(K)⟦a + b⟧ ≅ Tot(K[a, b]) :=
  show Tot(K)⟦a + b⟧ ≅ Tot((shiftFunctor₁ C a).obj ((shiftFunctor₂ C b).obj K)) from
    ((((shiftFunctor₂ C b).obj K).totalShift₁Iso a) ≪≫
        (shiftFunctor _ a).mapIso (K.totalShift₂Iso b) ≪≫
        ((shiftFunctorAdd' _ b a (a + b) (add_comm b a)).app (Tot(K))).symm).symm

-- Proof sketch: expand `K.totalShiftBidegreeIso a b` and apply the owner component formulas
-- `ι_totalShift₁Iso_inv_f` and `ι_totalShift₂Iso_inv_f`. The only nontrivial sign comes from
-- `totalShift₂Iso`, giving `(-1)^(p b)`.
/-- On the summand indexed by `(p, q)`, the canonical bidegree-shift comparison
`K.totalShiftBidegreeIso a b` acts by the sign `(-1)^(p b)` and sends it to the shifted summand
`(p - a, q - b)`. -/
@[reassoc]
theorem ι_totalShiftBidegreeIso_hom_f
    (n p q : ℤ) (h : p + q = n + (a + b)) :
    K.ιTotal (up ℤ) p q (n + (a + b)) h ≫
        (CochainComplex.shiftFunctorObjXIso (Tot(K)) (a + b)
          n (n + (a + b)) rfl).inv ≫
        (K.totalShiftBidegreeIso a b).hom.f n =
      (p * b).negOnePow •
        ((K.shiftFunctor₂XXIso p (q - b) b q (Int.sub_add_cancel q b).symm).inv ≫
          (((shiftFunctor₂ C b).obj K).shiftFunctor₁XXIso (p - a) a p
            (Int.sub_add_cancel p a).symm (q - b)).inv ≫
            ((K[a, b]).ιTotal
              (up ℤ) (p - a) (q - b) n (by
                dsimp [π] at h ⊢
                linarith))) := sorry

end HomologicalComplex₂

/-! ### Remark_12_18_6 (from Chap12) -/
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

/-! ### Remark_12_18_7 (from Chap12) -/
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
