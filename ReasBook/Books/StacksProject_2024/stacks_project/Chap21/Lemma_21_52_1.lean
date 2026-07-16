import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_4
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_10
import StacksProject_2024.stacks_project.Chap13.Lemma_13_33_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_7
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Retract
import StacksProject_2024.stacks_project.Chap13.Definition_13_37_1
import StacksProject_2024.stacks_project.Chap13.Remark_13_35_5

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open DerivedCategory
open DerivedCategory.TStructure
open Opposite
open scoped ZeroObject

noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

section

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{v} A]
variable [IsGrothendieckAbelian.{w} A]

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 21.52.1:
- primary domain: compact objects in Grothendieck abelian categories and their bounded-complex
  representatives in the derived category, with generation data expressed through the canonical
  separator API for object properties;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `CategoryTheory.ObjectProperty.IsSeparating`,
  `CategoryTheory.ObjectProperty.isSeparating_iff_epi`,
  `CategoryTheory.ObjectProperty.coproductFrom`,
  `CategoryTheory.isCompactObject_iff`,
  `CategoryTheory.additiveClosure`,
  `CochainComplex.bounded`,
  `Compᵇ(A)`,
  `CategoryTheory.Retract`;
- best owner abstraction: the compactness owner `IsCompactObject`, applied both to the compact
  derived object `K` and to the generators in an object property `P`, together with the
  separating owner `ObjectProperty.IsSeparating` for that generating family, the chapter
  bounded-complex owner `Compᵇ(A)` for the representing cochain complex, and the direct-summand
  owner `Retract` for the bounded-complex conclusion;
- primitive-vs-derived split: the primitive source data are the separating property of the
  generating object property `P` and the compactness of each generator in `A`; the concrete
  epimorphic-coproduct presentation is derived from `ObjectProperty.isSeparating_iff_epi`, while
  the boundedness is carried by `Compᵇ(A)`, the termwise finite-coproduct condition is expressed
  by membership in `P.additiveClosure`, and the retract data are derived from the canonical owner
  `Retract`.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that every compact object of `D(A)` is a direct summand of
  an object represented by a bounded complex with terms finite direct sums of generators;
- `core/canonical`: `CategoryTheory.IsCompactObject`,
  `CategoryTheory.ObjectProperty.IsSeparating`, `Compᵇ(A)`,
  and `CategoryTheory.Retract`;
- `bridge/view`: the Chapter 13 owner `CategoryTheory.additiveClosure`, which records the
  finite-coproduct closure of the generator set up to isomorphism, together with the bounded
  representative `P : Compᵇ(A)` of the retract target `DerivedCategory.Q.obj P.obj`.
-/

-- Proof sketch: apply the Stacks argument using compactness of `K` to force bounded-above
-- truncation, resolve `K` by a bounded-above complex of coproducts of elements of `S`, factor the
-- identity through a bounded subcomplex, and then shrink the remaining infinite summands one
-- degree at a time until each term is a finite coproduct of elements of `S`. The resulting
-- bounded complex yields an object of `D(A)` admitting `K` as a retract.
/- Helper for Lemma 21.52.1: the object property of objects that are either zero or isomorphic to
some coproduct of members of `P`. The explicit `IsZero` summand supplies the `ContainsZero`
instance needed by the bounded-above replacement theorem. -/
private def zeroOrCoproductOfMembers (P : ObjectProperty A) : ObjectProperty A :=
  fun X ↦ IsZero X ∨
    ∃ (I : Type w) (F : I → A), (∀ i, P (F i)) ∧ Nonempty ((∐ F) ≅ X)

/- Helper for Lemma 21.52.1: the zero object belongs to `zeroOrCoproductOfMembers P`. -/
private instance zeroOrCoproductOfMembers_containsZero (P : ObjectProperty A) :
    (zeroOrCoproductOfMembers P).ContainsZero where
  exists_zero := by
    exact ⟨0, isZero_zero A, Or.inl (isZero_zero A)⟩

/- Helper for Lemma 21.52.1: choose a `Type w`-small colimit model of the canonical separator
cover `P.coproductFrom X`. This is the small-family form of
`ObjectProperty.isSeparating_iff_epi`, used here because Lemma `13.15.4` only needs some
`Type w`-small epimorphic coproduct cover of `X`. -/
private lemma exists_small_coproductFrom_epi
    (P : ObjectProperty A) (hgen : P.IsSeparating) (X : A) :
    ∃ (I : Type w) (F : I → A) (_ : ∀ i, P (F i)) (c : Cofan F) (_ : IsColimit c)
      (p : c.pt ⟶ X), Epi p := by
  -- TODO: use the mathlib `isSeparating_iff_epi` shrink argument once the file carries the
  -- needed smallness side condition `ObjectProperty.Small.{w} P`.
  sorry

/- Helper for Lemma 21.52.1: a set of generators admits `Type w`-small epimorphic coproduct
covers if every object is a quotient of a direct sum of members of the set. -/
class HasSmallCoproductEpiCover (S : Set A) : Prop where
  exists_epi (X : A) :
    ∃ (I : Type w) (F : I → A),
      (∀ i, F i ∈ S) ∧ ∃ (p : (∐ F) ⟶ X), Epi p

/- Helper for Lemma 21.52.1: an explicit `Type w`-small generating-set cover gives the
`HasEpiCover` instance needed by Lemma `13.15.4` for the zero-or-coproduct object property. -/
private lemma zeroOrCoproductOfMembers_hasEpiCover_of_generatingSet
    (S : Set A) (hcover : HasSmallCoproductEpiCover (A := A) S) :
    ObjectProperty.HasEpiCover (zeroOrCoproductOfMembers (fun Y : A ↦ Y ∈ S)) := by
  refine ⟨?_⟩
  intro X
  -- The chosen generating-set cover already lands in the coproduct branch of the object
  -- property, so it can be used directly as an epi cover.
  obtain ⟨I, F, hF, p, hp⟩ := hcover.exists_epi X
  refine ⟨∐ F, Or.inr ⟨I, F, hF, ⟨Iso.refl _⟩⟩, p, hp⟩

/- Helper for Lemma 21.52.1: once the needed `HasEpiCover` instance is available, Lemma
`13.15.4` replaces a bounded-above derived object by a bounded-above complex whose terms are zero
or coproducts of members of `P`. -/
private lemma exists_zeroOrCoproduct_representative_of_hasEpiCover
    (P : ObjectProperty A) [ObjectProperty.HasEpiCover (zeroOrCoproductOfMembers P)]
    {K : DerivedCategory A} {b : ℤ} (hK : K.IsLE b) :
    ∃ L : CochainComplex A ℤ,
      ∃ e : DerivedCategory.Q.obj L ≅ K,
        L.IsStrictlyLE b ∧ ∀ i : ℤ, zeroOrCoproductOfMembers P (L.X i) := by
  -- Choose a bounded-above representative of `K`, then replace it termwise using Lemma
  -- `13.15.4`.
  obtain ⟨K', hK', ⟨eK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE K b
  obtain ⟨L, α, hα⟩ :=
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE
      (zeroOrCoproductOfMembers P) b K' hK'
  letI : QuasiIso α := hα.quasiIso
  refine ⟨L, asIso (DerivedCategory.Q.map α) ≪≫ eK.symm, hα.strictlyLE, ?_⟩
  intro i
  exact hα.term_mem i

/- Helper for Lemma 21.52.1: once a compact derived object is known to be bounded above, Lemma
`13.15.4` replaces a chosen representative by a bounded-above complex whose terms are zero or
coproducts of members of `P`. -/
private lemma exists_zeroOrCoproduct_representative
    (P : ObjectProperty A) {K : DerivedCategory A} {b : ℤ} (hK : K.IsLE b)
    (hgen : P.IsSeparating) :
    ∃ L : CochainComplex A ℤ,
      ∃ e : DerivedCategory.Q.obj L ≅ K,
        L.IsStrictlyLE b ∧ ∀ i : ℤ, zeroOrCoproductOfMembers P (L.X i) := by
  let hcover : ObjectProperty.HasEpiCover (zeroOrCoproductOfMembers P) := by
    refine ⟨?_⟩
    intro X
    obtain ⟨I, F, hF, c, hc, p, hp⟩ := exists_small_coproductFrom_epi P hgen X
    refine ⟨c.pt, ?_, p, hp⟩
    exact Or.inr ⟨I, F, hF, ⟨colimit.isoColimitCocone ⟨c, hc⟩⟩⟩
  letI : ObjectProperty.HasEpiCover (zeroOrCoproductOfMembers P) := hcover
  -- Route correction: the actual replacement argument only needs `HasEpiCover`; the arbitrary
  -- separating-family route is blocked solely by the missing smallness bridge above.
  exact exists_zeroOrCoproduct_representative_of_hasEpiCover P hK

/- Helper for Lemma 21.52.1: the represented functor `Hom(K,-)` sends the truncation morphism
`K ⟶ τ_{\ge n} K` to postcomposition by that same morphism. This fixes the direction of the
compactness transport needed later. -/
omit [HasCoproducts.{v} A] [IsGrothendieckAbelian.{w} A] in
private lemma truncGEπ_coyoneda_map_apply
    (K X : DerivedCategory A) (n : ℤ) (f : X ⟶ K) :
    ((preadditiveCoyoneda.obj (op X)).map ((t.truncGEπ n).app K)) f =
      f ≫ ((t.truncGEπ n).app K) :=
  rfl

/- Helper for Lemma 21.52.1: evaluating the previous transport on `𝟙_K` recovers the truncation
map itself, so the eventual-vanishing goal is exactly a finite-support statement for the image of
`𝟙_K`. -/
private lemma truncGEπ_coyoneda_map_id
    (K : DerivedCategory A) (n : ℤ) :
    ((preadditiveCoyoneda.obj (op K)).map ((t.truncGEπ n).app K))
        (𝟙 K) =
      ((t.truncGEπ n).app K) := by
  -- Evaluating the represented functor on the identity simply returns the truncation morphism.
  simpa using truncGEπ_coyoneda_map_apply K K n (𝟙 K)

/- Helper for Lemma 21.52.1: once the image of `𝟙_K` under a truncation map vanishes in the
represented functor `Hom(K, -)`, the truncation morphism itself is zero. This is the final
direction-fixing bridge after the finite-support compactness step. -/
private lemma truncGEπ_eq_zero_of_coyoneda_map_id_eq_zero
    (K : DerivedCategory A) (n : ℕ)
    (hzero :
      ((preadditiveCoyoneda.obj (op K)).map
          ((t.truncGEπ (n : ℤ)).app K)) (𝟙 K) =
        0) :
    ((t.truncGEπ (n : ℤ)).app K) = 0 := by
  -- The represented image of `𝟙_K` is exactly the truncation map itself.
  rw [truncGEπ_coyoneda_map_id] at hzero
  simpa using hzero

/- Helper for Lemma 21.52.1: an eventual-zero statement for the images of `𝟙_K` under the
represented truncation maps immediately upgrades to eventual vanishing of the truncation maps
themselves. -/
private lemma truncGE_maps_eventually_zero_of_coyoneda_id_eventually_zero
    (K : DerivedCategory A) {N : ℕ}
    (hzero :
      ∀ n : ℕ, N ≤ n →
        ((preadditiveCoyoneda.obj (op K)).map
            ((t.truncGEπ (n : ℤ)).app K)) (𝟙 K) =
          0) :
    ∀ n : ℕ, N ≤ n → ((t.truncGEπ (n : ℤ)).app K) = 0 := by
  intro n hn
  exact truncGEπ_eq_zero_of_coyoneda_map_id_eq_zero K n (hzero n hn)

/- Helper for Lemma 21.52.1: an element of an additive group determines the unique morphism from
`ULift ℤ` sending `1` to that element. This is the concrete source object used to package
finite-support statements as factorization problems. -/
private noncomputable def addCommGrpHomOfElement {B : AddCommGrpCat.{v}} (x : B) :
    AddCommGrpCat.of (ULift.{v} ℤ) ⟶ B :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun n : ULift.{v} ℤ ↦ n.down • x)
      (fun m n ↦ add_zsmul x m.down n.down)

/- Helper for Lemma 21.52.1: the concrete morphism attached to an element sends `1` back to the
chosen element. -/
private lemma addCommGrpHomOfElement_apply_one {B : AddCommGrpCat.{v}} (x : B) :
    addCommGrpHomOfElement x (ULift.up 1) = x := by
  -- The `ULift ℤ`-generator `1` is sent to the original element by construction.
  simp [addCommGrpHomOfElement]

/- Helper for Lemma 21.52.1: a morphism out of `ULift ℤ` is determined by the image of `1`. -/
private lemma addCommGrp_hom_ext_of_apply_one {B : AddCommGrpCat.{v}}
    {f g : AddCommGrpCat.of (ULift.{v} ℤ) ⟶ B}
    (h : f (ULift.up 1) = g (ULift.up 1)) :
    f = g := by
  -- Every morphism out of `ULift ℤ` is determined by the image of the generator `1`.
  ext n
  cases' n with z
  have hz : (ULift.up z : ULift.{v} ℤ) = z • ULift.up 1 := by
    change ULift.up z = ULift.up (z * 1)
    simp
  calc
    f (ULift.up z) = f (z • ULift.up 1) := by rw [hz]
    _ = z • f (ULift.up 1) := by
      simpa using (map_zsmul (ConcreteCategory.hom f) z (ULift.up 1))
    _ = z • g (ULift.up 1) := by rw [h]
    _ = g (z • ULift.up 1) := by
      simpa using (map_zsmul (ConcreteCategory.hom g) z (ULift.up 1)).symm
    _ = g (ULift.up z) := by rw [hz]

/- Helper for Lemma 21.52.1: once a finite prefix stops before the `n`th summand, its canonical
map to the countable coproduct has zero `n`th projection. This is the direct-sum support
calculation used in the compactness step. -/
private lemma finite_prefix_to_sigma_comp_sigma_π_eq_zero_of_le
    (K : ℕ ⥤ AddCommGrpCat.{v}) {m n : ℕ} (hmn : m ≤ n) :
    finite_prefix_to_sigma K m ≫ Limits.Sigma.π K.obj n = 0 := by
  -- Induct on the prefix length and check the last summand separately.
  induction m generalizing n with
  | zero =>
      have h0 : IsZero (finite_prefix_obj K 0) := by
        simpa [finite_prefix_obj] using (isZero_zero AddCommGrpCat.{v})
      exact h0.eq_of_src _ _
  | succ m ih =>
      apply biprod.hom_ext'
      · calc
          biprod.inl ≫ finite_prefix_to_sigma K (m + 1) ≫ Limits.Sigma.π K.obj n =
              finite_prefix_to_sigma K m ≫ Limits.Sigma.π K.obj n := by
                simp [finite_prefix_to_sigma]
          _ = 0 := ih (Nat.le_trans (Nat.le_succ m) hmn)
      · calc
          biprod.inr ≫ finite_prefix_to_sigma K (m + 1) ≫ Limits.Sigma.π K.obj n =
              Sigma.ι K.obj m ≫ Limits.Sigma.π K.obj n := by
                rw [finite_prefix_to_sigma, biprod.inr_desc_assoc]
          _ = 0 := by
                simpa using Limits.Sigma.ι_π_of_ne K.obj (by omega : m ≠ n)

/- Helper for Lemma 21.52.1: if the represented element factors through a finite prefix, then all
tail projections of that element vanish. This isolates the pure finite-support computation from
the later truncation transport. -/
private lemma finite_prefix_factorization_implies_element_tail_zero
    (K : ℕ ⥤ AddCommGrpCat.{v}) {x : (∐ K.obj : AddCommGrpCat.{v})} {M : ℕ}
    {β : AddCommGrpCat.of (ULift.{v} ℤ) ⟶ finite_prefix_obj K (M + 1)}
    (hfactor :
      addCommGrpHomOfElement x = β ≫ finite_prefix_to_sigma K (M + 1)) :
    ∀ n : ℕ, M + 1 ≤ n → Limits.Sigma.π K.obj n x = 0 := by
  intro n hn
  -- Evaluate the factorization at `1`, then project to the `n`th summand.
  have hx :
      x = (β ≫ finite_prefix_to_sigma K (M + 1)) (ULift.up 1) := by
    have happly := congrArg (fun f ↦ f (ULift.up 1)) hfactor
    simpa [addCommGrpHomOfElement] using happly
  rw [hx]
  -- The projection kills every summand beyond the finite prefix.
  change (β ≫ finite_prefix_to_sigma K (M + 1) ≫ Limits.Sigma.π K.obj n) (ULift.up 1) = 0
  rw [finite_prefix_to_sigma_comp_sigma_π_eq_zero_of_le K hn]
  simp

/- Helper for Lemma 21.52.1: the source truncation argument should show that compact objects of
`D(A)` are bounded above for the canonical `t`-structure. -/
private lemma compact_truncGE_maps_eventually_zero
    (K : DerivedCategory A) (hK : IsCompactObject K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ((t.truncGEπ (n : ℤ)).app K) = 0 := by
  sorry

/- Helper for Lemma 21.52.1: if the upper truncation map in degree `n` is zero, then the
degree-`n` cohomology of `K` already vanishes. -/
private lemma isZero_homology_of_truncGEπ_eq_zero
    (K : DerivedCategory A) (n : ℤ)
    (hπ : ((t.truncGEπ n).app K) = 0) :
    IsZero ((DerivedCategory.homologyFunctor A n).obj K) := by
  -- The induced homology map is an isomorphism, so if it vanishes then the source homology
  -- object has zero identity.
  let H := DerivedCategory.homologyFunctor A n
  let f := H.map ((t.truncGEπ n).app K)
  letI : IsIso f := by
    simpa [f] using isIso_homologyMap_truncGEπ K n
  have hf : f = 0 := by
    calc
      f = H.map ((t.truncGEπ n).app K) := rfl
      _ = H.map 0 := by rw [hπ]
      _ = 0 := by exact Functor.map_zero H K ((t.truncGE n).obj K)
  haveI : Mono f := by infer_instance
  haveI : Mono (0 : H.obj K ⟶ H.obj ((t.truncGE n).obj K)) := by
    simpa [hf] using (inferInstance : Mono f)
  exact IsZero.of_mono_zero (H.obj K) (H.obj ((t.truncGE n).obj K))

/- Helper for Lemma 21.52.1: eventual vanishing of the canonical upper truncation maps forces
`K` to lie in `D^-(A)`. -/
private lemma isLE_of_truncGE_maps_eventually_zero
    (K : DerivedCategory A) {N : ℕ}
    (hzero :
      ∀ n : ℕ, N ≤ n → ((t.truncGEπ (n : ℤ)).app K) = 0) :
    K.IsLE ((N : ℤ) - 1) := by
  -- Rewrite `IsLE` into high-degree homology vanishing and use the previous homology lemma.
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hi0 : 0 ≤ i := by omega
  have hNi : N ≤ Int.toNat i := by omega
  have hi_eq : ((Int.toNat i : ℕ) : ℤ) = i := by
    simpa using Int.toNat_of_nonneg hi0
  have hπ : ((t.truncGEπ i).app K) = 0 := by
    rw [← hi_eq]
    exact hzero (Int.toNat i) hNi
  exact isZero_homology_of_truncGEπ_eq_zero K i hπ

/- Helper for Lemma 21.52.1: the source truncation argument should show that compact objects of
`D(A)` are bounded above for the canonical `t`-structure. -/
private lemma compact_isLE_of_truncation_finite_support
    (K : DerivedCategory A) (hK : IsCompactObject K) :
    ∃ b : ℤ, K.IsLE b := by
  -- Route correction: isolate the finite-support compactness step as its own lemma, and keep the
  -- rest of the source argument on the canonical `H^n`-vanishing route.
  obtain ⟨N, hN⟩ := compact_truncGE_maps_eventually_zero K hK
  exact ⟨(N : ℤ) - 1, isLE_of_truncGE_maps_eventually_zero K hN⟩

/- Helper for Lemma 21.52.1: after choosing a bounded-above representative by coproducts of
members of `S`, the remaining source-faithful work is to factor `𝟙_K` through a bounded stupid
truncation and then shrink the surviving coproduct terms degree by degree to finite coproducts. -/
private lemma retract_of_zeroOrCoproduct_representative
    (P : ObjectProperty A) {K : DerivedCategory A} (hK : IsCompactObject K)
    (hsmall : ∀ E : A, P E → IsCompactObject E)
    {b : ℤ} {L : CochainComplex A ℤ} (e : DerivedCategory.Q.obj L ≅ K)
    (hL : L.IsStrictlyLE b)
    (hterm : ∀ i : ℤ, zeroOrCoproductOfMembers P (L.X i)) :
    ∃ B : Compᵇ(A),
      (∀ i : ℤ, P.additiveClosure (B.obj.X i)) ∧
        Nonempty (Retract K (DerivedCategory.Q.obj B.obj)) := by
  -- TODO: implement the bounded stupid-truncation factorization and the degreewise shrinking
  -- argument from the source proof, then package the final bounded complex as an object of `Compᵇ`.
  sorry

/-- Canonical object-property form of Lemma 21.52.1. A compact object of `D(A)` is a retract of
an object represented by a bounded complex whose terms lie in the additive closure of a
separating compact family `P`. -/
theorem compactObject_isRetract_of_finiteCoproductComplex_of_separatingFamily
    (P : ObjectProperty A) {K : DerivedCategory A} (hK : IsCompactObject K)
    (hgen : P.IsSeparating) (hsmall : ∀ E : A, P E → IsCompactObject E) :
    ∃ B : Compᵇ(A),
      (∀ i : ℤ, P.additiveClosure (B.obj.X i)) ∧
        Nonempty (Retract K (DerivedCategory.Q.obj B.obj)) := by
  -- First recover the bounded-above part of the source argument from compactness.
  obtain ⟨b, hKb⟩ := compact_isLE_of_truncation_finite_support K hK
  -- Then replace `K` by a bounded-above representative whose terms are coproducts of generators.
  obtain ⟨L, e, hL, hterm⟩ :=
    exists_zeroOrCoproduct_representative P hKb hgen
  -- The remaining source-faithful step is the bounded-truncation and shrinking argument.
  exact retract_of_zeroOrCoproduct_representative P hK hsmall e hL hterm

/-- Lemma 21.52.1: if `A` is a Grothendieck abelian category and `S` is a set of objects such
that every object of `A` is a quotient of a direct sum of elements of `S`, while every
`E ∈ S` has `Hom(E, -)` commuting with direct sums, then every compact object of `D(A)` is a
direct summand of an object represented by a bounded complex whose terms are finite direct sums
of elements of `S`. -/
@[stacks 094B]
theorem compactObject_isRetract_of_finiteCoproductComplex_of_generatingSet
    (S : Set A) {K : DerivedCategory A} (hK : IsCompactObject K)
    (hcover : HasSmallCoproductEpiCover (A := A) S)
    (hsmall : ∀ E : A, E ∈ S → IsCompactObject E) :
    ∃ B : Compᵇ(A),
      (∀ i : ℤ, (additiveClosure fun Y : A ↦ Y ∈ S) (B.obj.X i)) ∧
        Nonempty (Retract K (DerivedCategory.Q.obj B.obj)) := by
  let P : ObjectProperty A := fun Y ↦ Y ∈ S
  -- Route correction: bypass the arbitrary `P.IsSeparating` bridge here and use the explicit
  -- generating-set cover directly, since that is exactly the data needed to build
  -- `HasEpiCover (zeroOrCoproductOfMembers P)`.
  obtain ⟨b, hKb⟩ := compact_isLE_of_truncation_finite_support K hK
  let hcoverP : ObjectProperty.HasEpiCover (zeroOrCoproductOfMembers P) :=
    zeroOrCoproductOfMembers_hasEpiCover_of_generatingSet S hcover
  letI : ObjectProperty.HasEpiCover (zeroOrCoproductOfMembers P) := hcoverP
  obtain ⟨L, e, hL, hterm⟩ :=
    exists_zeroOrCoproduct_representative_of_hasEpiCover P hKb
  simpa [P] using
    retract_of_zeroOrCoproduct_representative P hK hsmall e hL hterm

end

end CategoryTheory.IsGrothendieckAbelian
