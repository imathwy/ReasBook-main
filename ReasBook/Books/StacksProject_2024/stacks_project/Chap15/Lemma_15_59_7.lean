import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap12.Lemma_12_25_1
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap15.Lemma_15_59_6
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RingTheory.Flat.CategoryTheory

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

namespace CochainComplex

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped HomologicalComplex₂

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling:
- primary domain: K-flat cochain complexes of `R`-modules and the bounded-above flat criterion;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.minus`,
  `CochainComplex.minus_iff`;
- best owner abstraction: the chapter owner predicate is `P.IsKFlat` on the complex `P` itself,
  with boundedness expressed by the existing owner predicate
  `CochainComplex.minus (ModuleCat R) P` rather than by a repeated existential spelling, and with
  termwise flatness as a separate hypothesis;
- primitive data: the complex `P`, the bounded-above hypothesis
  `hbounded : CochainComplex.minus (ModuleCat R) P`, and the termwise flatness hypothesis
  `hFlat : P.IsTermwiseFlat`;
- derived API: the K-flatness conclusion `P.IsKFlat`.

Source/core/bridge triage:
- `source-facing`: the bounded-above flat criterion from the source text;
- `core/canonical`: `CochainComplex.IsKFlat` and `CochainComplex.IsTermwiseFlat`;
- `bridge/view`: `CochainComplex.isKFlat_iff`, the owner eliminator expressing K-flatness by
  preservation of acyclicity under totalized tensoring.

The theorem is already an owner-level source-facing statement, so the refine pass should keep that
statement and move only its surface to the canonical owner-style spelling.
-/

/-- Helper for Lemma 15.59.7: tensoring an acyclic cochain complex on the right by a flat module
preserves acyclicity. -/
private theorem mapHomologicalComplex_acyclic_of_tensorRight_flat
    (L : CochainComplex (ModuleCat R) ℤ) (hL : L.Acyclic) (M : ModuleCat R)
    (hM : Module.Flat R M) :
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).Acyclic := by
  -- Put flatness into the local instance context so the exact-functor interface can be reused.
  letI : Module.Flat R M := hM
  -- Braiding compares right tensoring with the exact functor `tensorLeft M`.
  letI :
      PreservesFiniteLimits (CategoryTheory.MonoidalCategory.tensorRight M) :=
    preservesFiniteLimits_of_natIso
      (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight M)
  letI :
      PreservesFiniteColimits (CategoryTheory.MonoidalCategory.tensorRight M) :=
    preservesFiniteColimits_of_natIso
      (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight M)
  let hExact :
      CategoryTheory.exactFunctor (ModuleCat R) (ModuleCat R)
        (CategoryTheory.MonoidalCategory.tensorRight M) :=
    (CategoryTheory.exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
  letI :
      (CategoryTheory.MonoidalCategory.tensorRight M).Additive :=
    (CategoryTheory.exactFunctor_le_additiveFunctor (ModuleCat R) (ModuleCat R))
      (CategoryTheory.MonoidalCategory.tensorRight M) hExact
  letI :
      (CategoryTheory.MonoidalCategory.tensorRight M).PreservesHomology :=
    inferInstance
  -- Exactness of the short complex `L.sc n` is preserved degreewise by `tensorRight M`.
  rw [HomologicalComplex.acyclic_iff] at hL ⊢
  intro n
  rw [HomologicalComplex.exactAt_iff]
  have hLn : (L.sc n).Exact := by
    -- Unpack acyclicity into exactness at the chosen degree.
    simpa [HomologicalComplex.exactAt_iff] using hL n
  simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
    hLn.map (CategoryTheory.MonoidalCategory.tensorRight M)

/-- Helper for Lemma 15.59.7: acyclicity transports across an isomorphism of cochain complexes. -/
private theorem acyclic_of_iso
    {K L : CochainComplex (ModuleCat R) ℤ}
    (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Read acyclicity degreewise and move exactness across the complex isomorphism.
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hK n) e

/-- Helper for Lemma 15.59.7: if a shift of a cochain complex is acyclic, then the original
complex is acyclic. -/
private theorem acyclic_of_shift
    (K : CochainComplex (ModuleCat R) ℤ) (n : ℤ)
    (hShift : (K⟦n⟧).Acyclic) :
    K.Acyclic := by
  -- Route correction: descend acyclicity from the shifted complex through the canonical homology
  -- shift isomorphism instead of unfolding the shifted differentials directly.
  rw [HomologicalComplex.acyclic_iff] at hShift ⊢
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hZeroShift : IsZero ((K⟦n⟧).homology (i - n)) := by
    -- Exactness of the shifted complex at degree `i - n` gives vanishing of that shifted homology.
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hShift (i - n)
  -- The shifted homology in degree `i - n` is canonically the original homology in degree `i`.
  exact hZeroShift.of_iso
    (((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (0 : ℤ)).shiftIso
      n (i - n) i (by omega)).app K).symm

/-- Helper for Lemma 15.59.7: tensoring on the left by a fixed complex transports an isomorphism
in the right factor. -/
private noncomputable def tensor_right_iso
    (M : CochainComplex (ModuleCat R) ℤ)
    {K L : CochainComplex (ModuleCat R) ℤ}
    (e : K ≅ L) :
    HomologicalComplex.tensorObj M K ≅ HomologicalComplex.tensorObj M L :=
  { hom := HomologicalComplex.tensorHom (𝟙 M) e.hom
    inv := HomologicalComplex.tensorHom (𝟙 M) e.inv
    hom_inv_id := by
      -- Check the inverse relation on each tensor summand of every total degree.
      apply HomologicalComplex.hom_ext
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      have hhom :
          HomologicalComplex.ιTensorObj M K p q n h ≫
              (HomologicalComplex.tensorHom (𝟙 M) e.hom).f n =
            (M.X p ◁ e.hom.f q) ≫ HomologicalComplex.ιTensorObj M L p q n h := by
        simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
          HomologicalComplex.id_f] using
          (HomologicalComplex.ι_mapBifunctorMap
            (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := L)
            (f₁ := 𝟙 M) (f₂ := e.hom) (F := curriedTensor (ModuleCat R))
            (c := ComplexShape.up ℤ) p q n h)
      have hinv :
          HomologicalComplex.ιTensorObj M L p q n h ≫
              (HomologicalComplex.tensorHom (𝟙 M) e.inv).f n =
            (M.X p ◁ e.inv.f q) ≫ HomologicalComplex.ιTensorObj M K p q n h := by
        simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
          HomologicalComplex.id_f] using
          (HomologicalComplex.ι_mapBifunctorMap
            (K₁ := M) (K₂ := L) (L₁ := M) (L₂ := K)
            (f₁ := 𝟙 M) (f₂ := e.inv) (F := curriedTensor (ModuleCat R))
            (c := ComplexShape.up ℤ) p q n h)
      have hq :
          e.hom.f q ≫ e.inv.f q = 𝟙 (K.X q) := by
        exact congrArg (fun α : K ⟶ K ↦ α.f q) e.hom_inv_id
      calc
        HomologicalComplex.ιTensorObj M K p q n h ≫
            ((HomologicalComplex.tensorHom (𝟙 M) e.hom ≫
              HomologicalComplex.tensorHom (𝟙 M) e.inv).f n)
          = (M.X p ◁ e.hom.f q) ≫
              (HomologicalComplex.ιTensorObj M L p q n h ≫
                (HomologicalComplex.tensorHom (𝟙 M) e.inv).f n) := by
                  simpa [HomologicalComplex.comp_f, Category.assoc] using
                    congrArg
                      (fun k ↦ k ≫ (HomologicalComplex.tensorHom (𝟙 M) e.inv).f n)
                      hhom
        _ = (M.X p ◁ e.hom.f q) ≫
              ((M.X p ◁ e.inv.f q) ≫ HomologicalComplex.ιTensorObj M K p q n h) := by
                rw [hinv]
        _ = (M.X p ◁ (e.hom.f q ≫ e.inv.f q)) ≫
              HomologicalComplex.ιTensorObj M K p q n h := by
                rw [← Category.assoc, ← whiskerLeft_comp]
        _ = HomologicalComplex.ιTensorObj M K p q n h := by
          simp [hq]
    inv_hom_id := by
      -- The reverse inverse relation is the same computation with `e.inv_hom_id`.
      apply HomologicalComplex.hom_ext
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      have hhom :
          HomologicalComplex.ιTensorObj M L p q n h ≫
              (HomologicalComplex.tensorHom (𝟙 M) e.inv).f n =
            (M.X p ◁ e.inv.f q) ≫ HomologicalComplex.ιTensorObj M K p q n h := by
        simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
          HomologicalComplex.id_f] using
          (HomologicalComplex.ι_mapBifunctorMap
            (K₁ := M) (K₂ := L) (L₁ := M) (L₂ := K)
            (f₁ := 𝟙 M) (f₂ := e.inv) (F := curriedTensor (ModuleCat R))
            (c := ComplexShape.up ℤ) p q n h)
      have hinv :
          HomologicalComplex.ιTensorObj M K p q n h ≫
              (HomologicalComplex.tensorHom (𝟙 M) e.hom).f n =
            (M.X p ◁ e.hom.f q) ≫ HomologicalComplex.ιTensorObj M L p q n h := by
        simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
          HomologicalComplex.id_f] using
          (HomologicalComplex.ι_mapBifunctorMap
            (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := L)
            (f₁ := 𝟙 M) (f₂ := e.hom) (F := curriedTensor (ModuleCat R))
            (c := ComplexShape.up ℤ) p q n h)
      have hq :
          e.inv.f q ≫ e.hom.f q = 𝟙 (L.X q) := by
        exact congrArg (fun α : L ⟶ L ↦ α.f q) e.inv_hom_id
      calc
        HomologicalComplex.ιTensorObj M L p q n h ≫
            ((HomologicalComplex.tensorHom (𝟙 M) e.inv ≫
              HomologicalComplex.tensorHom (𝟙 M) e.hom).f n)
          = (M.X p ◁ e.inv.f q) ≫
              (HomologicalComplex.ιTensorObj M K p q n h ≫
                (HomologicalComplex.tensorHom (𝟙 M) e.hom).f n) := by
                  simpa [HomologicalComplex.comp_f, Category.assoc] using
                    congrArg
                      (fun k ↦ k ≫ (HomologicalComplex.tensorHom (𝟙 M) e.hom).f n)
                      hhom
        _ = (M.X p ◁ e.inv.f q) ≫
              ((M.X p ◁ e.hom.f q) ≫ HomologicalComplex.ιTensorObj M L p q n h) := by
                rw [hinv]
        _ = (M.X p ◁ (e.inv.f q ≫ e.hom.f q)) ≫
              HomologicalComplex.ιTensorObj M L p q n h := by
                rw [← Category.assoc, ← whiskerLeft_comp]
        _ = HomologicalComplex.ιTensorObj M L p q n h := by
          simp [hq] }

/-- Helper for Lemma 15.59.7: K-flatness transports across an isomorphism of cochain complexes. -/
private theorem isKFlat_of_iso
    {K L : CochainComplex (ModuleCat R) ℤ}
    (e : K ≅ L) (hK : K.IsKFlat) :
    L.IsKFlat := by
  -- Unpack the owner and transport the tensor test across the induced right-factor tensor
  -- isomorphism.
  rw [CochainComplex.isKFlat_iff] at hK ⊢
  intro M _ hM
  have hTensorK : (HomologicalComplex.tensorObj M K).Acyclic := hK hM
  let eTensor :
      HomologicalComplex.tensorObj M K ≅ HomologicalComplex.tensorObj M L :=
    tensor_right_iso (R := R) M e
  -- The tensor comparison is an isomorphism because the right-factor map is an isomorphism.
  exact acyclic_of_iso (R := R) eTensor hTensorK

/-- Helper for Lemma 15.59.7: shifting a single cochain complex by its own degree identifies it
with the degree-zero single complex. -/
private noncomputable def single_shift_to_zero_iso
    (M : ModuleCat R) (n : ℤ) :
    (((CochainComplex.singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) :=
  ((CochainComplex.singleFunctors (ModuleCat R)).shiftIso n 0 n (by simp)).app M

/-- Helper for Lemma 15.59.7: fixed-left tensoring commutes with shifts in the right argument. -/
private noncomputable def tensor_right_shift_transport_iso
    (L K : CochainComplex (ModuleCat R) ℤ) (b : ℤ) :
    HomologicalComplex.tensorObj L (K⟦b⟧) ≅
      (HomologicalComplex.tensorObj L K)⟦b⟧ := by
  -- Use the owner bifunctor-shift comparison directly on the tensor bifunctor.
  simpa using
    (CochainComplex.mapBifunctorShift₂Iso L K (curriedTensor (ModuleCat R)) b)

/-- Helper for Lemma 15.59.7: tensoring with a degree-zero single flat module complex is exactly
tensoring on the right by that flat module, off the diagonal all summands vanish. -/
private theorem tensor_single_zero_off_diagonal_isZero
    (L : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (p q : ℤ) (hq : q ≠ 0) :
    IsZero (((curriedTensor (ModuleCat R)).obj (L.X p)).obj
      (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).X q)) := by
  -- Apply `tensorLeft (L.X p)` to the zero object occurring in the single complex away from degree
  -- `0`.
  exact
    CategoryTheory.Functor.map_isZero ((curriedTensor (ModuleCat R)).obj (L.X p))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M q hq)

/-- Helper for Lemma 15.59.7: on the surviving degree-`0` summand, tensoring with the single
complex is just right tensoring by the underlying module. -/
private noncomputable def tensor_single_zero_diagonal_iso
    (L : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    ((curriedTensor (ModuleCat R)).obj (L.X n)).obj
      (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).X 0) ≅
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).X n := by
  -- The right tensor complex is defined degreewise, so only the canonical identification of the
  -- degree-`0` term of the single complex with `M` remains.
  simpa using
    CategoryTheory.Functor.mapIso ((curriedTensor (ModuleCat R)).obj (L.X n))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M)

/-- Helper for Lemma 15.59.7: postcomposing a descended tensor-totalization map can be checked on
each `(p,q)` summand. -/
@[reassoc]
private theorem iTensorObj_mapBifunctorDesc_assoc
    {K L : CochainComplex (ModuleCat R) ℤ} (n : ℤ) {A B : ModuleCat R}
    (f : ∀ p q
      (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat R)).obj (K.X p)).obj (L.X q) ⟶ A)
    (u : A ⟶ B) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R))
          (c := ComplexShape.up ℤ) (A := A) (j := n) f ≫ u =
      f p q h ≫ u := by
  -- Cross the `tensorObj` abbreviation once, then postcompose the owner universal-property
  -- formula `ι_mapBifunctorDesc`.
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) (A := A) (j := n) (f := f) p q h)

/-- Helper for Lemma 15.59.7: the forward degree-`n` comparison map kills every off-diagonal
summand and keeps only the `(n,0)` component. -/
private noncomputable def tensor_single_zero_component_hom
    (L : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    (HomologicalComplex.tensorObj L
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).X n ⟶
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := L)
    (K₂ := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
    (F := curriedTensor (ModuleCat R))
    (c := ComplexShape.up ℤ)
    (A := (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).X n)
    (j := n)
    (fun p q h ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        exact (tensor_single_zero_diagonal_iso L M n).hom
      · exact 0)

/-- Helper for Lemma 15.59.7: on the surviving `(n,0)` summand, the forward comparison map is the
canonical diagonal isomorphism. -/
@[reassoc]
private theorem tensor_single_zero_component_hom_diag
    (L : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιTensorObj L
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) n 0 n h ≫
      tensor_single_zero_component_hom L M n =
        (tensor_single_zero_diagonal_iso L M n).hom := by
  -- Restrict the descended map to the unique diagonal summand where the single complex survives.
  let A :
      ModuleCat R :=
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).X n
  let f : ∀ p q
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat R)).obj (L.X p)).obj
        (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).X q) ⟶ A :=
    fun p q h' ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h'
        subst p
        exact (tensor_single_zero_diagonal_iso L M n).hom
      · exact 0
  -- Route correction: evaluate `mapBifunctorDesc` once, then normalize only the diagonal branch.
  simpa [tensor_single_zero_component_hom, A, f] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := L)
      (L := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
      (n := n) (A := A) (B := A) f (𝟙 A) n 0 h)

/-- Helper for Lemma 15.59.7: away from the diagonal, the forward comparison map vanishes because
the degree-zero single complex has zero terms. -/
@[reassoc]
private theorem tensor_single_zero_component_hom_off_diagonal
    (L : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (hq : q ≠ 0) :
    HomologicalComplex.ιTensorObj L
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) p q n h ≫
      tensor_single_zero_component_hom L M n =
        0 := by
  -- Restrict the descended map to an off-diagonal summand, where the defining branch is zero.
  let A :
      ModuleCat R :=
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).X n
  let f : ∀ p' q'
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = n),
      ((curriedTensor (ModuleCat R)).obj (L.X p')).obj
        (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).X q') ⟶ A :=
    fun p' q' h' ↦ by
      by_cases hq' : q' = 0
      · subst hq'
        have hp' : p' = n := by simpa using h'
        subst p'
        exact (tensor_single_zero_diagonal_iso L M n).hom
      · exact 0
  -- Route correction: do not unfold the totalization; the universal property already isolates the
  -- off-diagonal branch, which is definitionally zero.
  simpa [tensor_single_zero_component_hom, A, f, hq] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := L)
      (L := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
      (n := n) (A := A) (B := A) f (𝟙 A) p q h)

/-- Helper for Lemma 15.59.7: the inverse degree-`n` comparison map reinserts the surviving
diagonal summand into the tensor totalization. -/
private noncomputable def tensor_single_zero_component_inv
    (L : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).X n ⟶
      (HomologicalComplex.tensorObj L
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).X n :=
  (tensor_single_zero_diagonal_iso L M n).inv ≫
    HomologicalComplex.ιTensorObj L
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) n 0 n
      (by simpa using (show n + 0 = n by simp))

/-- Helper for Lemma 15.59.7: in total degree `n`, tensoring with the degree-zero single complex
collapses to the unique surviving diagonal summand. -/
private noncomputable def tensor_single_zero_component_iso
    (L : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    (HomologicalComplex.tensorObj L
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).X n ≅
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).X n :=
  { hom := tensor_single_zero_component_hom L M n
    inv := tensor_single_zero_component_inv L M n
    hom_inv_id := by
      -- Check the identity on the tensor-totalization object summandwise.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        -- The surviving diagonal summand is sent out and then reinserted unchanged.
        change
          ((HomologicalComplex.ιTensorObj L
                ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) n 0 n h ≫
              tensor_single_zero_component_hom L M n) ≫
            tensor_single_zero_component_inv L M n) =
            HomologicalComplex.ιTensorObj L
              ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) n 0 n h ≫
                𝟙 ((HomologicalComplex.tensorObj L
                  ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).X n)
        simpa [tensor_single_zero_component_inv, Category.assoc] using
          congrArg
            (fun k ↦ k ≫ tensor_single_zero_component_inv L M n)
            (tensor_single_zero_component_hom_diag L M n h)
      · -- Off the diagonal the forward map is zero, and the source summand is already zero.
        change
          ((HomologicalComplex.ιTensorObj L
                ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) p q n h ≫
              tensor_single_zero_component_hom L M n) ≫
            tensor_single_zero_component_inv L M n) =
            HomologicalComplex.ιTensorObj L
              ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) p q n h ≫
                𝟙 ((HomologicalComplex.tensorObj L
                  ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).X n)
        rw [tensor_single_zero_component_hom_off_diagonal L M n p q h hq]
        simp only [zero_comp, Category.comp_id]
        symm
        exact (tensor_single_zero_off_diagonal_isZero L M p q hq).eq_of_src _ _
    inv_hom_id := by
      -- The inverse first lands in the diagonal summand, where the forward map is the diagonal
      -- isomorphism.
      let h0 : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n := by
        simpa using (show n + 0 = n by simp)
      -- Rewrite the middle composite to the diagonal isomorphism and cancel it immediately.
      change
        ((tensor_single_zero_diagonal_iso L M n).inv ≫
            HomologicalComplex.ιTensorObj L
              ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) n 0 n h0) ≫
          tensor_single_zero_component_hom L M n =
            𝟙 ((((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L).X n)
      calc
        ((tensor_single_zero_diagonal_iso L M n).inv ≫
            HomologicalComplex.ιTensorObj L
              ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) n 0 n h0) ≫
          tensor_single_zero_component_hom L M n
            = (tensor_single_zero_diagonal_iso L M n).inv ≫
                (HomologicalComplex.ιTensorObj L
                  ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) n 0 n h0 ≫
                    tensor_single_zero_component_hom L M n) := by
                      simp [Category.assoc]
        _ = (tensor_single_zero_diagonal_iso L M n).inv ≫
              (tensor_single_zero_diagonal_iso L M n).hom := by
                simpa using
                  congrArg (fun k ↦ (tensor_single_zero_diagonal_iso L M n).inv ≫ k)
                    (tensor_single_zero_component_hom_diag L M n h0)
        _ = 𝟙 _ := by simp }

/-- Helper for Lemma 15.59.7: the diagonal degreewise identification is natural in the left
cochain-complex differential. -/
private theorem tensor_single_zero_diagonal_iso_hom_naturality
    (L : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single_zero_diagonal_iso L M i).hom ≫
        (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L).d i j =
      (((curriedTensor (ModuleCat R)).map (L.d i j)).app
          (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).X 0)) ≫
        (tensor_single_zero_diagonal_iso L M j).hom := by
  -- The degreewise comparison is obtained by applying the tensor functor to `singleObjXSelf`.
  simpa [tensor_single_zero_diagonal_iso,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d] using
    (((curriedTensor (ModuleCat R)).map (L.d i j)).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom)

/-- Helper for Lemma 15.59.7: the inverse diagonal identification is the same naturality square,
rewritten in the form needed for the chain-level inverse map. -/
private theorem tensor_single_zero_diagonal_iso_inv_naturality
    (L : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single_zero_diagonal_iso L M i).inv ≫
        (((curriedTensor (ModuleCat R)).map (L.d i j)).app
          (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).X 0)) =
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).d i j ≫
        (tensor_single_zero_diagonal_iso L M j).inv := by
  -- Cancel the target diagonal isomorphism and reuse the forward naturality square.
  apply (cancel_mono (tensor_single_zero_diagonal_iso L M j).hom).1
  simpa [Category.assoc] using
    calc
      (tensor_single_zero_diagonal_iso L M i).inv ≫
          (((curriedTensor (ModuleCat R)).map (L.d i j)).app
            (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).X 0)) ≫
          (tensor_single_zero_diagonal_iso L M j).hom
        = (tensor_single_zero_diagonal_iso L M i).inv ≫
            ((tensor_single_zero_diagonal_iso L M i).hom ≫
              (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj L).d i j) := by
            rw [tensor_single_zero_diagonal_iso_hom_naturality L M i j hij]
      _ =
          (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L).d i j := by
            simp [Category.assoc]

/-- Helper for Lemma 15.59.7: the inverse degreewise comparison map is already a chain map, since
only the horizontal part of the tensor differential survives on the degree-zero single complex. -/
private theorem tensor_single_zero_component_inv_comm
    (L : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    tensor_single_zero_component_inv L M i ≫
        (HomologicalComplex.tensorObj L
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).d i j =
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).d i j ≫
        tensor_single_zero_component_inv L M j := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  -- Expand the total differential into its horizontal and vertical pieces; the vertical piece is
  -- zero because the single complex has zero differential.
  simp only [tensor_single_zero_component_inv, Category.assoc,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.single_obj_d, Functor.map_zero, comp_zero, add_zero]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := L)
      (K₂ := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
      (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ)
      (h := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))
      (i₂ := 0)
      (j := i + 1)
      (h' := by simpa using (show (i + 1) + 0 = i + 1 by simp))]
  rw [HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := L)
      (K₂ := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
      (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ)
      (i₁ := i)
      (h := (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp))
      (j := i + 1)
      (h' := by simpa using (show i + (0 + 1) = i + 1 by simp))]
  -- The remaining square is the diagonal naturality square, followed by reinserting the summand.
  have hsingle :
      (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).d 0 (0 + 1)) = 0 := rfl
  rw [hsingle, Functor.map_zero, zero_comp, smul_zero, comp_zero, add_zero]
  rw [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, 0) = 1 by
      rfl, one_smul]
  rw [← Category.assoc]
  rw [tensor_single_zero_diagonal_iso_inv_naturality
      (L := L)
      (M := M)
      (i := i)
      (j := i + 1)
      (hij := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))]
  simpa [HomologicalComplex.ιTensorObj, Category.assoc]

/-- Helper for Lemma 15.59.7: tensoring with a degree-zero single flat module complex is exactly
tensoring on the right by that flat module. -/
private theorem tensor_single_zero_acyclic_of_flat
    (L : CochainComplex (ModuleCat R) ℤ) (hL : L.Acyclic) (M : ModuleCat R)
    (hM : Module.Flat R M) :
    (HomologicalComplex.tensorObj L ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).Acyclic := by
  -- The intended proof identifies the degree-zero single tensor totalization with the right-tensor
  -- complex `((tensorRight M).mapHomologicalComplex _).obj L`.
  let eInv :
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) ≅
        HomologicalComplex.tensorObj L
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (tensor_single_zero_component_iso L M n).symm)
      (fun i j hij ↦ by
        -- The assembled inverse comparison is a chain map degreewise by the previous lemma.
        simpa using tensor_single_zero_component_inv_comm L M i j hij)
  have hRightTensor :
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).Acyclic :=
    mapHomologicalComplex_acyclic_of_tensorRight_flat L hL M hM
  -- Transport acyclicity across the componentwise chain isomorphism.
  exact acyclic_of_iso (R := R) eInv hRightTensor

/-- Helper for Lemma 15.59.7: a single cochain complex on a flat module is K-flat. -/
private theorem single_isKFlat_of_flat
    (M : ModuleCat R) (n : ℤ) (hM : Module.Flat R M) :
    ((CochainComplex.singleFunctor (ModuleCat R) n).obj M).IsKFlat := by
  -- Shift the single complex to degree `0`, use the already-proved degree-zero tensor
  -- identification, and then descend acyclicity from the shifted tensor complex.
  rw [CochainComplex.isKFlat_iff]
  intro L _ hL
  have hZero :
      (HomologicalComplex.tensorObj L
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).Acyclic :=
    tensor_single_zero_acyclic_of_flat (R := R) L hL M hM
  let eSingle :
      (((CochainComplex.singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) :=
    single_shift_to_zero_iso (R := R) M n
  let eTensorSingle :
      HomologicalComplex.tensorObj L
          (((CochainComplex.singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
        HomologicalComplex.tensorObj L
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) :=
    tensor_right_iso (R := R) L eSingle
  have hShiftSource :
      (HomologicalComplex.tensorObj L
        (((CochainComplex.singleFunctor (ModuleCat R) n).obj M)⟦n⟧)).Acyclic :=
    acyclic_of_iso (R := R) eTensorSingle.symm hZero
  have hTensorShifted :
      ((HomologicalComplex.tensorObj L
        ((CochainComplex.singleFunctor (ModuleCat R) n).obj M))⟦n⟧).Acyclic :=
    acyclic_of_iso (R := R)
      (tensor_right_shift_transport_iso (R := R) L
        ((CochainComplex.singleFunctor (ModuleCat R) n).obj M) n)
      hShiftSource
  -- The tensor/shift comparison reduces the arbitrary single degree to the degree-zero case.
  exact acyclic_of_shift (R := R)
    (HomologicalComplex.tensorObj L
      ((CochainComplex.singleFunctor (ModuleCat R) n).obj M)) n hTensorShifted

/-- Helper for Lemma 15.59.7: the single quotient term in the brutal-left stage sequence is
termwise flat as soon as the original complex is termwise flat. -/
private theorem shifted_brutal_left_stage_single_termwiseFlat
    (Q : CochainComplex (ModuleCat R) ℤ) [Q.IsStrictlyLE 0]
    (hFlat : Q.IsTermwiseFlat) (m : ℕ) :
    (shifted_brutal_left_stage_single (A := ModuleCat R) Q m).IsTermwiseFlat := by
  intro i
  by_cases hi : i = -((m + 1 : ℕ) : ℤ)
  · subst hi
    let eDiag :
        ((shifted_brutal_left_stage_single (A := ModuleCat R) Q m).X (-((m + 1 : ℕ) : ℤ))) ≅
          Q.X (-((m + 1 : ℕ) : ℤ)) :=
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((m + 1 : ℕ) : ℤ))
        (Q.X (-((m + 1 : ℕ) : ℤ)))
    have hCutoff : Module.Flat R (Q.X (-((m + 1 : ℕ) : ℤ)) : Type u) := hFlat _
    letI : Module.Flat R (Q.X (-((m + 1 : ℕ) : ℤ)) : Type u) := hCutoff
    exact Module.Flat.of_linearEquiv eDiag.toLinearEquiv
  · have hzero :
        IsZero ((shifted_brutal_left_stage_single (A := ModuleCat R) Q m).X i) := by
      simpa [shifted_brutal_left_stage_single] using
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-((m + 1 : ℕ) : ℤ))
          (Q.X (-((m + 1 : ℕ) : ℤ))) i hi)
    letI :
        Subsingleton (((shifted_brutal_left_stage_single (A := ModuleCat R) Q m).X i :
          ModuleCat R)) :=
      ModuleCat.subsingleton_of_isZero hzero
    let eZero :
        (((shifted_brutal_left_stage_single (A := ModuleCat R) Q m).X i : ModuleCat R)) ≃ₗ[R]
          (Fin 0 → R) :=
      LinearEquiv.ofSubsingleton _ _
    have hFreeZero :
        Module.Free R
          ((((shifted_brutal_left_stage_single (A := ModuleCat R) Q m).X i :
            ModuleCat R)) : Type u) :=
      Module.Free.of_equiv eZero.symm
    -- Off the cutoff degree, the single complex term is zero, hence free and flat.
    exact Module.Flat.of_free

/-- Helper for Lemma 15.59.7: the initial brutal-left stage is a single flat complex, hence
K-flat. -/
private theorem shifted_brutal_left_stage_zero_isKFlat
    (Q : CochainComplex (ModuleCat R) ℤ) [Q.IsStrictlyLE 0]
    (hFlat : Q.IsTermwiseFlat) :
    (shifted_brutal_left_stage (A := ModuleCat R) Q 0).IsKFlat := by
  let K₀ : CochainComplex (ModuleCat R) ℤ :=
    shifted_brutal_left_stage (A := ModuleCat R) Q 0
  letI : K₀.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    refine Q.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (0 : ℤ)) i ?_
    simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hi
  letI : K₀.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    by_cases h0i : (0 : ℤ) ≤ i
    · let e := shifted_brutal_left_stage_x_iso (A := ModuleCat R) Q 0 h0i
      have hzero : IsZero (Q.X i) := by
        simpa using Q.isZero_of_isStrictlyLE 0 i hi
      exact hzero.of_iso e
    · refine Q.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (0 : ℤ)) i ?_
      simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge h0i
  let M₀ : ModuleCat R := Classical.choose (CochainComplex.exists_iso_single (K := K₀) 0)
  let e₀ : K₀ ≅ ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M₀) := by
    simpa using
      (Classical.choice (Classical.choose_spec (CochainComplex.exists_iso_single (K := K₀) 0)))
  let eX :
      K₀.X 0 ≅ M₀ :=
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) 0).mapIso e₀ ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M₀
  have hK₀X₀ : Module.Flat R (K₀.X 0 : Type u) := by
    -- The retained degree `0` of the stage agrees with the original degree `0` term of `Q`.
    have hQ₀ : Module.Flat R (Q.X 0 : Type u) := hFlat 0
    letI : Module.Flat R (Q.X 0 : Type u) := hQ₀
    exact Module.Flat.of_linearEquiv
      ((shifted_brutal_left_stage_x_iso (A := ModuleCat R) Q 0 (by simp)).toLinearEquiv)
  have hM₀ : Module.Flat R (M₀ : Type u) := by
    -- The chosen single-term model has the same degree-`0` module as the stage.
    exact Module.Flat.of_linearEquiv eX.toLinearEquiv.symm
  have hSingle :
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M₀).IsKFlat :=
    single_isKFlat_of_flat (R := R) M₀ 0 hM₀
  exact isKFlat_of_iso (R := R) e₀.symm hSingle

/-- Helper for Lemma 15.59.7: every finite brutal-left stage of a strictly-left-supported flat
complex is K-flat. -/
private theorem shifted_brutal_left_stage_isKFlat
    (Q : CochainComplex (ModuleCat R) ℤ) [Q.IsStrictlyLE 0]
    (hFlat : Q.IsTermwiseFlat) :
    ∀ m : ℕ, (shifted_brutal_left_stage (A := ModuleCat R) Q m).IsKFlat
  | 0 => by
      -- The initial stage is concentrated in degree `0`.
      exact shifted_brutal_left_stage_zero_isKFlat (R := R) Q hFlat
  | m + 1 => by
      -- Use the sign-corrected short exact sequence `stage m ⟶ stage (m+1) ⟶ single`.
      let S :=
        shifted_brutal_left_stage_short_complex_sign_corrected (A := ModuleCat R) Q m
      have hS : S.ShortExact :=
        shifted_brutal_left_stage_short_exact_sign_corrected (A := ModuleCat R) Q m
      have hStage :
          S.X₁.IsKFlat :=
        by
          change (shifted_brutal_left_stage (A := ModuleCat R) Q m).IsKFlat
          exact shifted_brutal_left_stage_isKFlat Q hFlat m
      have hSingleFlat :
          S.X₃.IsTermwiseFlat := by
        change (shifted_brutal_left_stage_single (A := ModuleCat R) Q m).IsTermwiseFlat
        exact shifted_brutal_left_stage_single_termwiseFlat (R := R) Q hFlat m
      have hSingle :
          S.X₃.IsKFlat := by
        change (shifted_brutal_left_stage_single (A := ModuleCat R) Q m).IsKFlat
        simpa [shifted_brutal_left_stage_single] using
          single_isKFlat_of_flat (R := R)
            (Q.X (-((m + 1 : ℕ) : ℤ))) (-((m + 1 : ℕ) : ℤ))
            (hFlat (-((m + 1 : ℕ) : ℤ)))
      change (shifted_brutal_left_stage (A := ModuleCat R) Q (m + 1)).IsKFlat
      exact CategoryTheory.ShortComplex.ShortExact.isKFlat_X₂
        (R := R) (S := S) hS hSingleFlat hStage hSingle

/-- Helper for Lemma 15.59.7: the canonical map from the `m`th brutal-left stage back to the full
complex is the identity on retained degrees and zero below the cutoff. -/
private noncomputable def shifted_brutal_left_stage_to_complex
    (Q : CochainComplex (ModuleCat R) ℤ) [Q.IsStrictlyLE 0] (m : ℕ) :
    shifted_brutal_left_stage (A := ModuleCat R) Q m ⟶ Q :=
  { f := fun i ↦
      if hi : -((m : ℕ) : ℤ) ≤ i then
        (shifted_brutal_left_stage_x_iso (A := ModuleCat R) Q m hi).hom
      else
        0
    comm' := by
      intro i j hij
      by_cases hi : -((m : ℕ) : ℤ) ≤ i
      · have hj : -((m : ℕ) : ℤ) ≤ j := by
          have hij' : i + 1 = j := by simpa using hij
          omega
        -- On retained degrees, the stage differential is the original differential of `Q`.
        apply (cancel_epi
          (shifted_brutal_left_stage_x_iso (A := ModuleCat R) Q m hi).inv).1
        rw [dif_pos hi, dif_pos hj]
        simpa [Category.assoc] using
          (shifted_brutal_left_stage_d_via_x_iso (A := ModuleCat R) (K := Q) m hi hj).symm
      · by_cases hj : -((m : ℕ) : ℤ) ≤ j
        · have hi_lt : i < -((m : ℕ) : ℤ) := by
            have hij' : i + 1 = j := by simpa using hij
            omega
          have hzero :
              IsZero ((shifted_brutal_left_stage (A := ModuleCat R) Q m).X i) := by
            exact
              (shifted_brutal_left_stage (A := ModuleCat R) Q m).isZero_of_isStrictlyGE
                (-((m : ℕ) : ℤ)) i hi_lt
          -- Below the cutoff, the source term vanishes.
          rw [dif_neg hi, zero_comp, dif_pos hj]
          exact hzero.eq_of_src _ _
        · -- If both degrees are below the cutoff, both stage components vanish.
          rw [dif_neg hi, dif_neg hj, zero_comp, comp_zero] }

/-- Helper for Lemma 15.59.7: in degree `i` above the cutoff, the stage-to-complex comparison is
the canonical identification with the original term. -/
private theorem shifted_brutal_left_stage_to_complex_component_eq_iso
    (Q : CochainComplex (ModuleCat R) ℤ) [Q.IsStrictlyLE 0]
    (m : ℕ) {i : ℤ} (hi : -((m : ℕ) : ℤ) ≤ i) :
    (shifted_brutal_left_stage_to_complex (R := R) Q m).f i =
      (shifted_brutal_left_stage_x_iso (A := ModuleCat R) Q m hi).hom := by
  -- The comparison map is defined to be the retained-degree identification.
  simp [shifted_brutal_left_stage_to_complex, hi]

/-- Helper for Lemma 15.59.7: below the cutoff, the stage-to-complex comparison vanishes. -/
private theorem shifted_brutal_left_stage_to_complex_component_eq_zero
    (Q : CochainComplex (ModuleCat R) ℤ) [Q.IsStrictlyLE 0]
    (m : ℕ) {i : ℤ} (hi : i < -((m : ℕ) : ℤ)) :
    (shifted_brutal_left_stage_to_complex (R := R) Q m).f i = 0 := by
  -- The stage has no degree-`i` term below its cutoff.
  simp [shifted_brutal_left_stage_to_complex, not_le_of_gt hi]

/-- Helper for Lemma 15.59.7: the canonical pair-indexed fiber computing total tensor degree
`n`. -/
private abbrev tensor_degree_preimage (n : ℤ) : Type :=
  ((ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⁻¹'
    ({n} : Set ℤ))

/-- Helper for Lemma 15.59.7: the total-degree tensor fiber as a discrete indexing category. -/
private abbrev tensor_degree_preimage_discrete (n : ℤ) :=
  Discrete (tensor_degree_preimage n)

/-- Helper for Lemma 15.59.7: a pair `(p,q)` with total degree `n` lies in the canonical tensor
degree fiber over `n`. -/
private theorem tensor_degree_pair_mem
    (p q n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (p, q) ∈ ((ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⁻¹'
      ({n} : Set ℤ)) := by
  simpa using h

/-- Helper for Lemma 15.59.7: the pair `(p,q)` regarded as an element of the total-degree tensor
fiber over `n`. -/
private def tensor_degree_index
    (p q n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    tensor_degree_preimage n :=
  ⟨(p, q), tensor_degree_pair_mem p q n h⟩

/-- Helper for Lemma 15.59.7: the canonical `(p,q)` tensor summands contributing to total degree
`n`. -/
private abbrev tensor_degree_summands
    (L Q : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    tensor_degree_preimage n → ModuleCat R :=
  fun s ↦ ((curriedTensor (ModuleCat R)).obj (L.X s.1.1)).obj (Q.X s.1.2)

/-- Helper for Lemma 15.59.7: the underlying module family of the pair-indexed tensor summands. -/
private abbrev tensor_degree_summands_type
    (L Q : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    tensor_degree_preimage n → Type u :=
  fun s ↦ (tensor_degree_summands (R := R) L Q n s : Type u)

/-- Helper for Lemma 15.59.7: the concrete direct-sum module attached to the pair-indexed tensor
degree `n`. -/
private abbrev tensor_degree_directSum_module
    (L Q : CochainComplex (ModuleCat R) ℤ) (n : ℤ) : Type u :=
  DirectSum (tensor_degree_preimage n) (tensor_degree_summands_type (R := R) L Q n)

/-- Helper for Lemma 15.59.7: the pair-indexed summand diagram whose colimit is the degree-`n`
term of the tensor totalization. -/
private noncomputable def tensor_preimage_diagram
    (L Q : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    tensor_degree_preimage_discrete n ⥤ ModuleCat R :=
  Discrete.functor fun s ↦ tensor_degree_summands (R := R) L Q n s

/-- Helper for Lemma 15.59.7: the tautological cocone from the pair-indexed tensor summands to
the actual degree-`n` tensor term. -/
private noncomputable def tensor_preimage_cocone
    (L Q : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    Cocone (tensor_preimage_diagram (R := R) L Q n) where
  pt := (HomologicalComplex.tensorObj L Q).X n
  ι := Discrete.natTrans fun s ↦
    HomologicalComplex.ιTensorObj L Q s.as.1.1 s.as.1.2 n s.as.2

/-- Helper for Lemma 15.59.7: the tautological pair-indexed tensor cocone is colimiting by the
universal property of `mapBifunctorDesc`. -/
private noncomputable def tensor_preimage_cocone_isColimit
    (L Q : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    IsColimit (tensor_preimage_cocone (R := R) L Q n) :=
  IsColimit.mk
    (fun s ↦
      HomologicalComplex.mapBifunctorDesc
        (K₁ := L) (K₂ := Q) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
        (fun p q h ↦ s.ι.app ⟨⟨(p, q), by simpa using h⟩⟩))
    (fun s t ↦ by
      -- Restricting the descended map to one summand recovers the specified cocone leg.
      simpa [tensor_preimage_cocone] using
        (HomologicalComplex.ι_mapBifunctorDesc
          (K₁ := L) (K₂ := Q) (F := curriedTensor (ModuleCat R))
          (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
          (f := fun p q h ↦ s.ι.app ⟨⟨(p, q), by simpa using h⟩⟩)
          t.as.1.1 t.as.1.2 t.as.2))
    (fun s m hm ↦ by
      -- Two maps from the tensor degree agree once they agree on every `(p,q)` summand.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      let t : tensor_degree_preimage_discrete n := ⟨⟨(p, q), by simpa using h⟩⟩
      have hleg :
          HomologicalComplex.ιTensorObj L Q p q n h ≫ m = s.ι.app t := by
        simpa [t, tensor_preimage_cocone] using hm t
      have hdesc :
          HomologicalComplex.ιTensorObj L Q p q n h ≫
              HomologicalComplex.mapBifunctorDesc
                (K₁ := L) (K₂ := Q) (F := curriedTensor (ModuleCat R))
                (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
                (fun p q h ↦ s.ι.app ⟨⟨(p, q), by simpa using h⟩⟩) =
            s.ι.app t := by
        simpa [t, tensor_preimage_cocone] using
          (HomologicalComplex.ι_mapBifunctorDesc
            (K₁ := L) (K₂ := Q) (F := curriedTensor (ModuleCat R))
            (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
            (f := fun p q h ↦ s.ι.app ⟨⟨(p, q), by simpa using h⟩⟩)
            p q h)
      exact hleg.trans hdesc.symm)

/-- Helper for Lemma 15.59.7: every tensor degree is canonically the direct sum of its pair-indexed
summands. -/
private noncomputable def tensor_degree_iso_directSum
    (L Q : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    (HomologicalComplex.tensorObj L Q).X n ≅
      ModuleCat.of R (tensor_degree_directSum_module (R := R) L Q n) := by
  let Z := tensor_degree_summands (R := R) L Q n
  let e :
      (HomologicalComplex.tensorObj L Q).X n ≅ colimit (tensor_preimage_diagram (R := R) L Q n) :=
    (tensor_preimage_cocone_isColimit (R := R) L Q n).coconePointUniqueUpToIso
      (colimit.isColimit (tensor_preimage_diagram (R := R) L Q n))
  exact e ≪≫ (Sigma.isoColimit (tensor_preimage_diagram (R := R) L Q n)).symm ≪≫
    ModuleCat.coprodIsoDirectSum (R := R) Z

/-- Helper for Lemma 15.59.7: under the direct-sum model of a tensor degree, each `ιTensorObj`
becomes the corresponding `DirectSum.lof`. -/
private theorem ιTensorObj_tensor_degree_iso_directSum_hom
    (L Q : CochainComplex (ModuleCat R) ℤ) (p q n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj L Q p q n h ≫
        (tensor_degree_iso_directSum (R := R) L Q n).hom =
      ModuleCat.ofHom
        (DirectSum.lof R (tensor_degree_preimage n)
          (tensor_degree_summands_type (R := R) L Q n)
          (tensor_degree_index p q n h)) := by
  let Z := tensor_degree_summands (R := R) L Q n
  let s : tensor_degree_preimage_discrete n :=
    ⟨tensor_degree_index p q n h⟩
  let e :
      (HomologicalComplex.tensorObj L Q).X n ≅ colimit (tensor_preimage_diagram (R := R) L Q n) :=
    (tensor_preimage_cocone_isColimit (R := R) L Q n).coconePointUniqueUpToIso
      (colimit.isColimit (tensor_preimage_diagram (R := R) L Q n))
  -- Compare the tensor summand injection with the chosen colimit comparison `e`.
  have hcolim :
      HomologicalComplex.ιTensorObj L Q p q n h ≫ e.hom =
        colimit.ι (tensor_preimage_diagram (R := R) L Q n) s := by
    simpa [s, e, tensor_preimage_cocone] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (tensor_preimage_cocone_isColimit (R := R) L Q n)
        (colimit.isColimit (tensor_preimage_diagram (R := R) L Q n)) s
  have hsigma :
      colimit.ι (tensor_preimage_diagram (R := R) L Q n) s ≫
          (Sigma.isoColimit (tensor_preimage_diagram (R := R) L Q n)).inv ≫
            (ModuleCat.coprodIsoDirectSum (R := R) Z).hom =
        Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := by
    -- Rewrite the coproduct-colimit comparison before the final direct-sum identification.
    change
      ((colimit.ι (tensor_preimage_diagram (R := R) L Q n) s ≫
          (Sigma.isoColimit (tensor_preimage_diagram (R := R) L Q n)).inv) ≫
            (ModuleCat.coprodIsoDirectSum (R := R) Z).hom) =
        Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom
    rw [Sigma.ι_isoColimit_inv]
    change
      Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom =
        Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom
    rfl
  -- Then pass through the coproduct colimit and the standard `ModuleCat` direct-sum model.
  calc
    HomologicalComplex.ιTensorObj L Q p q n h ≫
        (tensor_degree_iso_directSum (R := R) L Q n).hom
      = Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := by
          -- Expand the chosen comparison isomorphism, then rewrite through the colimit and Sigma
          -- coproduct comparisons.
          have hDirect :
              HomologicalComplex.ιTensorObj L Q p q n h ≫
                  (tensor_degree_iso_directSum (R := R) L Q n).hom =
                HomologicalComplex.ιTensorObj L Q p q n h ≫ e.hom ≫
                  (Sigma.isoColimit (tensor_preimage_diagram (R := R) L Q n)).inv ≫
                    (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := by
            rfl
          have hcolim' :
              HomologicalComplex.ιTensorObj L Q p q n h ≫ e.hom ≫
                  (Sigma.isoColimit (tensor_preimage_diagram (R := R) L Q n)).inv ≫
                    (ModuleCat.coprodIsoDirectSum (R := R) Z).hom =
                colimit.ι (tensor_preimage_diagram (R := R) L Q n) s ≫
                  (Sigma.isoColimit (tensor_preimage_diagram (R := R) L Q n)).inv ≫
                    (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := by
            -- Reassociate once, then rewrite the tensor summand map through the chosen colimit
            -- comparison `e`.
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ k ≫
                  (Sigma.isoColimit (tensor_preimage_diagram (R := R) L Q n)).inv ≫
                    (ModuleCat.coprodIsoDirectSum (R := R) Z).hom)
                hcolim
          calc
            HomologicalComplex.ιTensorObj L Q p q n h ≫
                (tensor_degree_iso_directSum (R := R) L Q n).hom =
              HomologicalComplex.ιTensorObj L Q p q n h ≫ e.hom ≫
                (Sigma.isoColimit (tensor_preimage_diagram (R := R) L Q n)).inv ≫
                  (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := hDirect
            _ = Sigma.ι Z s.as ≫ (ModuleCat.coprodIsoDirectSum (R := R) Z).hom := by
                exact hcolim'.trans hsigma
    _ = ModuleCat.ofHom
          (DirectSum.lof R (tensor_degree_preimage n)
            (tensor_degree_summands_type (R := R) L Q n) s.as) := by
          simpa [Z] using
            (ModuleCat.ι_coprodIsoDirectSum_hom (R := R) (Z := Z) s.as)

/-- Helper for Lemma 15.59.7: a degree `i ≤ b` lies in the image of the upper-truncation
embedding `m ↦ b - m`. -/
private theorem embeddingUpIntLE_toNat_sub_eq
    (b i : ℤ) (hi : i ≤ b) :
    (ComplexShape.embeddingUpIntLE b).f (Int.toNat (b - i)) = i := by
  -- The retained upper-truncation range is indexed by the nonnegative difference `b - i`.
  dsimp [ComplexShape.embeddingUpIntLE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.59.7: strictly below the cutoff, upper truncation keeps the original
term. -/
private noncomputable def truncLE_term_iso_of_lt
    (L : CochainComplex (ModuleCat R) ℤ) (b i : ℤ) (hi : i < b) :
    (L.truncLE b).X i ≅ L.X i :=
  let j : ℕ := Int.toNat (b - i)
  let hj : (ComplexShape.embeddingUpIntLE b).f j = i :=
    embeddingUpIntLE_toNat_sub_eq b i (le_of_lt hi)
  let hboundary : ¬ (ComplexShape.embeddingUpIntLE b).BoundaryLE j := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    intro hj0
    have : b = i := by
      simpa [j, hj0, ComplexShape.embeddingUpIntLE] using hj
    omega
  L.truncLEXIso (e := ComplexShape.embeddingUpIntLE b) hj hboundary

/-- Helper for Lemma 15.59.7: at the cutoff, upper truncation keeps the cycles object. -/
private noncomputable def truncLE_term_iso_cycles
    (L : CochainComplex (ModuleCat R) ℤ) (b : ℤ) :
    (L.truncLE b).X b ≅ L.cycles b :=
  let hi' : (ComplexShape.embeddingUpIntLE b).f 0 = b := by
    simp [ComplexShape.embeddingUpIntLE]
  let hboundary : (ComplexShape.embeddingUpIntLE b).BoundaryLE 0 := by
    simpa using (ComplexShape.boundaryLE_embeddingUpIntLE_iff b 0).2 rfl
  L.truncLEXIsoCycles (e := ComplexShape.embeddingUpIntLE b) hi' hboundary

/-- Helper for Lemma 15.59.7: strictly below the cutoff, the component of `L.ιTruncLE b`
is the standard retained-term identification. -/
private theorem ιTruncLE_f_eq_term_iso_of_lt
    (L : CochainComplex (ModuleCat R) ℤ) (b i : ℤ) (hi : i < b) :
    (L.ιTruncLE b).f i = (truncLE_term_iso_of_lt (R := R) L b i hi).hom := by
  let e := ComplexShape.embeddingUpIntLE b
  let j : ℕ := Int.toNat (b - i)
  have hj : e.f j = i := embeddingUpIntLE_toNat_sub_eq b i (le_of_lt hi)
  have hboundary : ¬ e.BoundaryLE j := by
    -- Strictly below the cutoff, the chosen index is not the boundary index of the truncation.
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    intro hj0
    have : b = i := by
      simpa [e, j, hj0, ComplexShape.embeddingUpIntLE] using hj
    omega
  -- Route correction: read the component from the dual `πTruncGE` formula and then unop it.
  apply Quiver.Hom.op_inj
  change ((L.op.πTruncGE e.op).f i) =
    (L.op.truncGEXIso e.op hj (by simpa using hboundary)).inv
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [e.op.liftExtend_f (L.op.restrictionToTruncGE' e.op)
      (L.op.restrictionToTruncGE'_hasLift e.op) hj]
  rw [L.op.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e.op hj (by simpa using hboundary)]
  simp [HomologicalComplex.truncGEXIso, Category.assoc]
  rfl

/-- Helper for Lemma 15.59.7: at the cutoff degree, the component of `L.ιTruncLE b`
is the cycles inclusion under the standard cutoff-term identification. -/
private theorem ιTruncLE_f_eq_term_iso_cycles
    (L : CochainComplex (ModuleCat R) ℤ) (b : ℤ) :
    (L.ιTruncLE b).f b = (truncLE_term_iso_cycles (R := R) L b).hom ≫ L.iCycles b := by
  let e := ComplexShape.embeddingUpIntLE b
  let hi' : e.f 0 = b := by
    simpa [e, ComplexShape.embeddingUpIntLE] using
      (embeddingUpIntLE_toNat_sub_eq b b le_rfl)
  have hi : e.BoundaryLE 0 := by
    simpa [e] using (ComplexShape.boundaryLE_embeddingUpIntLE_iff b 0).2 rfl
  -- Route correction: read the cutoff component from the dual `πTruncGE` boundary formula, then
  -- transport it across the canonical `opcycles`/`cycles` comparison.
  apply Quiver.Hom.op_inj
  change ((L.op.πTruncGE e.op).f b) =
    ((truncLE_term_iso_cycles (R := R) L b).hom ≫ L.iCycles b).op
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [e.op.liftExtend_f (L.op.restrictionToTruncGE' e.op)
      (L.op.restrictionToTruncGE'_hasLift e.op) hi']
  rw [L.op.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e.op hi' (by simpa using hi)]
  simp [Category.assoc]
  change (L.op.pOpcycles b ≫
      ((L.op.truncGE'XIsoOpcycles e.op hi' (by simpa using hi)).inv ≫
        (((L.op.truncGE' e.op).extendXIso e.op hi').inv))) =
    (L.sc b).iCycles.op ≫ (truncLE_term_iso_cycles (R := R) L b).hom.op
  rw [← (L.sc b).op_pOpcycles_opcyclesOpIso_hom]
  have hcut :
      (L.opcyclesOpIso b).hom ≫ (truncLE_term_iso_cycles (R := R) L b).hom.op =
        (L.op.truncGE'XIsoOpcycles e.op hi' (by simpa using hi)).inv ≫
          (((L.op.truncGE' e.op).extendXIso e.op hi').inv) := by
    simp [truncLE_term_iso_cycles, CochainComplex.truncLE, HomologicalComplex.truncLEXIsoCycles,
      HomologicalComplex.truncGEXIsoOpcycles, HomologicalComplex.opcyclesOpIso, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    rfl
  simpa [HomologicalComplex.opcyclesOpIso, Category.assoc] using
    congrArg (fun f ↦ L.op.pOpcycles b ≫ f) hcut.symm

/-- Helper for Lemma 15.59.7: every upper truncation of an acyclic complex is again acyclic. -/
private theorem truncLE_acyclic_of_acyclic
    {L : CochainComplex (ModuleCat R) ℤ}
    (hL : L.Acyclic) (b : ℤ) :
    (L.truncLE b).Acyclic := by
  -- Route correction: transfer exactness through the canonical quasi-isomorphism
  -- `L.truncLE b ⟶ L` instead of unfolding the truncation differential.
  rw [HomologicalComplex.acyclic_iff] at hL ⊢
  have hLE : L.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    -- Acyclicity forces vanishing homology in every degree, so any upper bound works.
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact hL n)
  letI : L.IsLE b := hLE
  intro n
  -- Exactness pulls back along the quasi-isomorphism `L.ιTruncLE b`.
  exact (exactAt_iff_of_quasiIsoAt (L.ιTruncLE b) n).2 (hL n)

/-- Helper for Lemma 15.59.7: a boundary produced after upper truncation pushes forward to a
boundary in the original tensor complex. -/
private theorem tensor_boundary_descends_from_truncLE
    (K : CochainComplex (ModuleCat R) ℤ)
    {L : CochainComplex (ModuleCat R) ℤ} [_h : HomologicalComplex.HasTensor L K]
    (n b : ℤ)
    {z' : (HomologicalComplex.tensorObj (L.truncLE b) K).X n}
    {z : (HomologicalComplex.tensorObj L K).X n}
    (hz : (((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f n).hom z' = z))
    (hb :
      ∃ y' : (HomologicalComplex.tensorObj (L.truncLE b) K).X (n - 1),
        ((HomologicalComplex.tensorObj (L.truncLE b) K).d (n - 1) n).hom y' = z') :
    ∃ y : (HomologicalComplex.tensorObj L K).X (n - 1),
      ((HomologicalComplex.tensorObj L K).d (n - 1) n).hom y = z := by
  rcases hb with ⟨y', hy'⟩
  refine ⟨((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f (n - 1)).hom y', ?_⟩
  -- Apply the degree-`n - 1 → n` naturality square for `tensorHom`.
  have hcomm :=
    (HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).comm (n - 1) n
  have hcomm_apply :
      (((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f (n - 1) ≫
          (HomologicalComplex.tensorObj L K).d (n - 1) n).hom y') =
        (((HomologicalComplex.tensorObj (L.truncLE b) K).d (n - 1) n ≫
          (HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f n).hom y') := by
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hcomm) y'
  -- Evaluate the commutative square on `y'` and rewrite the boundary upstairs to the target.
  change
    (((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f (n - 1) ≫
        (HomologicalComplex.tensorObj L K).d (n - 1) n).hom y') = z
  calc
    (((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f (n - 1) ≫
        (HomologicalComplex.tensorObj L K).d (n - 1) n).hom y')
      = (((HomologicalComplex.tensorObj (L.truncLE b) K).d (n - 1) n ≫
            (HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f n).hom y') := hcomm_apply
    _ = ((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f n).hom
          (((HomologicalComplex.tensorObj (L.truncLE b) K).d (n - 1) n).hom y') := rfl
    _ = ((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f n).hom z' := by rw [hy']
    _ = z := hz

/-- Helper for Lemma 15.59.7: every tensor cocycle already comes from some upper truncation of the
left factor. -/
private theorem tensor_cycle_factors_through_truncLE
    (L Q : CochainComplex (ModuleCat R) ℤ)
    (n : ℤ) (z : (HomologicalComplex.tensorObj L Q).X n)
    (hz : ((HomologicalComplex.tensorObj L Q).d n (n + 1)).hom z = 0) :
    ∃ b : ℤ, ∃ z' : (HomologicalComplex.tensorObj (L.truncLE b) Q).X n,
      ((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 Q)).f n).hom z' = z ∧
        ((HomologicalComplex.tensorObj (L.truncLE b) Q).d n (n + 1)).hom z' = 0 := by
  -- TODO: use `tensor_degree_iso_directSum` to choose a finite support cutoff `b`, then rebuild a
  -- preimage in `(L.truncLE b) ⊗ Q` coordinatewise via
  -- `ιTruncLE_f_eq_term_iso_of_lt` and `ιTruncLE_f_eq_term_iso_cycles`.
  let _ := hz
  sorry

/-- Helper for Lemma 15.59.7: the tensor bicomplex whose total complex is the ordinary tensor
product complex. -/
private abbrev tensor_bicomplex
    (L Q : CochainComplex (ModuleCat R) ℤ) :
    HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj L).obj Q

/-- Helper for Lemma 15.59.7: if the left factor vanishes above the cutoff, then the
corresponding tensor-bicomplex term is zero. -/
private theorem tensor_bicomplex_isZero_of_left_strictlyLE
    {L Q : CochainComplex (ModuleCat R) ℤ} {b p q : ℤ}
    [L.IsStrictlyLE b] (hp : b < p) :
    IsZero ((tensor_bicomplex (R := R) L Q).X p |>.X q) := by
  -- The left tensor factor already vanishes in degree `p`, so tensoring with it gives zero.
  have hLzero : IsZero (L.X p) := L.isZero_of_isStrictlyLE b p hp
  let F : ModuleCat R ⥤ ModuleCat R := (curriedTensor (ModuleCat R)).flip.obj (Q.X q)
  change IsZero (F.obj (L.X p))
  exact F.map_isZero hLzero

/-- Helper for Lemma 15.59.7: if the right factor vanishes above degree `0`, then the
corresponding tensor-bicomplex term is zero. -/
private theorem tensor_bicomplex_isZero_of_right_strictlyLE_zero
    {L Q : CochainComplex (ModuleCat R) ℤ} {p q : ℤ}
    [Q.IsStrictlyLE 0] (hq : 0 < q) :
    IsZero ((tensor_bicomplex (R := R) L Q).X p |>.X q) := by
  -- The right tensor factor already vanishes in degree `q`, so the whole tensor term is zero.
  have hQzero : IsZero (Q.X q) := Q.isZero_of_isStrictlyLE 0 q hq
  let F : ModuleCat R ⥤ ModuleCat R := (curriedTensor (ModuleCat R)).obj (L.X p)
  change IsZero (F.obj (Q.X q))
  exact F.map_isZero hQzero

/-- Helper for Lemma 15.59.7: strict upper bounds on the two tensor factors force only finitely
many nonzero tensor-bicomplex terms on each antidiagonal. -/
private theorem tensor_bicomplex_has_finite_antidiagonal_support_of_strictlyLE
    (L Q : CochainComplex (ModuleCat R) ℤ)
    (b : ℤ) [L.IsStrictlyLE b] [Q.IsStrictlyLE 0] :
    ∀ n : ℤ,
      { p : ℤ | ¬ IsZero ((tensor_bicomplex (R := R) L Q).X p |>.X (n - p)) }.Finite := by
  intro n
  -- Any nonzero term on the antidiagonal `p + (n - p) = n` must satisfy `n ≤ p ≤ b`.
  refine (Set.finite_Icc n b).subset ?_
  intro p hp
  constructor
  · by_contra hpn
    have hq : 0 < n - p := by omega
    have hzero :
        IsZero ((tensor_bicomplex (R := R) L Q).X p |>.X (n - p)) :=
      tensor_bicomplex_isZero_of_right_strictlyLE_zero (R := R) (L := L) (Q := Q) hq
    exact hp hzero
  · by_contra hpb
    have hpb' : b < p := lt_of_not_ge hpb
    have hzero :
        IsZero ((tensor_bicomplex (R := R) L Q).X p |>.X (n - p)) :=
      tensor_bicomplex_isZero_of_left_strictlyLE (R := R) (L := L) (Q := Q) hpb'
    exact hp hzero

/-- Helper for Lemma 15.59.7: totalizing the local tensor bicomplex recovers the usual tensor
product complex. -/
private noncomputable def tensor_bicomplex_total_iso_tensorObj
    (L Q : CochainComplex (ModuleCat R) ℤ) :
    HomologicalComplex₂.total (tensor_bicomplex (R := R) L Q) (ComplexShape.up ℤ) ≅
      HomologicalComplex.tensorObj L Q := by
  -- Both sides are the same tensor-totalization construction.
  exact Iso.refl _

/-- Helper for Lemma 15.59.7: a fixed row of the tensor bicomplex is just right tensoring the
left complex by the corresponding term of the right complex. -/
private noncomputable def tensor_bicomplex_row_iso_tensorRight
    (L Q : CochainComplex (ModuleCat R) ℤ) (q : ℤ) :
    (tensor_bicomplex (R := R) L Q).flip.X q ≅
      (((CategoryTheory.MonoidalCategory.tensorRight (Q.X q)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) := by
  -- After flipping, the `q`-th row is definitionally the fixed-right tensor image of `L`.
  exact Iso.refl _

/-- Helper for Lemma 15.59.7: every second-page-one term of the tensor bicomplex vanishes when the
left factor is acyclic and the right factor is termwise flat. -/
private theorem tensor_bicomplex_second_pageOne_isZero_of_acyclic_of_termwiseFlat
    (L Q : CochainComplex (ModuleCat R) ℤ)
    (hL : L.Acyclic) (hFlat : Q.IsTermwiseFlat)
    (p q : ℤ) :
    IsZero (secondDoubleComplexPageOne (tensor_bicomplex (R := R) L Q) p q) := by
  let eRow :=
    tensor_bicomplex_row_iso_tensorRight (R := R) L Q p
  have hRow :
      (((CategoryTheory.MonoidalCategory.tensorRight (Q.X p)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).Acyclic :=
    mapHomologicalComplex_acyclic_of_tensorRight_flat (R := R) L hL (Q.X p) (hFlat p)
  have hRow' :
      ((tensor_bicomplex (R := R) L Q).flip.X p).Acyclic :=
    acyclic_of_iso (R := R) eRow.symm hRow
  -- The second page-one term is the corresponding row homology object.
  change IsZero (((tensor_bicomplex (R := R) L Q).flip.X p).homology q)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact hRow' q

/-- Helper for Lemma 15.59.7: once the left factor is bounded above, the tensor totalization is
acyclic by the source spectral-sequence argument. -/
private theorem tensor_boundedAbove_acyclic_of_acyclic_of_strictlyLE_zero_of_termwiseFlat
    (L Q : CochainComplex (ModuleCat R) ℤ)
    (b : ℤ) (hL : L.Acyclic) [L.IsStrictlyLE b] [Q.IsStrictlyLE 0]
    (hFlat : Q.IsTermwiseFlat) :
    (HomologicalComplex.tensorObj L Q).Acyclic := by
  -- TODO: use the new finite-antidiagonal-support lemma above to build the local second
  -- filtration on `Tot(tensor_bicomplex L Q)`, apply `FilteredComplex.pageOneIso` to identify
  -- its `E₁`-page with `secondDoubleComplexPageOne`, and then feed the resulting page-one
  -- vanishing into `FilteredComplex.cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations`.
  let _ := tensor_bicomplex_has_finite_antidiagonal_support_of_strictlyLE
    (R := R) L Q b
  let _ := hL
  let _ := hFlat
  sorry

/-- Helper for Lemma 15.59.7: once the bounded-above right factor is shifted so that its top
degree is `0`, the remaining proof follows the source route by truncating the acyclic left
factor. -/
private theorem acyclic_tensor_of_acyclic_of_strictlyLE_zero_of_termwiseFlat
    (L Q : CochainComplex (ModuleCat R) ℤ)
    (hL : L.Acyclic) [Q.IsStrictlyLE 0]
    (hFlat : Q.IsTermwiseFlat) :
    (HomologicalComplex.tensorObj L Q).Acyclic := by
  -- Route correction: now that the two structural truncation lemmas isolate the real blockers, the
  -- source argument itself is short: factor a cycle through `L.truncLE b`, kill it upstairs by
  -- bounded-above acyclicity, and push the resulting boundary back down.
  rw [HomologicalComplex.acyclic_iff]
  intro n
  have hprev : (ComplexShape.up ℤ).prev n = n - 1 := by
    exact ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  have hnext : (ComplexShape.up ℤ).next n = n + 1 := by
    exact ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1)]
  · rw [ShortComplex.exact_iff_of_hasForget]
    intro z hz
  -- Lift the given cycle to a cocycle on some bounded-above truncation of the left factor.
    rcases tensor_cycle_factors_through_truncLE (R := R) L Q n z hz with
      ⟨b, z', hz', hz'closed⟩
    have hTruncAcyclic : (L.truncLE b).Acyclic :=
      truncLE_acyclic_of_acyclic (R := R) hL b
    have hTruncStrict : (L.truncLE b).IsStrictlyLE b := by
      infer_instance
    letI : (L.truncLE b).IsStrictlyLE b := hTruncStrict
    have hTensorTruncAcyclic :
        (HomologicalComplex.tensorObj (L.truncLE b) Q).Acyclic :=
      tensor_boundedAbove_acyclic_of_acyclic_of_strictlyLE_zero_of_termwiseFlat
        (R := R) (L.truncLE b) Q b hTruncAcyclic hFlat
    -- Exactness of the bounded-above tensor complex supplies a primitive for the lifted cocycle.
    rw [HomologicalComplex.acyclic_iff] at hTensorTruncAcyclic
    have hExactTrunc := hTensorTruncAcyclic n
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1)
      hprev
      hnext] at hExactTrunc
    rw [ShortComplex.exact_iff_of_hasForget] at hExactTrunc
    obtain ⟨y', hy'⟩ := hExactTrunc z' hz'closed
    -- Descend that primitive along `L.ιTruncLE b` to recover a primitive for the original cycle.
    exact tensor_boundary_descends_from_truncLE (R := R) (K := Q) (L := L) n b hz' ⟨y', hy'⟩
  · exact hprev
  · exact hnext

section

variable [CategoryTheory.LocallySmall.{0} (ModuleCat.{u} R)]
  [CategoryTheory.WellPowered.{0} (ModuleCat.{u} R)]
  [CategoryTheory.Limits.HasWidePullbacks (ModuleCat.{u} R)]
  [CategoryTheory.Limits.HasCoproducts (ModuleCat.{u} R)]
  [CategoryTheory.Limits.InitialMonoClass (ModuleCat.{u} R)]

/-- Lemma 15.59.7: a bounded above cochain complex of flat `R`-modules is K-flat, expressed in
the canonical owner predicate `P.IsKFlat`. -/
theorem isKFlat_of_boundedAbove_of_flat
    (P : CochainComplex (ModuleCat R) ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) P)
    (hFlat : P.IsTermwiseFlat) :
    P.IsKFlat := by
  -- Route correction: the new proof now runs through the shifted complex `Q := P⟦b⟧` with
  -- `Q.IsStrictlyLE 0`, then applies `acyclic_tensor_of_acyclic_of_strictlyLE_zero_of_termwiseFlat`
  -- and descends back across the tensor/shift isomorphism.
  rw [CochainComplex.isKFlat_iff]
  intro L _ hL
  obtain ⟨b, hLE⟩ := (CochainComplex.minus_iff (ModuleCat R) P).1 hbounded
  let Q : CochainComplex (ModuleCat R) ℤ := P⟦b⟧
  have hQLE : Q.IsStrictlyLE 0 := by
    letI : P.IsStrictlyLE b := hLE
    simpa [Q] using
      CochainComplex.isStrictlyLE_shift (K := P) b b 0 (by omega)
  letI : Q.IsStrictlyLE 0 := hQLE
  have hQFlat : Q.IsTermwiseFlat := by
    intro i
    -- Each shifted term is canonically the corresponding term of `P`.
    have hPi : Module.Flat R (P.X (i + b) : Type u) := hFlat (i + b)
    letI : Module.Flat R (P.X (i + b) : Type u) := hPi
    exact Module.Flat.of_linearEquiv
      ((P.shiftFunctorObjXIso b i (i + b) (by omega)).toLinearEquiv)
  have hTensorShift :
      (HomologicalComplex.tensorObj L Q).Acyclic :=
    acyclic_tensor_of_acyclic_of_strictlyLE_zero_of_termwiseFlat (R := R) L Q hL hQFlat
  have hTensorShifted :
      ((HomologicalComplex.tensorObj L P)⟦b⟧).Acyclic :=
    acyclic_of_iso (R := R)
      (tensor_right_shift_transport_iso (R := R) L P b)
      (by simpa [Q] using hTensorShift)
  exact acyclic_of_shift (R := R) (HomologicalComplex.tensorObj L P) b hTensorShifted

end

end CochainComplex

end
