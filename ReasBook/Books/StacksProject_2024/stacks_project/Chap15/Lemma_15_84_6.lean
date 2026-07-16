import Mathlib
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_84_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_61_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_72_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_74_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_74_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_3_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_84_4
import StacksProject_2024.stacks_project.Chap15.«15_74_0_2»

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open scoped DerivedTensorWithAlgebra
open scoped DerivedInternalHom
open scoped ModuleComplexInternalHom
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "MinusCpxA" => CochainComplex.minus (ModuleCat A)
local notation "BoundedCpxA" => CochainComplex.bounded (ModuleCat A)
local notation "PlusCpxA" => CochainComplex.plus (ModuleCat A)

/-
Domain-style sampling for Lemma 15.84.6:
- primary domain: derived internal-Hom in `D(A)` for a pseudo-coherent source and an
  `R`-perfect target, computed by the chapter owner `module_complex_internal_hom` through concrete
  cochain representatives over `A`;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.IsPerfectOver`,
  `isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative`,
  `CochainComplex.minus`,
  `CochainComplex.bounded`,
  `CochainComplex.plus`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `module_complex_internal_hom`,
  `RHom[H](K, L)`,
  `module_complex_internal_hom_represents_derivedInternalHom_of_boundedAbove_projective`,
  `CochainComplex.IsTermwiseFlat`;
- best owner abstraction: the primitive owner data live upstream on `K.IsPseudoCoherent` and
  `DerivedCategory.IsPerfectOver R L`, together with the representative criterion
  `isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative`; the concrete
  complexes `P`, `F`, and `⟪P, F⟫` here are therefore bridge/view data over those owners,
  expressed with the canonical boundedness owners
  `CochainComplex.minus`, `CochainComplex.bounded`, and `CochainComplex.plus`;
- primitive vs. derived:
  primitive data are the chosen bounded-above finite-free representative of `K` and bounded
  termwise `R`-flat finitely presented representative of `L`, with the latter obtained from
  `hL` through Lemma `15.84.4` under the ambient flat finite-presentation hypotheses on `R → A`;
  derived API is the resulting bounded-below flat finitely presented Hom-complex representative,
  together with the base-change and finite-presentation companion lemmas for fixed
  representatives;
- source/core/bridge triage:
  `source-facing`: the existential representative theorem immediately below;
  `core/canonical`: `DerivedCategory.IsPseudoCoherent`, `DerivedCategory.IsPerfectOver`,
    `CochainComplex.IsTermwiseFiniteFree`, `⟪P, F⟫`, and the canonical scalar-restriction and
    scalar-extension functors on cochain complexes;
  `bridge/view`: the fixed-representative Hom-complex theorems that follow.
-/

-- Proof sketch: unpack `hK : K.IsPseudoCoherent` to choose a bounded-above termwise finite-free
-- representative `P^•` of `K`, and use Lemma `15.84.4` under `[Module.Flat R A]` and
-- `[Algebra.FinitePresentation R A]` to choose a bounded termwise `R`-flat representative `F^•`
-- of `L` with finitely presented terms. The fixed-representative companion theorems below then
-- show that `Hom^•(P^•, F^•)` is bounded below, termwise `R`-flat after restriction of scalars,
-- has finitely presented terms, and computes the chosen derived internal-Hom object
-- `RHom[H](K, L)`.
/-- Lemma 15.84.6: let `R → A` be a flat ring map of finite presentation. If `K` is
pseudo-coherent and `L` is perfect over `R`, then one can choose a bounded-above termwise
finite-free representative `P^•` of `K` and a bounded termwise `R`-flat representative `F^•` of
`L` with finitely presented terms such that
`Hom^•(P^•, F^•)` is bounded below, termwise `R`-flat after restriction of scalars, has finitely
presented terms, and represents the chosen derived internal-Hom object
`R\mathrm{Hom}_A(K, L)`. -/
theorem exists_homComplex_termwiseFlat_finitePresentation_representative_of_isPseudoCoherent_of_isPerfectOver
    (H : MonoidalClosed DModA) {K L : DModA}
    (hK : K.IsPseudoCoherent)
    (hL : DerivedCategory.IsPerfectOver R L) :
    ∃ P F : CpxA,
      MinusCpxA P ∧
        P.IsTermwiseFiniteFree ∧
        IsIsomorphic (DerivedCategory.Q.obj P) K ∧
        BoundedCpxA F ∧
        CochainComplex.IsTermwiseFlat
          (((Functor.mapHomologicalComplex
            (ModuleCat.restrictScalars (algebraMap R A))
            (up ℤ)).obj F : CpxR)) ∧
        (∀ i : ℤ, Module.FinitePresentation A (F.X i)) ∧
        IsIsomorphic (DerivedCategory.Q.obj F) L ∧
        PlusCpxA ⟪P, F⟫ ∧
        CochainComplex.IsTermwiseFlat
          (((Functor.mapHomologicalComplex
            (ModuleCat.restrictScalars (algebraMap R A))
            (up ℤ)).obj ⟪P, F⟫ : CpxR)) ∧
        (∀ n : ℤ, Module.FinitePresentation A ((⟪P, F⟫).X n)) ∧
        IsIsomorphic (DerivedCategory.Q.obj ⟪P, F⟫) (RHom[H](K, L)) := by
  -- Proof comment: unpack pseudo-coherence into the fixed bounded-above finite-free source model
  -- required by the source proof.
  rcases hK with ⟨P, ⟨b, hPstrictLE⟩, hPfiniteFree, ⟨α, hαiso⟩⟩
  have hPbounded : MinusCpxA P := by
    exact (CochainComplex.minus_iff (ModuleCat A) P).2 ⟨b, hPstrictLE⟩
  have hPiso : IsIsomorphic (DerivedCategory.Q.obj P) K := by
    exact ⟨asIso α⟩
  -- Proof comment: use the earlier relative-perfectness criterion to choose the bounded termwise
  -- `R`-flat finitely presented target model.
  rcases
      (isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative
        (R := R) L).1 hL with
    ⟨F, hFflat, hFfinitePresentation, hFiso⟩
  rcases hFiso with ⟨eF⟩
  have hFiso' : IsIsomorphic (DerivedCategory.Q.obj F.obj) L := by
    exact ⟨eF.symm⟩
  -- Proof comment: the remaining work is exactly the fixed-representative computation for the
  -- Hom complex and the degreewise finite-presentation upgrade.
  have hHom :=
    homComplex_isBoundedBelowTermwiseFlatRepresentativeOverBase
      (H := H) (K := K) (L := L) P F.obj
      hPbounded hPfiniteFree hPiso F.property hFflat hFiso'
  have hHomFinitePresentation :=
    homComplex_term_finitePresentation_of_boundedAbove_of_bounded_of_termwiseFiniteFree
      P F.obj hPbounded hPfiniteFree F.property hFfinitePresentation
  exact
    ⟨P, F.obj, hPbounded, hPfiniteFree, hPiso, F.property, hFflat, hFfinitePresentation,
      hFiso', hHom.1, hHom.2.1, hHomFinitePresentation, hHom.2.2⟩

/-- Helper for Lemma 15.84.6: each term of a termwise finite-free complex is projective. -/
private theorem termwiseFiniteFree_term_projective
    (P : CpxA)
    (hPfiniteFree : P.IsTermwiseFiniteFree) :
    ∀ i : ℤ, Projective (P.X i) := by
  -- Proof comment: finite free modules are projective, so the standard instance applies in each
  -- degree once the termwise finite-free structure is installed.
  intro i
  let _ : P.IsTermwiseFiniteFree := hPfiniteFree
  infer_instance

/-- Helper for Lemma 15.84.6: a bounded-above termwise finite-free complex packages as a
`ProjectiveMinus` complex. -/
private noncomputable abbrev termwiseFiniteFree_projective_minus
    (P : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree) :
    CochainComplex.ProjectiveMinus (ModuleCat A) :=
  ⟨⟨P, hPbounded⟩, termwiseFiniteFree_term_projective P hPfiniteFree⟩

/-- Helper for Lemma 15.84.6: the Chapter `15.74.2` cohomology comparison applies to a
bounded-above termwise finite-free source after packaging it as `ProjectiveMinus`. -/
private noncomputable abbrev termwiseFiniteFree_homologyAddEquivShiftedHom
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (n : ℤ) :
    (CochainComplex.HomComplex P F).homology n ≃+
      ShiftedHom (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F) n :=
  CochainComplex.ProjectiveMinus.homologyAddEquivShiftedHom
    (termwiseFiniteFree_projective_minus P hPbounded hPfiniteFree) F n

/-- Helper for Lemma 15.84.6: transporting morphisms across source and target isomorphisms is
additive in the derived category. -/
private theorem iso_hom_congr_add_equiv_map_add
    {X Y X₁ Y₁ : DModA} (α : X ≅ X₁) (β : Y ≅ Y₁)
    (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- Proof comment: `Iso.homCongr` is composition with fixed isomorphisms, so additivity follows
  -- from bilinearity of composition in the preadditive derived category.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 15.84.6: source and target isomorphisms induce an additive equivalence on
the corresponding shifted-Hom groups. -/
private noncomputable def iso_hom_congr_add_equiv
    {X Y X₁ Y₁ : DModA} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) where
  toEquiv := α.homCongr β
  map_add' := iso_hom_congr_add_equiv_map_add α β

/-- Helper for Lemma 15.84.6: the chapter owner `⟪P, F⟫` is definitionally the standard
`CochainComplex.HomComplex P F`. -/
private theorem module_complex_internal_hom_eq_hom_complex
    (P F : CpxA) :
    ⟪P, F⟫ = CochainComplex.HomComplex P F :=
  rfl

/-- Helper for Lemma 15.84.6: outside the source-faithful window `a - n ≤ p ≤ b`, the degree-`p`
Hom summand contributing to `(⟪P, F⟫).X n` vanishes. -/
private theorem module_complex_internal_hom_degree_factor_isZero_outside_window
    (P F : CpxA) {a b n p : ℤ}
    (hPstrictLE : P.IsStrictlyLE b)
    (hFstrictGE : F.IsStrictlyGE a)
    (hp : p < a - n ∨ b < p) :
    IsZero ((ihom (P.X p)).obj (F.X (n + p))) := by
  -- Proof comment: if `p` lies below the interval, then the target degree `n + p` lies below the
  -- lower bound `a`; if `p` lies above the interval, then the source term already vanishes.
  rcases hp with hp | hp
  · have hnp_lt : n + p < a := by
      omega
    rw [CochainComplex.isStrictlyGE_iff] at hFstrictGE
    have hzeroF : IsZero (F.X (n + p)) := hFstrictGE (n + p) hnp_lt
    change IsZero ((ihom (P.X p)).obj (F.X (n + p)))
    infer_instance
  · rw [CochainComplex.isStrictlyLE_iff] at hPstrictLE
    have hzeroP : IsZero (P.X p) := hPstrictLE p hp
    change IsZero ((ihom (P.X p)).obj (F.X (n + p)))
    infer_instance

/-- Helper for Lemma 15.84.6: once `n < a - b`, every degreewise Hom summand contributing to
`(⟪P, F⟫).X n` is zero. -/
private theorem module_complex_internal_hom_degree_factor_isZero_below_lower_bound
    (P F : CpxA) {a b n p : ℤ}
    (hPstrictLE : P.IsStrictlyLE b)
    (hFstrictGE : F.IsStrictlyGE a)
    (hn : n < a - b) :
    IsZero ((ihom (P.X p)).obj (F.X (n + p))) := by
  -- Proof comment: below the global lower bound `a - b`, every integer `p` lies outside the
  -- finite window `a - n ≤ p ≤ b`, so the previous window-vanishing lemma applies.
  have hp : p < a - n ∨ b < p := by
    omega
  exact module_complex_internal_hom_degree_factor_isZero_outside_window
    P F hPstrictLE hFstrictGE hp

/-- Helper for Lemma 15.84.6: deleting zero factors outside a bounded interval identifies the
ambient product with the product over the interval subtype. -/
private noncomputable def pi_iso_subtype_of_isZero_off_interval
    (Z : ℤ → ModuleCat A) (l u : ℤ)
    (hzero : ∀ p : ℤ, p ∉ Set.Icc l u → IsZero (Z p)) :
    ∏ᶜ Z ≅ ∏ᶜ (fun p : Set.Icc l u ↦ Z p.1) := by
  refine
    ⟨Pi.lift (fun p : Set.Icc l u ↦ Pi.π Z p.1),
      Pi.lift (fun p : ℤ ↦
        if hp : p ∈ Set.Icc l u then
          Pi.π (fun q : Set.Icc l u ↦ Z q.1) ⟨p, hp⟩
        else
          (hzero p hp).to_ _),
      ?_,
      ?_⟩
  · -- Proof comment: after projecting back to one interval index, the inclusion and restriction
    -- maps recover the original interval coordinate.
    apply Pi.hom_ext
    intro p
    rw [Category.assoc, Pi.lift_π]
    simp only [dif_pos p.2]
  · -- Proof comment: for an ambient coordinate inside the interval we recover that coordinate,
    -- while outside the interval both routes are zero because the factor itself is zero.
    apply Pi.hom_ext
    intro p
    rw [Category.assoc, Pi.lift_π]
    by_cases hp : p ∈ Set.Icc l u
    · rw [Category.assoc, Pi.lift_π]
      simp only [dif_pos hp]
    · have hzp : IsZero (Z p) := hzero p hp
      simp only [dif_neg hp]
      simp [hzp.eq_zero_of_tgt (Pi.π Z p), hzp.eq_zero_of_tgt ((Pi.lift
        (fun q : Set.Icc l u ↦ Pi.π Z q.1)) ≫ hzp.to_ _)]

/-- Helper for Lemma 15.84.6: the degree-`n` term of the strict Hom complex is the product over
the finite source-faithful window `a - n ≤ p ≤ b`. -/
private noncomputable def module_complex_internal_hom_degree_iso_finite_window
    (P F : CpxA) {a b : ℤ}
    (hPstrictLE : P.IsStrictlyLE b)
    (hFstrictGE : F.IsStrictlyGE a)
    (n : ℤ) :
    (⟪P, F⟫).X n ≅
      ∏ᶜ (fun p : Set.Icc (a - n) b ↦ (ihom (P.X p.1)).obj (F.X (n + p.1))) := by
  -- Proof comment: first expose the ambient `ℤ`-indexed product description of degree `n`, then
  -- delete the zero factors that lie outside the bounded support window.
  refine (module_complex_internal_hom_piIso P F n).symm ≪≫
    pi_iso_subtype_of_isZero_off_interval
      (Z := fun p : ℤ ↦ (ihom (P.X p)).obj (F.X (n + p)))
      (l := a - n) (u := b) ?_
  intro p hp
  have hp' : p < a - n ∨ b < p := by
    rw [Set.mem_Icc] at hp
    omega
  exact module_complex_internal_hom_degree_factor_isZero_outside_window
    P F hPstrictLE hFstrictGE hp'

/-- Helper for Lemma 15.84.6: if the source module is finite free, then its internal-Hom into `N`
is a finite coordinate power of `N`. -/
private theorem ihom_finite_free_linearEquiv_fin_fun
    (M N : ModuleCat A)
    [Module.Free A M] [Module.Finite A M] :
    ∃ m : ℕ, Nonempty ((((ihom M).obj N : ModuleCat A) : Type u) ≃ₗ[A] (Fin m → N)) := by
  -- Proof comment: put the finite free source into a `Fin m` coordinate model and then use the
  -- standard equivalence `Hom_A(A^m, N) ≃ N^m`.
  rcases finite_free_linearEquiv_fin (R := A) (F := M) with ⟨m, ⟨eM⟩⟩
  refine ⟨m, ?_⟩
  refine ⟨(LinearEquiv.arrowCongr eM.symm (LinearEquiv.refl A N)).trans
    (LinearEquiv.piRing A N (Fin m) A)⟩

/-- Helper for Lemma 15.84.6: if `P` is bounded above and `F` is bounded, then the strict Hom
complex `⟪P, F⟫` is bounded below. -/
private theorem module_complex_internal_hom_plus_of_boundedAbove_of_bounded
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hFbounded : BoundedCpxA F) :
    PlusCpxA ⟪P, F⟫ := by
  obtain ⟨b, hPstrictLE⟩ := (CochainComplex.minus_iff (ModuleCat A) P).1 hPbounded
  obtain ⟨hFplus, _⟩ := (CochainComplex.bounded_iff (ModuleCat A) F).1 hFbounded
  obtain ⟨a, hFstrictGE⟩ := (CochainComplex.plus_iff (ModuleCat A) F).1 hFplus
  -- Proof comment: below degree `a - b`, every summand `Hom_A(P^p, F^{n + p})` vanishes because
  -- either `p` lies above the source bound `b` or the target degree `n + p` lies below `a`.
  refine (CochainComplex.plus_iff (ModuleCat A) ⟪P, F⟫).2 ?_
  refine ⟨a - b, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  let Z : ℤ → ModuleCat A := fun p ↦ (ihom (P.X p)).obj (F.X (n + p))
  letI : ∀ p : ℤ, IsZero (Z p) := by
    intro p
    -- Proof comment: the degree bound `n < a - b` forces each index `p` outside the support
    -- window, so each product factor vanishes by the previous helper.
    simpa [Z] using
      module_complex_internal_hom_degree_factor_isZero_below_lower_bound
        P F hPstrictLE hFstrictGE (p := p) hn
  have hzeroPi : IsZero (∏ᶜ Z) := by
    infer_instance
  -- Proof comment: transport the product-side vanishing back across the canonical degreewise
  -- decomposition of `⟪P, F⟫`.
  exact hzeroPi.of_iso (module_complex_internal_hom_piIso P F n)

/-- Helper for Lemma 15.84.6: the strict evaluation map from the concrete Hom complex
`⟪P, F⟫` back to `F`. -/
private noncomputable abbrev strict_hom_complex_evaluation
    (P F : CpxA) :
    ⟪P, F⟫ ⊗ P ⟶ F :=
  (β_ ⟪P, F⟫ P).hom ≫ (ihom.ev P).app F

/-- Helper for Lemma 15.84.6: after passing the strict evaluation map through `Q`, tensoring with
the chosen source isomorphism `Q(P) ≅ K`, and transporting the target by `Q(F) ≅ L`, we obtain a
derived evaluation morphism `Q(⟪P,F⟫) ⊗^L K ⟶ L`. -/
private noncomputable def strict_hom_complex_evaluation_derived
    (H : MonoidalClosed DModA)
    (P F : CpxA) {K L : DModA}
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eF : DerivedCategory.Q.obj F ≅ L) :
    DerivedCategory.Q.obj ⟪P, F⟫ ⊗[A]^L K ⟶ L :=
  (derivedTensorProductMap H eP.inv).app (DerivedCategory.Q.obj ⟪P, F⟫) ≫
    (derivedCategory_tensorObj_iso_derivedTensorProduct
      (DerivedCategory.Q.obj ⟪P, F⟫) (DerivedCategory.Q.obj P)).inv ≫
        (Functor.Monoidal.μIso
          (DerivedCategory.Q : CpxA ⥤ DModA) ⟪P, F⟫ P).hom ≫
            DerivedCategory.Q.map (strict_hom_complex_evaluation P F) ≫
              eF.hom

/-- Helper for Lemma 15.84.6: the model-level comparison morphism
`Q(⟪P,F⟫) ⟶ RHom_A(K,L)` obtained by transposing the transported strict evaluation map under
`- ⊗^L K ⊣ RHom_A(K,-)`. -/
private noncomputable def strict_hom_complex_comparison
    (H : MonoidalClosed DModA)
    (P F : CpxA) {K L : DModA}
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eF : DerivedCategory.Q.obj F ≅ L) :
    DerivedCategory.Q.obj ⟪P, F⟫ ⟶ RHom[H](K, L) :=
  (H.derivedTensorAdj K).homEquiv _ _
    (strict_hom_complex_evaluation_derived H P F eP eF)

/-- Helper for Lemma 15.84.6: by construction, the mate of the strict Hom-complex comparison is
exactly the transported derived evaluation morphism. -/
private theorem strict_hom_complex_comparison_def
    (H : MonoidalClosed DModA)
    (P F : CpxA) {K L : DModA}
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eF : DerivedCategory.Q.obj F ≅ L) :
    ((H.derivedTensorAdj K).homEquiv _ _).symm
        (strict_hom_complex_comparison H P F eP eF) =
      strict_hom_complex_evaluation_derived H P F eP eF := by
  -- Proof comment: this is the defining `homEquiv`/`symm` cancellation for the chosen mate.
  simp [strict_hom_complex_comparison]

/-- Helper for Lemma 15.84.6: the cohomology of the concrete Hom complex agrees degreewise with
the cohomology of the chosen derived internal-Hom object after transporting along the selected
source and target isomorphisms. -/
private noncomputable def termwiseFiniteFree_homologyAddEquiv_derivedHom
    (H : MonoidalClosed DModA)
    (P F : CpxA) {K L : DModA}
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eF : DerivedCategory.Q.obj F ≅ L)
    (n : ℤ) :
    (CochainComplex.HomComplex P F).homology n ≃+
      ((DerivedCategory.homologyFunctor (ModuleCat A) n).obj (RHom[H](K, L))) :=
  let e₁ :
      (CochainComplex.HomComplex P F).homology n ≃+
        ShiftedHom (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F) n :=
    termwiseFiniteFree_homologyAddEquivShiftedHom P F hPbounded hPfiniteFree n
  let e₂ :
      ShiftedHom (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F) n ≃+
        ShiftedHom K L n :=
    iso_hom_congr_add_equiv eP ((shiftFunctor DModA n).mapIso eF)
  let e₃ :
      ((DerivedCategory.homologyFunctor (ModuleCat A) n).obj (RHom[H](K, L))) ≃+
        ShiftedHom K L n :=
    (derivedHom_cohomology_iso_shiftedHom H K L n).toAddEquiv
  (e₁.trans e₂).trans e₃.symm

/-- Helper for Lemma 15.84.6: after translating the homology of the chosen `RHom` object to
shifted morphisms, the strict Hom-complex comparison agrees with the source-faithful transport of
Lemma `15.74.2`. -/
private theorem strict_hom_complex_comparison_homology_to_shiftedHom_eq
    (H : MonoidalClosed DModA)
    (P F : CpxA) {K L : DModA}
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eF : DerivedCategory.Q.obj F ≅ L)
    (n : ℤ) :
    ((derivedHom_cohomology_iso_shiftedHom H K L n).toAddEquiv : _ → _)
        ∘ ((DerivedCategory.homologyFunctor (ModuleCat A) n).map
          (strict_hom_complex_comparison H P F eP eF) : _ → _) =
      ((iso_hom_congr_add_equiv eP ((shiftFunctor DModA n).mapIso eF)).toEquiv : _ → _)
        ∘ ((termwiseFiniteFree_homologyAddEquivShiftedHom
          P F hPbounded hPfiniteFree n).toEquiv : _ → _) := by
  -- TODO: normalize the adjoint mate defining `strict_hom_complex_comparison` on the shifted-Hom
  -- side, then rewrite through `derivedHom_cohomology_iso_shiftedHom` and the source-side
  -- `termwiseFiniteFree_homologyAddEquivShiftedHom` owner from Lemma `15.74.2`.
  sorry

/-- Helper for Lemma 15.84.6: every cohomology map induced by the strict Hom-complex comparison
agrees with the packaged additive equivalence computing `RHom_A(K,L)` degreewise. -/
private theorem strict_hom_complex_comparison_homology_eq_transport
    (H : MonoidalClosed DModA)
    (P F : CpxA) {K L : DModA}
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eF : DerivedCategory.Q.obj F ≅ L)
    (n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat A) n).map
      (strict_hom_complex_comparison H P F eP eF) : _ → _) =
      (termwiseFiniteFree_homologyAddEquiv_derivedHom
        H P F hPbounded hPfiniteFree eP eF n : _ → _) := by
  -- Proof comment: conjugate the shifted-Hom-side normalization by the canonical cohomology
  -- equivalence for `RHom_A(K,L)`.
  ext x
  apply (derivedHom_cohomology_iso_shiftedHom H K L n).injective
  simpa [Function.comp, termwiseFiniteFree_homologyAddEquiv_derivedHom] using
    congrFun
      (strict_hom_complex_comparison_homology_to_shiftedHom_eq
        H P F hPbounded hPfiniteFree eP eF n) x

/-- Helper for Lemma 15.84.6: every cohomology map induced by the strict Hom-complex comparison
is bijective, because the transported source-level computation already identifies it with the
cohomology of `RHom_A(K,L)`. -/
private theorem strict_hom_complex_comparison_homology_bijective
    (H : MonoidalClosed DModA)
    (P F : CpxA) {K L : DModA}
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eF : DerivedCategory.Q.obj F ≅ L)
    (n : ℤ) :
    Function.Bijective
      ((DerivedCategory.homologyFunctor (ModuleCat A) n).map
        (strict_hom_complex_comparison H P F eP eF)) := by
  -- Proof comment: reduce bijectivity to the explicit additive equivalence identified in the
  -- previous transport lemma.
  rw [strict_hom_complex_comparison_homology_eq_transport
    H P F hPbounded hPfiniteFree eP eF n]
  exact
    (termwiseFiniteFree_homologyAddEquiv_derivedHom
      H P F hPbounded hPfiniteFree eP eF n).bijective

-- Proof sketch: `P` is bounded above and termwise finite free, while `F` is bounded and termwise
-- `R`-flat, so `Hom^•(P^•, F^•)` is bounded below and its degree-`n` terms are finite direct sums
-- of `R`-flat modules. The standard K-projective Hom-complex computation identifies
-- `Hom^•(P^•, F^•)` with the canonical chosen derived internal-Hom object `RHom[H](K, L)` in
-- `D(A)`.
/-- Companion bridge for Lemma 15.84.6: once `P^•` and `F^•` are already chosen as above, the
Hom complex `\mathrm{Hom}^\bullet(P^•, F^•)` is a bounded-below termwise `R`-flat representative
of `R\mathrm{Hom}_A(K, L)`. -/
theorem homComplex_isBoundedBelowTermwiseFlatRepresentativeOverBase
    (H : MonoidalClosed DModA) {K L : DModA}
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hPiso : IsIsomorphic (DerivedCategory.Q.obj P) K)
    (hFbounded : BoundedCpxA F)
    (hFflat :
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj F : CpxR)))
    (hFiso : IsIsomorphic (DerivedCategory.Q.obj F) L) :
    PlusCpxA ⟪P, F⟫ ∧
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj ⟪P, F⟫ : CpxR)) ∧
      IsIsomorphic (DerivedCategory.Q.obj ⟪P, F⟫) (RHom[H](K, L)) := by
  -- Route correction: this proof must compare cohomology of `⟪P, F⟫` with shifted derived Homs
  -- via Lemmas `15.74.2` and `15.74.0.2`, rather than using the later shortcut `15.99.4`.
  let _ : P.IsTermwiseFiniteFree := hPfiniteFree
  have hPlus : PlusCpxA ⟪P, F⟫ :=
    module_complex_internal_hom_plus_of_boundedAbove_of_bounded
      P F hPbounded hFbounded
  have hFlat :
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj ⟪P, F⟫ : CpxR)) := by
    obtain ⟨b, hPstrictLE⟩ := (CochainComplex.minus_iff (ModuleCat A) P).1 hPbounded
    obtain ⟨hFplus, _⟩ := (CochainComplex.bounded_iff (ModuleCat A) F).1 hFbounded
    obtain ⟨a, hFstrictGE⟩ := (CochainComplex.plus_iff (ModuleCat A) F).1 hFplus
    intro n
    -- Proof comment: replace the ambient `ℤ`-product for degree `n` by the finite window
    -- `a - n ≤ p ≤ b`, prove each factor is a finite coordinate power of a flat target term, and
    -- then transport flatness back through the resulting degreewise isomorphism.
    let eWindow :=
      module_complex_internal_hom_degree_iso_finite_window
        P F hPstrictLE hFstrictGE n
    let Z : Set.Icc (a - n) b → ModuleCat A :=
      fun p ↦ (ihom (P.X p.1)).obj (F.X (n + p.1))
    classical
    letI : Finite (Set.Icc (a - n) b) := (Set.finite_Icc (a - n) b).to_subtype
    letI : Fintype (Set.Icc (a - n) b) := Fintype.ofFinite (Set.Icc (a - n) b)
    have hFactorFlat :
        ∀ p : Set.Icc (a - n) b,
          Module.Flat R ((Z p : ModuleCat A) : Type u) := by
      intro p
      have hFlatTarget : Module.Flat R (F.X (n + p.1) : Type u) := by
        simpa using hFflat (n + p.1)
      obtain ⟨m, ⟨eFactor⟩⟩ :=
        ihom_finite_free_linearEquiv_fin_fun (M := P.X p.1) (N := F.X (n + p.1))
      let _ : Module.Flat R (Fin m → F.X (n + p.1)) := by infer_instance
      exact Module.Flat.of_linearEquiv (eFactor.restrictScalars R)
    have hWindowFlat : Module.Flat R ((∏ᶜ Z : ModuleCat A) : Type u) := by
      let _ : ∀ p : Set.Icc (a - n) b, Module.Flat R ((Z p : ModuleCat A) : Type u) := hFactorFlat
      let _ : Module.Flat R ((∀ p : Set.Icc (a - n) b, Z p) : Type u) := by infer_instance
      exact Module.Flat.of_linearEquiv ((ModuleCat.piIsoPi Z).toLinearEquiv.restrictScalars R)
    let _ : Module.Flat R ((∏ᶜ Z : ModuleCat A) : Type u) := hWindowFlat
    exact Module.Flat.of_linearEquiv (eWindow.toLinearEquiv.restrictScalars R)
  have hIso : IsIsomorphic (DerivedCategory.Q.obj ⟪P, F⟫) (RHom[H](K, L)) := by
    rcases hPiso with ⟨eP⟩
    rcases hFiso with ⟨eF⟩
    -- Proof comment: define the strict evaluation comparison `Q.obj ⟪P,F⟫ ⟶ RHom[H](K,L)` and
    -- detect it as an isomorphism on all cohomology groups using the transported `15.74.2` and
    -- `15.74.0.2` additive equivalences.
    have hcomparison :
        IsIso (strict_hom_complex_comparison H P F eP eF) := by
      refine
        (derivedCategory_isIso_iff_homology_map_isIso
          (ℬ := ModuleCat A)
          (strict_hom_complex_comparison H P F eP eF)).2 ?_
      intro n
      refine (CategoryTheory.isIso_iff_bijective _).2 ?_
      exact strict_hom_complex_comparison_homology_bijective
        H P F hPbounded hPfiniteFree eP eF n
    exact ⟨asIso (strict_hom_complex_comparison H P F eP eF)⟩
  exact ⟨hPlus, hFlat, hIso⟩

end

section

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

local notation "Aprime" => A ⊗[R] R'
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModAprime" => DerivedCategory (ModuleCat Aprime)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "CpxR'" => CochainComplex (ModuleCat R') ℤ
local notation "CpxAprime" => CochainComplex (ModuleCat Aprime) ℤ
local notation "MinusCpxA" => CochainComplex.minus (ModuleCat A)
local notation "BoundedCpxA" => CochainComplex.bounded (ModuleCat A)
local notation "PlusCpxA" => CochainComplex.plus (ModuleCat A)
local notation "PlusCpxAprime" => CochainComplex.plus (ModuleCat Aprime)
local instance commRingAprime : CommRing Aprime := by infer_instance
local instance algebraRprimeAprime : Algebra R' Aprime := by infer_instance
local instance algebraAAprime : Algebra A Aprime := by infer_instance

-- Proof sketch: extend scalars degreewise from `A` to `A' = A ⊗[R] R'`. Because `P` is termwise
-- finite free, internal Homs commute with this scalar extension termwise, and the resulting
-- complex stays bounded below and computes the canonical derived internal-Hom object over `A'` of
-- the base-changed representatives.
/-- After any base change `R → R'`, the scalar extension of `Hom^•(P^•, F^•)` to
`A' = A ⊗[R] R'` is bounded below. -/
theorem baseChange_homComplex_isBoundedBelow
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hFboundedBelow : PlusCpxA F) :
    PlusCpxAprime
      (((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A Aprime))
          (up ℤ)).obj ⟪P, F⟫ : CpxAprime)) := by
  -- TODO: first identify scalar extension of `⟪P, F⟫` with the Hom complex of the scalar-extended
  -- representatives, then transport bounded-below support across that complex isomorphism.
  let _ := hPbounded
  let _ := hPfiniteFree
  let _ := hFboundedBelow
  sorry

/-- After any base change `R → R'`, the scalar extension of `Hom^•(P^•, F^•)` to
`A' = A ⊗[R] R'` is termwise `R'`-flat after restriction of scalars. -/
theorem baseChange_homComplex_isTermwiseFlatOverBase
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hFbounded : BoundedCpxA F)
    (hFflat :
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj F : CpxR))) :
    CochainComplex.IsTermwiseFlat
      (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R' Aprime))
          (up ℤ)).obj
          (((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (algebraMap A Aprime))
              (up ℤ)).obj ⟪P, F⟫ : CpxAprime)) : CpxR')) :=
      by
  -- TODO: after the same scalar-extension/Hom-complex identification, prove degreewise that
  -- extending scalars preserves flatness of the finite direct sums appearing in each Hom degree.
  let _ := hPbounded
  let _ := hPfiniteFree
  let _ := hFbounded
  let _ := hFflat
  sorry

/-- After any base change `R → R'`, the scalar extension of `Hom^•(P^•, F^•)` to
`A' = A ⊗[R] R'` represents the derived internal-Hom of the actual derived base changes of the
objects represented by `P^•` and `F^•`. -/
theorem baseChange_homComplex_represents_derivedInternalHom
    (H' : MonoidalClosed DModAprime)
    {K L : DModA} (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hPiso : IsIsomorphic (DerivedCategory.Q.obj P) K)
    (hFbounded : BoundedCpxA F)
    (hFflat :
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj F : CpxR)))
    (hFiso : IsIsomorphic (DerivedCategory.Q.obj F) L) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (((Functor.mapHomologicalComplex
            (ModuleCat.extendScalars (algebraMap A Aprime))
            (up ℤ)).obj ⟪P, F⟫ : CpxAprime)))
      (RHom[H'](K ⊗[A]^L[Aprime], L ⊗[A]^L[Aprime])) := by
  -- TODO: use Lemma `15.61.2` to identify the scalar-extended representatives with the actual
  -- derived base changes, then transport the fixed-representative RHom computation across the
  -- scalar-extension/Hom-complex isomorphism.
  let _ := H'
  let _ := hPbounded
  let _ := hPfiniteFree
  let _ := hPiso
  let _ := hFbounded
  let _ := hFflat
  let _ := hFiso
  sorry

end

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "MinusCpxA" => CochainComplex.minus (ModuleCat A)
local notation "BoundedCpxA" => CochainComplex.bounded (ModuleCat A)

-- Proof sketch: because `P` is bounded above and termwise finite free while `F` is bounded, each
-- degree of `Hom^•(P^•, F^•)` is a finite direct sum of copies of finitely presented terms of
-- `F`; finite presentation is stable under finite direct sums.
/-- If `P^•` is bounded above and termwise finite free, and `F^•` is bounded with finitely
presented terms, then every degree of `Hom^•(P^•, F^•)` is a finitely presented `A`-module. -/
theorem homComplex_term_finitePresentation_of_boundedAbove_of_bounded_of_termwiseFiniteFree
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hFbounded : BoundedCpxA F)
    (hFfinitePresentation : ∀ i : ℤ, Module.FinitePresentation A (F.X i)) :
    ∀ n : ℤ, Module.FinitePresentation A ((⟪P, F⟫).X n) := by
  -- TODO: expand the degree-`n` term by `module_complex_internal_hom_piIso`, use boundedness to
  -- cut the product down to a finite direct sum, and reduce each summand to finite presentation of
  -- `F.X i` because the corresponding source term of `P` is finite free.
  let _ := hPbounded
  let _ := hPfiniteFree
  let _ := hFbounded
  let _ := hFfinitePresentation
  sorry

end

end CategoryTheory
