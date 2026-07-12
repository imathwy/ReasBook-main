import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_60_3
import StacksProject_2024.Chap15.Lemma_15_67_4
import StacksProject_2024.Chap15.Lemma_15_77_2

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField
local notation "Hκ" => DerivedCategory.homologyFunctor (ModuleCat κ)

/- Domain-style sampling:
- primary domain: localization of pseudo-coherent derived objects, residue-field homology
  vanishing, and canonical gap splittings in the standard `t`-structure;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeGE`,
  `exists_localizationAway_split_of_residueField_homology_surjective`,
  `existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge`;
- best owner abstraction: this item is a `source-facing` zero-fiber specialization of
  `exists_localizationAway_split_of_residueField_homology_surjective`; the compatible splitting
  data should stay in the owner-level `∃! e` form rather than a local package;
- primitive data: `K`, `i`, the pseudo-coherence witness `hK`, and the vanishing of the derived
  residue-field homology object
  `((Hκ i).obj (K ⊗[R]^L[κ]))`;
- derived API: perfectness and tor-amplitude of the localized upper truncation, together with the
  unique compatible gap splitting.

Source/core/bridge triage:
- `source-facing`: the localization theorem below;
- `core/canonical`: `exists_localizationAway_split_of_residueField_homology_surjective`,
  `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, and the standard truncation API;
- `bridge/view`: the zero-fiber hypothesis in degree `i`, which upgrades the localized
  `τ_{\le i} ⊞ τ_{\ge i + 1}` splitting to the gap splitting
  `τ_{\le i - 1} ⊞ τ_{\ge i + 1}` without introducing a second owner abstraction.
-/

-- Proof sketch: apply Lemma `15.77.2` to the vanishing hypothesis, viewed as a trivially
-- surjective base-change map onto zero, to split off the perfect upper truncation after
-- inverting some `f ∉ 𝔭`. Then shrink once more so that the localized degree-`i` homology
-- vanishes, which identifies `τ_{\le i}` with `τ_{\le i - 1}` and yields the canonical gap
-- decomposition.
/-- Helper for Lemma 15.77.4: if the residue-field homology object is zero, then the canonical
homology comparison into it is automatically an epimorphism. -/
private theorem homology_comparison_epi_of_isZero_target
    (K : DMod) (i : ℤ)
    (hHi : IsZero ((Hκ i).obj (K ⊗[R]^L[κ]))) :
    Epi (derivedTensorWithAlgebraHomologyComparison κ K i) := by
  -- Proof comment: every morphism into a zero object is epi, because the zero object has a
  -- subsingleton outgoing hom-set to every target.
  letI : Epi (derivedTensorWithAlgebraHomologyComparison κ K i) := by
    refine ⟨?_⟩
    intro Z g h _
    exact hHi.eq_of_src g h
  infer_instance

/-- Helper for Lemma 15.77.4: the single object on a zero module is zero in the derived
category. -/
private theorem singleFunctor_obj_isZero_of_isZero
    {A : Type u} [CommRing A] (n : ℤ) {M : ModuleCat A} (hM : IsZero M) :
    IsZero ((DerivedCategory.singleFunctor (ModuleCat A) n).obj M) := by
  -- Proof comment: applying the single-degree embedding functor to a zero object preserves
  -- zeroness.
  simpa using Functor.map_isZero (DerivedCategory.singleFunctor (ModuleCat A) n) hM

/-- Helper for Lemma 15.77.4: if the right summand is zero, then the left biproduct inclusion is
an isomorphism. -/
private theorem biprod_inl_isIso_of_isZero_right
    {A : Type u} [CommRing A]
    {X Y : DerivedCategory (ModuleCat A)} [HasBinaryBiproduct X Y]
    (hY : IsZero Y) :
    IsIso (biprod.inl : X ⟶ X ⊞ Y) := by
  have hsnd_zero : (biprod.snd : X ⊞ Y ⟶ Y) = 0 := by
    exact hY.eq_of_tgt _ _
  -- Proof comment: `biprod.fst` is a two-sided inverse once the right summand disappears.
  refine ⟨⟨biprod.fst, ?_, ?_⟩⟩
  · simp
  · apply biprod.hom_ext
    · simp [Category.assoc]
    · simpa [Category.assoc, hsnd_zero]

/-- Helper for Lemma 15.77.4: vanishing of `H^i(X)` makes the adjacent lower-truncation
comparison `τ_{\le i - 1} X ⟶ τ_{\le i} X` an isomorphism. -/
private theorem truncLE_step_comparison_isIso_of_homology_isZero
    {A : Type u} [CommRing A]
    (X : DerivedCategory (ModuleCat A)) (i : ℤ)
    (hzero :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj X)) :
    IsIso
      ((DerivedCategory.TStructure.t.natTransTruncLEOfLE (i - 1) i (by omega)).app X) := by
  let T : Triangle (DerivedCategory (ModuleCat A)) := truncLE_step_homologyTriangle X (i - 1)
  have hT : T ∈ distTriang (DerivedCategory (ModuleCat A)) := by
    -- Proof comment: this is the standard one-step lower-truncation triangle.
    simpa [T] using truncLE_step_homology_triangle X (i - 1)
  have h₃ : IsZero T.obj₃ := by
    -- Proof comment: the third vertex is the single object on `H^i(X)`.
    simpa [T, truncLE_step_homologyTriangle] using
      singleFunctor_obj_isZero_of_isZero (A := A) i hzero
  have hzero₃ : T.mor₃ = 0 := by
    -- Proof comment: every morphism out of a zero object vanishes.
    exact h₃.eq_of_src T.mor₃ 0
  obtain ⟨e, he₁, _he₂⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hzero₃
  have hinl : IsIso (biprod.inl : T.obj₁ ⟶ T.obj₁ ⊞ T.obj₃) :=
    biprod_inl_isIso_of_isZero_right (A := A) h₃
  have hcomp : IsIso (T.mor₁ ≫ e.hom) := by
    simpa [he₁] using hinl
  have hmor₁ : IsIso T.mor₁ := by
    letI : IsIso (T.mor₁ ≫ e.hom) := hcomp
    exact IsIso.of_isIso_comp_right T.mor₁ e.hom
  -- Proof comment: in this concrete triangle, `mor₁` is the adjacent truncation comparison.
  simpa [T, truncLE_step_homologyTriangle] using hmor₁

/-- Helper for Lemma 15.77.4: package the one-step lower-truncation comparison as an isomorphism
once `H^i(X)` vanishes. -/
private noncomputable def truncLE_step_iso_of_homology_isZero
    {A : Type u} [CommRing A]
    (X : DerivedCategory (ModuleCat A)) (i : ℤ)
    (hzero :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj X)) :
    (DerivedCategory.TStructure.t.truncLE (i - 1)).obj X ≅
      (DerivedCategory.TStructure.t.truncLE i).obj X :=
  @asIso _ _ _ _
    ((DerivedCategory.TStructure.t.natTransTruncLEOfLE (i - 1) i (by omega)).app X)
    (truncLE_step_comparison_isIso_of_homology_isZero (A := A) X i hzero)

/-- Helper for Lemma 15.77.4: transport the unique `τ_{\le i} ⊞ U` splitting along an
isomorphism `τ_{\le i - 1} X ≅ τ_{\le i} X`. -/
private theorem transport_unique_gap_split_of_truncLE_iso
    {A : Type u} [CommRing A]
    (X : DerivedCategory (ModuleCat A)) (i : ℤ) (U : DerivedCategory (ModuleCat A))
    (ρ : X ⟶ U)
    {eLE : (DerivedCategory.TStructure.t.truncLE (i - 1)).obj X ≅
        (DerivedCategory.TStructure.t.truncLE i).obj X}
    (hι :
      eLE.hom ≫ ((DerivedCategory.TStructure.t.truncLEι i).app X) =
        ((DerivedCategory.TStructure.t.truncLEι (i - 1)).app X))
    (hsplit :
      ∃! e : X ≅
          (DerivedCategory.TStructure.t.truncLE i).obj X ⊞ U,
        ((DerivedCategory.TStructure.t.truncLEι i).app X) ≫ e.hom = biprod.inl ∧
          e.hom ≫ biprod.snd = ρ) :
    ∃! e : X ≅
        (DerivedCategory.TStructure.t.truncLE (i - 1)).obj X ⊞ U,
      ((DerivedCategory.TStructure.t.truncLEι (i - 1)).app X) ≫ e.hom = biprod.inl ∧
        e.hom ≫ biprod.snd = ρ := by
  rcases hsplit with ⟨e₀, he₀, huniq₀⟩
  let e : X ≅ (DerivedCategory.TStructure.t.truncLE (i - 1)).obj X ⊞ U :=
    e₀ ≪≫ biprod.mapIso eLE.symm (Iso.refl U)
  refine ⟨e, ?_, ?_⟩
  · constructor
    · -- Proof comment: conjugating by `biprod.mapIso eLE.symm (Iso.refl U)` transports the
      -- left truncation compatibility from `τ≤ i` to `τ≤ i - 1`.
      calc
        ((DerivedCategory.TStructure.t.truncLEι (i - 1)).app X) ≫ e.hom =
            eLE.hom ≫ ((DerivedCategory.TStructure.t.truncLEι i).app X) ≫ e.hom := by
              rw [hι]
        _ =
            eLE.hom ≫
              (((DerivedCategory.TStructure.t.truncLEι i).app X) ≫ e₀.hom) ≫
                (biprod.mapIso eLE.symm (Iso.refl U)).hom := by
              simp [e, Category.assoc]
        _ = eLE.hom ≫ biprod.inl ≫ (biprod.mapIso eLE.symm (Iso.refl U)).hom := by
              rw [he₀.1]
        _ = biprod.inl := by
              simp [Category.assoc]
    · -- Proof comment: the conjugation does not change the right projection.
      calc
        e.hom ≫ biprod.snd =
            e₀.hom ≫ (biprod.mapIso eLE.symm (Iso.refl U)).hom ≫ biprod.snd := by
              simp [e, Category.assoc]
        _ = e₀.hom ≫ biprod.snd := by
              simp [Category.assoc]
        _ = ρ := he₀.2
  · intro e' he'
    let e'' : X ≅ (DerivedCategory.TStructure.t.truncLE i).obj X ⊞ U :=
      e' ≪≫ biprod.mapIso eLE (Iso.refl U)
    have he'' :
        ((DerivedCategory.TStructure.t.truncLEι i).app X) ≫ e''.hom = biprod.inl ∧
          e''.hom ≫ biprod.snd = ρ := by
      constructor
      · -- Proof comment: composing back with `biprod.mapIso eLE (Iso.refl U)` recovers a
        -- compatible `τ≤ i` splitting, so uniqueness reduces to the original one.
        calc
          ((DerivedCategory.TStructure.t.truncLEι i).app X) ≫ e''.hom =
              eLE.inv ≫ ((DerivedCategory.TStructure.t.truncLEι (i - 1)).app X) ≫ e''.hom := by
                rw [← hι]
                simp
          _ =
              eLE.inv ≫
                (((DerivedCategory.TStructure.t.truncLEι (i - 1)).app X) ≫ e'.hom) ≫
                  (biprod.mapIso eLE (Iso.refl U)).hom := by
                simp [e'', Category.assoc]
          _ = eLE.inv ≫ biprod.inl ≫ (biprod.mapIso eLE (Iso.refl U)).hom := by
                rw [he'.1]
          _ = biprod.inl := by
                simp [Category.assoc]
      · calc
          e''.hom ≫ biprod.snd =
              e'.hom ≫ (biprod.mapIso eLE (Iso.refl U)).hom ≫ biprod.snd := by
                simp [e'', Category.assoc]
          _ = e'.hom ≫ biprod.snd := by
                simp [Category.assoc]
          _ = ρ := he'.2
    have heq : e'' = e₀ := huniq₀ e'' he''
    apply Iso.ext
    apply (cancel_mono (biprod.mapIso eLE (Iso.refl U)).hom).1
    simpa [e, e'', Category.assoc] using congrArg Iso.hom heq

/-- Helper for Lemma 15.77.4: choose a bounded-above termwise finite-free representative of `K`
that already carries the residue-field homology vanishing hypothesis. -/
private theorem exists_termwiseFiniteFree_model_with_residueField_homology_isZero
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hHi : IsZero ((Hκ i).obj (K ⊗[R]^L[κ]))) :
    ∃ (E : CochainComplex (ModuleCat R) ℤ) (b : ℤ),
      E.IsStrictlyLE b ∧ E.IsTermwiseFiniteFree ∧
        ∃ e : DerivedCategory.Q.obj E ≅ K,
          IsZero ((Hκ i).obj ((DerivedCategory.Q.obj E) ⊗[R]^L[κ])) := by
  rcases hK with ⟨E, ⟨b, hE⟩, hEfree, α, hα⟩
  let e : DerivedCategory.Q.obj E ≅ K := by
    letI : IsIso α := hα
    exact asIso α
  have hHiE : IsZero ((Hκ i).obj ((DerivedCategory.Q.obj E) ⊗[R]^L[κ])) := by
    -- Proof comment: transport the zero residue-field homology statement from `K` back to the
    -- chosen bounded-above finite-free model through the derived tensor comparison isomorphism.
    exact (((Hκ i).mapIso ((derivedTensorWithAlgebra κ).mapIso e)).isZero_iff).2 hHi
  exact ⟨E, b, hE, hEfree, e, hHiE⟩

/-- Helper for Lemma 15.77.4: a termwise finite-free cochain complex is termwise flat. -/
private theorem isTermwiseFlat_of_isTermwiseFiniteFree
    (E : CochainComplex (ModuleCat R) ℤ) (hEfree : E.IsTermwiseFiniteFree) :
    E.IsTermwiseFlat := by
  intro n
  rcases hEfree n with ⟨hfree, _hfinite⟩
  -- Proof comment: finite free modules are projective, hence flat.
  let _ : Module.Free R (E.X n) := hfree
  exact Module.Flat.of_projective (R := R) (M := E.X n)

/-- Helper for Lemma 15.77.4: termwise finite-free cochain complexes have finite homology. -/
private theorem homology_finite_of_isTermwiseFiniteFree
    {E : CochainComplex (ModuleCat R) ℤ} [E.IsTermwiseFiniteFree] (i : ℤ) :
    Module.Finite R (E.homology i) := by
  have hcycles : Module.Finite R (E.cycles i) := by
    -- Proof comment: cycles form a submodule of the finite free degree-`i` term.
    exact Module.Finite.of_injective
      (E.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  let _ : Module.Finite R (E.cycles i) := hcycles
  -- Proof comment: homology is the quotient of cycles by the boundaries.
  exact Module.Finite.of_surjective
    (E.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- Helper for Lemma 15.77.4: over a local ring, a finite module with zero residue quotient is
already zero by Nakayama. -/
private theorem subsingleton_of_subsingleton_maximalIdeal_smul_quotient
    {A : Type u} [CommRing A] [IsLocalRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hsub : Subsingleton (M ⧸ (maximalIdeal A • (⊤ : Submodule A M)))) :
    Subsingleton M := by
  letI : Subsingleton (M ⧸ (maximalIdeal A • (⊤ : Submodule A M))) := hsub
  have htop : maximalIdeal A • (⊤ : Submodule A M) = ⊤ := by
    -- Proof comment: a zero residue quotient means every element already lies in
    -- `maximalIdeal A • ⊤`.
    apply top_unique
    intro x hx
    have hxzero :
        Submodule.mkQ (maximalIdeal A • (⊤ : Submodule A M)) x = 0 := Subsingleton.elim _ _
    simpa using hxzero
  have hmaxJac₀ : maximalIdeal A ≤ Ideal.jacobson (⊥ : Ideal A) :=
    IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A)
  have hmaxJac : maximalIdeal A ≤ Ring.jacobson A := by
    -- Proof comment: specialize the local-ring Jacobson-radical containment to the zero ideal.
    rw [← Ideal.jacobson_bot]
    exact hmaxJac₀
  -- Proof comment: Nakayama kills the whole finite module once `𝔪 • ⊤ = ⊤`.
  exact
    subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
      (I := maximalIdeal A) (M := M) htop hmaxJac

/-- Helper for Lemma 15.77.4: if a finite module localizes to zero at a prime, then one basic
open around that prime already kills the away-localized module. -/
private theorem exists_localizationAway_subsingleton_of_finite_localizedAtPrime_subsingleton
    {A : Type u} [CommRing A] (𝔮 : PrimeSpectrum A)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hsub : Subsingleton (LocalizedModule.AtPrime 𝔮.asIdeal M)) :
    ∃ s : A, s ∉ 𝔮.asIdeal ∧ Subsingleton (LocalizedModule.Away s M) := by
  classical
  rcases (Module.Finite.iff_exists_surjective_free A M).1 inferInstance with ⟨n, π, hπ⟩
  let kill : Fin n → A := fun j ↦
    Classical.choose <|
      (LocalizedModule.subsingleton_iff (S := 𝔮.asIdeal.primeCompl) (M := M)).mp
        hsub (π (Pi.single j (1 : A)))
  have hkill_mem : ∀ j : Fin n, kill j ∉ 𝔮.asIdeal := by
    intro j
    exact (Classical.choose_spec <|
      (LocalizedModule.subsingleton_iff (S := 𝔮.asIdeal.primeCompl) (M := M)).mp
        hsub (π (Pi.single j (1 : A)))).1
  have hkill_zero : ∀ j : Fin n, kill j • π (Pi.single j (1 : A)) = 0 := by
    intro j
    exact (Classical.choose_spec <|
      (LocalizedModule.subsingleton_iff (S := 𝔮.asIdeal.primeCompl) (M := M)).mp
        hsub (π (Pi.single j (1 : A)))).2
  let s' : 𝔮.asIdeal.primeCompl := ∏ j, ⟨kill j, hkill_mem j⟩
  have hs_gen : ∀ j : Fin n, s'.1 • π (Pi.single j (1 : A)) = 0 := by
    intro j
    have hs_split :
        s'.1 = ((Finset.univ.erase j).prod fun k ↦ kill k) * kill j := by
      simpa [s'] using
        (Finset.prod_erase_mul (s := Finset.univ) (f := fun k : Fin n ↦ kill k)
          (a := j) (by simp : j ∈ (Finset.univ : Finset (Fin n))))
    -- Proof comment: the global product still kills the `j`th generator because one factor already
    -- does.
    calc
      s'.1 • π (Pi.single j (1 : A)) =
          ((Finset.univ.erase j).prod fun k ↦ kill k) •
            (kill j • π (Pi.single j (1 : A))) := by
              rw [hs_split, mul_smul]
      _ = 0 := by simp [hkill_zero j]
  have hs_ann : s'.1 ∈ Module.annihilator A M := by
    rw [Submodule.mem_annihilator]
    intro x
    rcases hπ x with ⟨y, rfl⟩
    have hy :
        y = ∑ j, y j • Pi.single j (1 : A) := by
      ext j
      simp
    -- Proof comment: surjectivity reduces the annihilator claim to the chosen finite generating
    -- family.
    calc
      s'.1 • π y = π (s'.1 • y) := by simp
      _ = π (s'.1 • ∑ j, y j • Pi.single j (1 : A)) := by rw [hy]
      _ = π (∑ j, y j • (s'.1 • Pi.single j (1 : A))) := by
            simp [smul_sum, Finset.sum_smul, mul_smul]
      _ = π 0 := by
            congr 1
            ext j
            simp [hs_gen j]
      _ = 0 := by simp
  refine ⟨s'.1, s'.2, ?_⟩
  rw [LocalizedModule.subsingleton_iff (S := Submonoid.powers s'.1) (M := M)]
  intro x
  refine ⟨s'.1, ⟨1, by simp⟩, ?_⟩
  exact (Module.mem_annihilator.mp hs_ann) x

/-- Helper for Lemma 15.77.4: a subsingleton away-localized module is zero in `ModuleCat`. -/
private theorem moduleCat_isZero_of_away_subsingleton
    {A : Type u} [CommRing A] {s : A}
    {M : Type u} [AddCommGroup M] [Module A M]
    (hsub : Subsingleton (LocalizedModule.Away s M)) :
    IsZero (ModuleCat.of (Localization.Away s) (LocalizedModule.Away s M)) := by
  simpa [ModuleCat.isZero_iff_subsingleton] using hsub

/-- Helper for Lemma 15.77.4: vanishing after inverting `g` persists after any further basic-open
refinement `D(f * g) ⊆ D(g)`. -/
private theorem away_subsingleton_of_away_subsingleton_right
    {A : Type u} [CommRing A] (f g : A)
    {M : Type u} [AddCommGroup M] [Module A M]
    (hsub : Subsingleton (LocalizedModule.Away g M)) :
    Subsingleton (LocalizedModule.Away (f * g) M) := by
  rw [LocalizedModule.subsingleton_iff (S := Submonoid.powers g) (M := M)] at hsub
  rw [LocalizedModule.subsingleton_iff (S := Submonoid.powers (f * g)) (M := M)]
  intro x
  obtain ⟨g', hg', hgx⟩ := hsub x
  rcases hg' with ⟨n, rfl⟩
  refine ⟨(f * g) ^ n, ⟨n, rfl⟩, ?_⟩
  -- Proof comment: the same exponent works after multiplying by the extra factor `f^n`.
  calc
    (f * g) ^ n • x = (f ^ n * g ^ n) • x := by rw [mul_pow]
    _ = f ^ n • (g ^ n • x) := by rw [mul_smul]
    _ = 0 := by simp [hgx]

/-- Helper for Lemma 15.77.4: the residue-field vanishing hypothesis forces exactness of the
scalar-extended three-term complex at degree `i`. -/
private theorem fiber_shortComplex_exact_of_residueField_homology_isZero
    (i : ℤ) (E : CochainComplex (ModuleCat R) ℤ) (b : ℤ)
    (hE : E.IsStrictlyLE b) (hEfree : E.IsTermwiseFiniteFree)
    (hHiE : IsZero ((Hκ i).obj ((DerivedCategory.Q.obj E) ⊗[R]^L[κ]))) :
    (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).ExactAt i := by
  let Eκ :=
    (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E)
  have hEflat : E.IsTermwiseFlat :=
    isTermwiseFlat_of_isTermwiseFiniteFree (R := R) E hEfree
  let eTensor :
      ((DerivedCategory.Q.obj E) ⊗[R]^L[κ]) ≅ DerivedCategory.Q.obj Eκ :=
    derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
      (A := R) (B := κ) hEflat hE
  have hzeroDerived :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat κ) i).obj
        (DerivedCategory.Q.obj Eκ)) := by
    -- Proof comment: bounded-above flat scalar extension identifies the derived tensor with the
    -- explicit scalar-extended complex.
    exact (((DerivedCategory.homologyFunctor (ModuleCat κ) i).mapIso eTensor).isZero_iff).1 hHiE
  have hzeroHomology : IsZero (Eκ.homology i) := by
    -- Proof comment: on an honest cochain complex, the derived homology object is computed by the
    -- ordinary homology of that complex.
    exact ((DerivedCategory.homologyFunctorFactors (ModuleCat κ) i).app Eκ).isZero_iff.1
      hzeroDerived
  -- Proof comment: exactness at the middle degree is exactly the vanishing of the degree-`i`
  -- homology object of the scalar-extended complex.
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hzeroHomology

/-- Helper for Lemma 15.77.4: exact away-localization of a cochain complex computes the away
localization of its ordinary homology module. -/
private noncomputable def extendScalars_away_homology_iso_localizedModule
    (E : CochainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    ((((ModuleCat.extendScalars (algebraMap R (Localization.Away f))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).homology i) ≅
      ModuleCat.of (Localization.Away f) (LocalizedModule.Away f (E.homology i)) := by
  let A := Localization.Away f
  let F : ModuleCat R ⥤ ModuleCat A := ModuleCat.extendScalars (algebraMap R A)
  let _ : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : F.PreservesHomology := inferInstance
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) ≃ₗ[A] A :=
    { __ := AddEquiv.refl A
      map_smul' := fun _ _ ↦ rfl }
  let eTensor :
      F.obj (ModuleCat.of R (E.homology i)) ≅
        ModuleCat.of A (A ⊗[R] E.homology i) := by
    -- Proof comment: expand exact scalar extension into the honest tensor-product model.
    simpa [F, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl R (E.homology i))).toModuleIso
  let eLocal :
      ModuleCat.of A (A ⊗[R] E.homology i) ≅
        ModuleCat.of A (LocalizedModule.Away f (E.homology i)) :=
    ((LocalizedModule.equivTensorProduct (Submonoid.powers f) (E.homology i)).symm).toModuleIso
  -- Proof comment: first commute homology past exact scalar extension, then identify the result
  -- with ordinary away-localization of the homology module.
  exact (E.sc i).mapHomologyIso F ≪≫ eTensor ≪≫ eLocal

/-- Helper for Lemma 15.77.4: exact localization at the prime `𝔭` computes the prime-localized
ordinary homology module of a cochain complex. -/
private noncomputable def extendScalars_atPrime_homology_iso_localizedModule
    (E : CochainComplex (ModuleCat R) ℤ) (i : ℤ) :
    ((((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭.asIdeal)))
          .mapHomologicalComplex (ComplexShape.up ℤ)).obj E).homology i) ≅
      ModuleCat.of (Localization.AtPrime 𝔭.asIdeal)
        (LocalizedModule.AtPrime 𝔭.asIdeal (E.homology i)) := by
  let A := Localization.AtPrime 𝔭.asIdeal
  let F : ModuleCat R ⥤ ModuleCat A := ModuleCat.extendScalars (algebraMap R A)
  let _ : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : F.PreservesHomology := inferInstance
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) ≃ₗ[A] A :=
    { __ := AddEquiv.refl A
      map_smul' := fun _ _ ↦ rfl }
  let eTensor :
      F.obj (ModuleCat.of R (E.homology i)) ≅
        ModuleCat.of A (A ⊗[R] E.homology i) := by
    -- Proof comment: expand exact scalar extension once into the honest tensor-product model.
    simpa [F, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl R (E.homology i))).toModuleIso
  let eLocal :
      ModuleCat.of A (A ⊗[R] E.homology i) ≅
        ModuleCat.of A (LocalizedModule.AtPrime 𝔭.asIdeal (E.homology i)) :=
    ((LocalizedModule.equivTensorProduct 𝔭.asIdeal.primeCompl (E.homology i)).symm).toModuleIso
  -- Proof comment: commute homology with the exact localization functor and then rewrite the
  -- resulting tensor product as the canonical prime-localized module.
  exact (E.sc i).mapHomologyIso F ≪≫ eTensor ≪≫ eLocal

/-- Helper for Lemma 15.77.4: localizing at a prime ideal does not change its residue field. -/
private noncomputable abbrev prime_localization_residueField_equiv
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] :
    IsLocalRing.ResidueField (Localization.AtPrime p) ≃+* p.ResidueField :=
  -- Proof comment: compare the residue field of `A_p` through the maximal ideal of the local
  -- ring `A_p`.
  (maximalIdeal_residueField_equiv (Localization.AtPrime p)).symm.trans <|
    by
      change (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField ≃+* p.ResidueField
      exact maximalIdeal_residueField_equiv (Localization.AtPrime p)

/-- Helper for Lemma 15.77.4: the prime-local residue-field equivalence sends the canonical local
residue class of a base element to its original prime-residue-field class. -/
private theorem prime_localization_residueField_equiv_apply_algebraMap
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] (a : A) :
    prime_localization_residueField_equiv (p := p)
        (algebraMap (Localization.AtPrime p)
          (IsLocalRing.ResidueField (Localization.AtPrime p))
          (algebraMap A (Localization.AtPrime p) a)) =
      algebraMap A p.ResidueField a := by
  -- Proof comment: both residue-field descriptions of `A_p` carry the class of `a`.
  simpa [prime_localization_residueField_equiv, RingEquiv.trans_apply] using
    maximalIdeal_residueField_equiv_apply_algebraMap (Localization.AtPrime p)
      (algebraMap A (Localization.AtPrime p) a)

/-- Helper for Lemma 15.77.4: the inverse prime-local residue-field equivalence sends the
original prime-residue-field class of a base element to the canonical local residue class. -/
private theorem prime_localization_residueField_equiv_symm_apply_algebraMap
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] (a : A) :
    (prime_localization_residueField_equiv (p := p)).symm (algebraMap A p.ResidueField a) =
      algebraMap (Localization.AtPrime p)
        (IsLocalRing.ResidueField (Localization.AtPrime p))
        (algebraMap A (Localization.AtPrime p) a) := by
  -- Proof comment: apply the forward evaluation formula and invert the resulting equivalence.
  exact (prime_localization_residueField_equiv (p := p)).injective <|
    by
      rw [RingEquiv.apply_symm_apply, prime_localization_residueField_equiv_apply_algebraMap]

/-- Helper for Lemma 15.77.4: the quotient by the maximal ideal of a local ring is its residue
field as a linear object over the local ring itself. -/
private noncomputable abbrev maximalIdeal_quotient_residueField_equiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (A ⧸ maximalIdeal A) ≃+* IsLocalRing.ResidueField A :=
  RingEquiv.ofBijective
    (algebraMap (A ⧸ maximalIdeal A) (IsLocalRing.ResidueField A))
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))

/-- Helper for Lemma 15.77.4: the quotient by the maximal ideal of a local ring is its residue
field as a linear object over the local ring itself. -/
private noncomputable abbrev maximalIdeal_quotient_linearEquiv_residueField
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (A ⧸ maximalIdeal A) ≃ₗ[A] IsLocalRing.ResidueField A :=
  let e := maximalIdeal_quotient_residueField_equiv A
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := by
      intro a x
      -- Proof comment: both scalar actions are multiplication by the image of `a` in the local
      -- residue field.
      change
        e ((Ideal.Quotient.mk (maximalIdeal A) a) * x) =
        IsLocalRing.residue A a *
          e x
      rw [e.map_mul]
      rfl }

/-- Helper for Lemma 15.77.4: the residue-field identification `κ(R_𝔭) ≃ κ(𝔭)` is linear over
the original ring `R`. -/
private noncomputable def prime_localization_residueField_linearEquiv :
    IsLocalRing.ResidueField (Localization.AtPrime 𝔭.asIdeal) ≃ₗ[R] κ :=
  let e := prime_localization_residueField_equiv (p := 𝔭.asIdeal)
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := by
      intro r x
      -- Proof comment: the ring equivalence carries the class of `r` in `κ(R_𝔭)` to its
      -- original class in `κ(𝔭)`.
      change
        e ((algebraMap R (IsLocalRing.ResidueField (Localization.AtPrime 𝔭.asIdeal)) r) * x) =
          (algebraMap R κ r) *
            e x
      rw [e.map_mul,
        prime_localization_residueField_equiv_apply_algebraMap (p := 𝔭.asIdeal)] }

/-- Helper for Lemma 15.77.4: exact scalar extension to `κ(𝔭)` identifies the homology of an
ordinary complex with the tensor product `κ(𝔭) ⊗_R H^i(E)`. -/
private noncomputable def extendScalars_residueField_homology_iso_tensor
    (E : CochainComplex (ModuleCat R) ℤ) (i : ℤ) :
    ((((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).homology i) ≅
      ModuleCat.of κ (κ ⊗[R] E.homology i) := by
  let F : ModuleCat R ⥤ ModuleCat κ := ModuleCat.extendScalars (algebraMap R κ)
  let _ : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : F.PreservesHomology := inferInstance
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R κ)).obj (ModuleCat.of κ κ)) ≃ₗ[κ] κ :=
    { __ := AddEquiv.refl κ
      map_smul' := fun _ _ ↦ rfl }
  let eTensor :
      F.obj (ModuleCat.of R (E.homology i)) ≅
        ModuleCat.of κ (κ ⊗[R] E.homology i) := by
    -- Proof comment: unfold exact scalar extension once into the usual tensor-product model.
    simpa [F, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl R (E.homology i))).toModuleIso
  -- Proof comment: exactness of scalar extension lets homology commute with the functor `F`.
  exact (E.sc i).mapHomologyIso F ≪≫ eTensor

/-- Helper for Lemma 15.77.4: if the closed fiber `κ(𝔭) ⊗_R M` is zero for a finite module,
then the prime-localized module `M_𝔭` is already zero. -/
private theorem localizedAtPrime_subsingleton_of_residueField_tensor_subsingleton
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hsub : Subsingleton (κ ⊗[R] M)) :
    Subsingleton (LocalizedModule.AtPrime 𝔭.asIdeal M) := by
  let A := Localization.AtPrime 𝔭.asIdeal
  let κA := IsLocalRing.ResidueField A
  let N := LocalizedModule.AtPrime 𝔭.asIdeal M
  have hfiniteTensor : Module.Finite A (A ⊗[R] M) := inferInstance
  let _ : Module.Finite A (A ⊗[R] M) := hfiniteTensor
  let hfiniteLocal : Module.Finite A N :=
    Module.Finite.equiv (LocalizedModule.equivTensorProduct 𝔭.asIdeal.primeCompl M).symm
  let _ : Module.Finite A N := hfiniteLocal
  have hquot :
      Subsingleton (N ⧸ (maximalIdeal A • (⊤ : Submodule A N))) := by
    let eQuot :
        N ⧸ (maximalIdeal A • (⊤ : Submodule A N)) ≃
          ((A ⧸ maximalIdeal A) ⊗[A] N) :=
      (TensorProduct.quotTensorEquivQuotSMul N (maximalIdeal A)).symm.toEquiv
    let eResidue :
        ((A ⧸ maximalIdeal A) ⊗[A] N) ≃ (κA ⊗[A] N) :=
      (TensorProduct.AlgebraTensorModule.congr
        (maximalIdeal_quotient_linearEquiv_residueField A)
        (LinearEquiv.refl A N)).toEquiv
    let eLocal :
        (κA ⊗[A] N) ≃ (κA ⊗[A] (A ⊗[R] M)) :=
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl A κA)
        (LocalizedModule.equivTensorProduct 𝔭.asIdeal.primeCompl M)).toEquiv
    let eAssoc :
        (κA ⊗[A] (A ⊗[R] M)) ≃ ((κA ⊗[A] A) ⊗[R] M) :=
      (TensorProduct.AlgebraTensorModule.assoc
        (R := R) (A := A) (B := κA) (M := κA) (P := A) (Q := M)).symm.toEquiv
    let eRid :
        ((κA ⊗[A] A) ⊗[R] M) ≃ (κA ⊗[R] M) :=
      (TensorProduct.AlgebraTensorModule.congr
        (TensorProduct.rid A κA)
        (LinearEquiv.refl R M)).toEquiv
    let ePrime :
        (κA ⊗[R] M) ≃ (κ ⊗[R] M) :=
      (TensorProduct.AlgebraTensorModule.congr
        (prime_localization_residueField_linearEquiv (R := R) (𝔭 := 𝔭))
        (LinearEquiv.refl R M)).toEquiv
    let eTotal :
        N ⧸ (maximalIdeal A • (⊤ : Submodule A N)) ≃ (κ ⊗[R] M) :=
      eQuot.trans (eResidue.trans (eLocal.trans (eAssoc.trans (eRid.trans ePrime))))
    let _ : Subsingleton (κ ⊗[R] M) := hsub
    exact eTotal.subsingleton
  -- Proof comment: after identifying the closed fiber of `M_𝔭` with `κ(𝔭) ⊗_R M`, Nakayama
  -- kills the whole localized module.
  exact
    subsingleton_of_subsingleton_maximalIdeal_smul_quotient
      (A := A) (M := N) hquot

/-- Helper for Lemma 15.77.4: a subsingleton away-localized ordinary homology module forces the
corresponding derived homology object after away localization to be zero. -/
private theorem away_derived_homology_isZero_of_away_homology_subsingleton
    (K : DMod) (i : ℤ)
    (E : CochainComplex (ModuleCat R) ℤ) (b : ℤ)
    (hE : E.IsStrictlyLE b) (hEfree : E.IsTermwiseFiniteFree)
    (e : DerivedCategory.Q.obj E ≅ K)
    {f : R}
    (hsub : Subsingleton (LocalizedModule.Away f (E.homology i))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away f)) i).obj
      (K ⊗[R]^L[Localization.Away f])) := by
  let A := Localization.Away f
  let EF :=
    (((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E)
  have hzeroHomology :
      IsZero (EF.homology i) := by
    have hzeroAway :
        IsZero (ModuleCat.of A (LocalizedModule.Away f (E.homology i))) :=
      moduleCat_isZero_of_away_subsingleton (A := R) (s := f) hsub
    -- Proof comment: exact away-localization computes ordinary away-localized homology.
    exact hzeroAway.of_iso
      (extendScalars_away_homology_iso_localizedModule (R := R) E f i).symm
  have hzeroDerivedEF :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
        (DerivedCategory.Q.obj EF)) := by
    -- Proof comment: on an honest complex, derived homology is the ordinary homology object.
    exact ((DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app EF).isZero_iff.2
      hzeroHomology
  have hEflat : E.IsTermwiseFlat :=
    isTermwiseFlat_of_isTermwiseFiniteFree (R := R) E hEfree
  let eTensor :
      ((DerivedCategory.Q.obj E) ⊗[R]^L[A]) ≅ DerivedCategory.Q.obj EF :=
    derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
      (A := R) (B := A) hEflat hE
  have hzeroDerivedE :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
        ((DerivedCategory.Q.obj E) ⊗[R]^L[A])) := by
    -- Proof comment: compare the derived tensor with the explicit scalar-extended model `EF`.
    exact (((DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso eTensor).isZero_iff).2
      hzeroDerivedEF
  -- Proof comment: finally transport the vanishing back across the chosen model isomorphism `e`.
  exact (((DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso
      ((derivedTensorWithAlgebra A).mapIso e)).isZero_iff).1 hzeroDerivedE

/-- Helper for Lemma 15.77.4: once the prime-local ordinary homology module of the finite-free
model is zero, one basic open around `𝔭` already kills both the ordinary and derived degree-`i`
homology after away localization. -/
private theorem exists_localizationAway_homology_isZero_of_finite_localizedAtPrime_subsingleton
    (K : DMod) (i : ℤ)
    (E : CochainComplex (ModuleCat R) ℤ) (b : ℤ)
    (hE : E.IsStrictlyLE b) (hEfree : E.IsTermwiseFiniteFree)
    (e : DerivedCategory.Q.obj E ≅ K)
    (hsub : Subsingleton (LocalizedModule.AtPrime 𝔭.asIdeal (E.homology i))) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      Subsingleton (LocalizedModule.Away f (E.homology i)) ∧
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away f)) i).obj
        (K ⊗[R]^L[Localization.Away f])) := by
  have hfinite : Module.Finite R (E.homology i) :=
    homology_finite_of_isTermwiseFiniteFree (R := R) (E := E) i
  let _ : Module.Finite R (E.homology i) := hfinite
  rcases
      exists_localizationAway_subsingleton_of_finite_localizedAtPrime_subsingleton
        (𝔮 := 𝔭) (M := E.homology i) hsub with
    ⟨f, hf, hsubAway⟩
  refine ⟨f, hf, hsubAway, ?_⟩
  -- Proof comment: the module-level away-localized vanishing now upgrades to the derived
  -- homology object by comparing with the bounded-above finite-free model `E`.
  exact away_derived_homology_isZero_of_away_homology_subsingleton
    (R := R) K i E b hE hEfree e hsubAway

/-- Helper for Lemma 15.77.4: specialize Lemma `15.77.2` to the zero-fiber case and choose one
away-localization where the degree-`i` localized homology already vanishes. -/
private theorem localizedAtPrime_homology_subsingleton_of_exact_fiber
    (i : ℤ) (E : CochainComplex (ModuleCat R) ℤ)
    (hEfree : E.IsTermwiseFiniteFree)
    (hExactFiber :
      (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).ExactAt i) :
    Subsingleton (LocalizedModule.AtPrime 𝔭.asIdeal (E.homology i)) := by
  let Eκ :=
    (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E)
  have hzeroFiber : IsZero (Eκ.homology i) := by
    -- Proof comment: the exactness hypothesis on the residue-field fiber is exactly the vanishing
    -- of its degree-`i` ordinary homology object.
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hExactFiber
  have hzeroTensor :
      IsZero (ModuleCat.of κ (κ ⊗[R] E.homology i)) := by
    -- Proof comment: commute homology with exact scalar extension to rewrite the zero fiber
    -- homology as the residue-field tensor product of `H^i(E)`.
    exact hzeroFiber.of_iso
      (extendScalars_residueField_homology_iso_tensor (R := R) (𝔭 := 𝔭) E i)
  have hsubTensor : Subsingleton (κ ⊗[R] E.homology i) :=
    ModuleCat.subsingleton_of_isZero hzeroTensor
  let _ : E.IsTermwiseFiniteFree := hEfree
  have hfinite : Module.Finite R (E.homology i) :=
    homology_finite_of_isTermwiseFiniteFree (R := R) (E := E) i
  let _ : Module.Finite R (E.homology i) := hfinite
  -- Proof comment: the remaining step is purely local algebra: identify the local closed fiber of
  -- `H^i(E)_𝔭` with `κ(𝔭) ⊗_R H^i(E)` and apply Nakayama.
  exact
    localizedAtPrime_subsingleton_of_residueField_tensor_subsingleton
      (R := R) (𝔭 := 𝔭) (M := E.homology i) hsubTensor

/-- Helper for Lemma 15.77.4: refine the split-open from Lemma `15.77.2` and the homology-kill
open to their product localization `D(fSplit * fKill)`. -/
private theorem split_package_on_product_localization
    (K : DMod) (i : ℤ)
    (E : CochainComplex (ModuleCat R) ℤ) (b : ℤ)
    (hE : E.IsStrictlyLE b) (hEfree : E.IsTermwiseFiniteFree)
    (e : DerivedCategory.Q.obj E ≅ K)
    {fSplit fKill : R}
    (hfSplit : fSplit ∉ 𝔭.asIdeal)
    (hPerfSplit :
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away fSplit])).IsPerfect)
    (hTorSplit :
      HasTorAmplitudeGE
        ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away fSplit]))
        (i + 1))
    (hSplit :
      ∃! e' :
          K ⊗[R]^L[Localization.Away fSplit] ≅
            (t.truncLE i).obj (K ⊗[R]^L[Localization.Away fSplit]) ⊞
              (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away fSplit]),
        ((t.truncLEι i).app (K ⊗[R]^L[Localization.Away fSplit])) ≫ e'.hom = biprod.inl ∧
          e'.hom ≫ biprod.snd =
            ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away fSplit])))
    (hfKill : fKill ∉ 𝔭.asIdeal)
    (hsubKill : Subsingleton (LocalizedModule.Away fKill (E.homology i))) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away f)) i).obj
        (K ⊗[R]^L[Localization.Away f])) ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        HasTorAmplitudeGE
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          ∃! e' :
              K ⊗[R]^L[Localization.Away f] ≅
                (t.truncLE i).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                  (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
            ((t.truncLEι i).app (K ⊗[R]^L[Localization.Away f])) ≫ e'.hom = biprod.inl ∧
              e'.hom ≫ biprod.snd =
                ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away f])) :=
  -- TODO: set `f = fSplit * fKill`; transport the split/perfect/tor-amplitude package from
  -- `fSplit` to `f` by further localization and the iterated-vs-direct away-localization
  -- comparison, then combine `away_subsingleton_of_away_subsingleton_right` with
  -- `away_derived_homology_isZero_of_away_homology_subsingleton` to recover the localized
  -- vanishing of `H^i`.
  sorry

/-- Helper for Lemma 15.77.4: specialize Lemma `15.77.2` to the zero-fiber case and choose one
away-localization where the degree-`i` localized homology already vanishes. -/
private theorem exists_localizationAway_split_truncLE_and_homology_isZero_of_termwiseFiniteFree_model
    (K : DMod) (i : ℤ)
    (E : CochainComplex (ModuleCat R) ℤ) (b : ℤ)
    (hE : E.IsStrictlyLE b) (hEfree : E.IsTermwiseFiniteFree)
    (e : DerivedCategory.Q.obj E ≅ K)
    (hHiE : IsZero ((Hκ i).obj ((DerivedCategory.Q.obj E) ⊗[R]^L[κ]))) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away f)) i).obj
        (K ⊗[R]^L[Localization.Away f])) ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        HasTorAmplitudeGE
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          ∃! e' :
              K ⊗[R]^L[Localization.Away f] ≅
                (t.truncLE i).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                  (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
            ((t.truncLEι i).app (K ⊗[R]^L[Localization.Away f])) ≫ e'.hom = biprod.inl ∧
              e'.hom ≫ biprod.snd =
                ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away f])) := by
  -- Route correction: the old proof tried to intersect two unrelated basic opens, but the source
  -- proof uses one bounded-above finite-free model and a single localization `f = a * b`
  -- extracted from the two adjacent differentials around degree `i`.
  let Eκ :=
    (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E)
  have hExactFiber : Eκ.ExactAt i :=
    fiber_shortComplex_exact_of_residueField_homology_isZero
      (𝔭 := 𝔭) i E b hE hEfree hHiE
  let _ : E.IsTermwiseFiniteFree := hEfree
  have hEhomFinite : Module.Finite R (E.homology i) :=
    homology_finite_of_isTermwiseFiniteFree (R := R) (E := E) i
  let _ : Module.Finite R (E.homology i) := hEhomFinite
  have hsurj :
      Epi (derivedTensorWithAlgebraHomologyComparison κ K i) :=
    homology_comparison_epi_of_isZero_target (𝔭 := 𝔭) K i hHiE
  rcases
      exists_localizationAway_split_of_residueField_homology_surjective
        (𝔭 := 𝔭) K i (by
          -- Proof comment: the chosen finite-free model already witnesses pseudo-coherence of `K`.
          refine ⟨E, ⟨b, hE⟩, hEfree, e.hom, ?_⟩
          exact e.isIso) hsurj with
    ⟨fSplit, hfSplit, hPerfSplit, hTorSplit, hSplit⟩
  have hsubAtPrime :
      Subsingleton (LocalizedModule.AtPrime 𝔭.asIdeal (E.homology i)) :=
    localizedAtPrime_homology_subsingleton_of_exact_fiber
      (𝔭 := 𝔭) i E hEfree hExactFiber
  rcases
      exists_localizationAway_homology_isZero_of_finite_localizedAtPrime_subsingleton
        (𝔭 := 𝔭) K i E b hE hEfree e hsubAtPrime with
    ⟨fKill, hfKill, hsubKill, _hHKill⟩
  -- Proof comment: the remaining source-faithful step is now isolated: intersect the split-open
  -- from Lemma `15.77.2` with the homology-kill open by passing to the product localization.
  exact
    split_package_on_product_localization
      (𝔭 := 𝔭) K i E b hE hEfree e
      hfSplit hPerfSplit hTorSplit hSplit hfKill hsubKill

/-- Helper for Lemma 15.77.4: specialize Lemma `15.77.2` to the zero-fiber case and choose one
away-localization where the degree-`i` localized homology already vanishes. -/
private theorem exists_localizationAway_split_truncLE_and_homology_isZero_of_residueField_homology_isZero
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hHi : IsZero ((Hκ i).obj (K ⊗[R]^L[κ]))) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away f)) i).obj
        (K ⊗[R]^L[Localization.Away f])) ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        HasTorAmplitudeGE
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          ∃! e :
              K ⊗[R]^L[Localization.Away f] ≅
                (t.truncLE i).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                  (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
            ((t.truncLEι i).app (K ⊗[R]^L[Localization.Away f])) ≫ e.hom = biprod.inl ∧
              e.hom ≫ biprod.snd =
                ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away f])) := by
  rcases
      exists_termwiseFiniteFree_model_with_residueField_homology_isZero
        (𝔭 := 𝔭) K i hK hHi with
    ⟨E, b, hE, hEfree, e, hHiE⟩
  -- Proof comment: after this reduction, the only remaining source-level work is the matrix
  -- argument on the representative `E` in degrees `i - 1`, `i`, and `i + 1`.
  simpa [e] using
    exists_localizationAway_split_truncLE_and_homology_isZero_of_termwiseFiniteFree_model
      (𝔭 := 𝔭) K i E b hE hEfree e hHiE

/-- Lemma 15.77.4: if `K^•` is a pseudo-coherent complex of `R`-modules and
`H^i(K^• \otimes_R^{\mathbf L} \kappa(\mathfrak p)) = 0`, then after inverting some
`f \notin \mathfrak p` the localized object `K^• \otimes_R^{\mathbf L} R_f` admits a canonical
direct-sum decomposition
`τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f) ⊕ τ_{\le i - 1}(K^• \otimes_R^{\mathbf L} R_f)`
in `D(R_f)`, and the upper summand is perfect with tor-amplitude in `[i + 1, ∞]`. -/
theorem exists_localizationAway_gapSplit_of_residueField_homology_isZero
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hHi : IsZero ((Hκ i).obj (K ⊗[R]^L[κ]))) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        HasTorAmplitudeGE
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          ∃! e :
              K ⊗[R]^L[Localization.Away f] ≅
                (t.truncLE (i - 1)).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                  (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
            ((t.truncLEι (i - 1)).app (K ⊗[R]^L[Localization.Away f])) ≫ e.hom = biprod.inl ∧
              e.hom ≫ biprod.snd =
                ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away f])) := by
  rcases
      exists_localizationAway_split_truncLE_and_homology_isZero_of_residueField_homology_isZero
        (𝔭 := 𝔭) K i hK hHi with
    ⟨f, hf, hHf, hPerf, hTor, hsplit⟩
  let Kf := K ⊗[R]^L[Localization.Away f]
  let eLE : (t.truncLE (i - 1)).obj Kf ≅ (t.truncLE i).obj Kf :=
    truncLE_step_iso_of_homology_isZero (A := Localization.Away f) Kf i hHf
  have hι :
      eLE.hom ≫ (t.truncLEι i).app Kf =
        (t.truncLEι (i - 1)).app Kf := by
    -- Proof comment: this is the canonical compatibility of adjacent lower truncations.
    simpa [eLE] using t.ι_natTransTruncLEOfLE_app (i - 1) i (by omega) Kf
  have hsplit' :
      ∃! e : Kf ≅
          (t.truncLE (i - 1)).obj Kf ⊞
            (t.truncGE (i + 1)).obj Kf,
        ((t.truncLEι (i - 1)).app Kf) ≫ e.hom = biprod.inl ∧
          e.hom ≫ biprod.snd = ((t.truncGEπ (i + 1)).app Kf) := by
    -- Proof comment: transport the unique `τ≤ i ⊞ τ≥ i + 1` split across the one-step
    -- identification `τ≤ i - 1 ≅ τ≤ i` coming from the vanishing of localized `H^i`.
    exact
      transport_unique_gap_split_of_truncLE_iso (A := Localization.Away f) Kf i
        ((t.truncGE (i + 1)).obj Kf) ((t.truncGEπ (i + 1)).app Kf) hι hsplit
  exact ⟨f, hf, hPerf, hTor, hsplit'⟩

end

end CategoryTheory
