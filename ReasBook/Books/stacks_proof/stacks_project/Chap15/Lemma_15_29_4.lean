import Mathlib.Algebra.Homology.AlternatingConst
import Mathlib.Algebra.Homology.Homotopy
import StacksProject_2024.Chap14.Lemma_14_28_5
import StacksProject_2024.Chap14.Lemma_14_28_7
import StacksProject_2024.Chap15.Lemma_15_29_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open HomologicalComplex
open ZeroObject
open LocalizedModule

noncomputable section

universe u v

/-
Domain-style sampling:
- primary domain: localization families and the extended alternating Čech complex of an
  `R`-module;
- sampled owner declarations:
  `awayLocalizationFamilyMap`,
  `extendedAlternatingCechComplex`,
  `CategoryTheory.cechConerveRetraction_comp_coaugmentation_homotopic_id`,
  `CategoryTheory.CosimplicialObject.alternatingCofaceMapComplex_map_isHomotopyEquivalence`;
- best owner abstraction: the source-facing statement here is the contractibility of the canonical
  owner `extendedAlternatingCechComplex f M` under the unit-at-one-index hypothesis, while the
  split-mono and Čech-conerve homotopy machinery remains derived bridge data from the Chapter 10
  and Chapter 14 owners.

Primitive data is only the canonical localization-family map `awayLocalizationFamilyMap M f`.
The retraction of that map and the resulting homotopy-equivalence-to-zero statement are derived
API and should not be repackaged as new owners.
-/

section

variable {R : Type u} [CommRing R]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]
variable {r : ℕ}

/-- Scalar multiplication by an element of the powers of a unit is an invertible endomorphism of
an `R`-module. -/
private theorem powers_endomorphism_isUnit_of_isUnit (x : R) (hx : IsUnit x)
    (s : Submonoid.powers x) :
    IsUnit ((algebraMap R (Module.End R M)) s) := by
  -- Unpack the chosen power of `x` and map the corresponding unit witness to `Module.End R M`.
  rcases s.2 with ⟨n, hn⟩
  rw [← hn]
  simpa using (hx.map (algebraMap R (Module.End R M))).pow n

private abbrev awayLocalizationFamilyMapSection (f : Fin r → R) (i : Fin r)
    [Fact (IsUnit (f i))] :
    ModuleCat.of R (∀ j : Fin r, LocalizedModule.Away (f j) M) ⟶ ModuleCat.of R M :=
  ModuleCat.ofHom <|
    (LocalizedModule.lift (Submonoid.powers (f i)) (LinearMap.id)
        (powers_endomorphism_isUnit_of_isUnit (f i) (Fact.out : IsUnit (f i)))).comp
      (LinearMap.proj i)

/-- Helper for Lemma 15.29.4: the explicit section obtained from a unit entry is a left inverse to
the canonical localization-family map. -/
private theorem awayLocalizationFamilyMap_comp_section_eq_id (f : Fin r → R) (i : Fin r)
    [Fact (IsUnit (f i))] :
    ModuleCat.ofHom (awayLocalizationFamilyMap M f) ≫ awayLocalizationFamilyMapSection (M := M) f i =
      𝟙 (ModuleCat.of R M) := by
  -- Evaluate the composite on underlying elements and simplify the localization lift at the unit.
  refine ModuleCat.hom_ext ?_
  ext m
  simp [awayLocalizationFamilyMapSection, awayLocalizationFamilyMap]

-- Proof sketch: project to the `i`th factor and apply the localization universal property with
-- `g = LinearMap.id`; because `f i` is a unit, the resulting lift is inverse to
-- `LocalizedModule.mkLinearMap`, so the canonical localization-family map admits a retraction.
/-- If one entry `f i` is a unit, the canonical localization-family map is split mono. -/
theorem awayLocalizationFamilyMap_isSplitMono_of_isUnit_at (f : Fin r → R) (i : Fin r)
    (hi : IsUnit (f i)) :
    IsSplitMono (ModuleCat.ofHom (awayLocalizationFamilyMap M f)) := by
  letI : Fact (IsUnit (f i)) := ⟨hi⟩
  -- Package the explicit section together with its left-inverse identity.
  refine IsSplitMono.mk' ?_
  exact ⟨awayLocalizationFamilyMapSection f i, awayLocalizationFamilyMap_comp_section_eq_id
    (M := M) f i⟩

/-- Helper for Lemma 15.29.4: the Čech-conerve coaugmentation of the localization-family map is a
cosimplicial homotopy equivalence once one localizing entry is a unit. -/
private theorem cech_conerve_coaugmentation_isHomotopyEquivalence_of_isUnit_at
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    CategoryTheory.CosimplicialObject.IsHomotopyEquivalence
      (Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom := by
  letI : Fact (IsUnit (f i)) := ⟨hi⟩
  let s := awayLocalizationFamilyMapSection (M := M) f i
  have hs :
      ModuleCat.ofHom (awayLocalizationFamilyMap M f) ≫ s = 𝟙 (ModuleCat.of R M) := by
    -- Reuse the explicit section computation already proved above.
    simpa [s] using awayLocalizationFamilyMap_comp_section_eq_id (M := M) f i
  -- The Chapter 14 retract data packages the coaugmentation as a source-faithful homotopy
  -- equivalence of cosimplicial objects.
  refine ⟨{
    hom := (Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom
    inv := CategoryTheory.cechConerveRetraction
      (ModuleCat.ofHom (awayLocalizationFamilyMap M f)) s hs
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_
  }, rfl⟩
  · -- The coaugmentation-retraction composite is strictly the identity on the constant object.
    have hcoaug :
        (Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom ≫
            CategoryTheory.cechConerveRetraction
              (ModuleCat.ofHom (awayLocalizationFamilyMap M f)) s hs =
          𝟙 ((CosimplicialObject.const (ModuleCat R)).obj (ModuleCat.of R M)) := by
      simpa using CategoryTheory.cechConerveCoaugmentation_comp_retraction
        (ModuleCat.ofHom (awayLocalizationFamilyMap M f)) s hs
    exact hcoaug ▸ CategoryTheory.CosimplicialObject.DeltaOneHomotopic.refl _
  · -- Chapter 14 already identifies the reverse composite with the identity up to `Δ[1]`-homotopy.
    exact CategoryTheory.cechConerveRetraction_comp_coaugmentation_deltaOneHomotopic_id
      (ModuleCat.ofHom (awayLocalizationFamilyMap M f)) s hs

/-- Helper for Lemma 15.29.4: after applying the alternating coface map complex functor, the
Čech-conerve coaugmentation remains a homotopy equivalence of cochain complexes. -/
private theorem alternating_cech_coaugmentation_map_isHomotopyEquivalence_of_isUnit_at
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{max u v} R) (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex (ModuleCat.{max u v} R)).map
        (Arrow.mk (ModuleCat.ofHom (awayLocalizationFamilyMap M f))).augmentedCechConerve.hom) := by
  -- Transport the cosimplicial homotopy equivalence through Lemma `14.28.7`.
  exact
    CategoryTheory.CosimplicialObject.alternatingCofaceMapComplex_map_isHomotopyEquivalence
      (cech_conerve_coaugmentation_isHomotopyEquivalence_of_isUnit_at (M := M) f i hi)

/-- Helper for Lemma 15.29.4: for a homotopy equivalence out of `single₀ X`, the degree-zero
component of the chosen inverse is already a strict right inverse. -/
private theorem single₀_degree_zero_retraction
    {C : CochainComplex (ModuleCat.{max u v} R) ℕ} {X : ModuleCat.{max u v} R}
    (e : HomotopyEquiv ((CochainComplex.single₀ (ModuleCat.{max u v} R)).obj X) C) :
    e.hom.f 0 ≫ e.inv.f 0 = 𝟙 X := by
  -- In degree `0`, every neighboring differential of `single₀ X` vanishes, so the single-side
  -- homotopy is forced to be strict on components.
  have h := e.homotopyHomInvId.comm 0
  rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
    HomologicalComplex.single_obj_d, zero_comp, zero_add] at h
  rw [zero_add] at h
  simpa [HomologicalComplex.comp_f] using h

/-- Helper for Lemma 15.29.4: the inverse-side homotopy rewrites the identity on `C.X 0` as the
chosen degree-zero retraction followed by the augmentation, up to an explicit boundary term. -/
private theorem single₀_degree_zero_id_decomposition
    {C : CochainComplex (ModuleCat.{max u v} R) ℕ} {X : ModuleCat.{max u v} R}
    (e : HomotopyEquiv ((CochainComplex.single₀ (ModuleCat.{max u v} R)).obj X) C) :
    𝟙 (C.X 0) =
      e.inv.f 0 ≫ e.hom.f 0 +
        C.d 0 1 ≫ (-e.homotopyInvHomId.hom 1 0) := by
  -- Rewrite the degree-zero commutativity relation from the inverse-side homotopy so the
  -- boundary term appears on the right-hand side.
  calc
    𝟙 (C.X 0) =
        (C.d 0 1 ≫ e.homotopyInvHomId.hom 1 0 + 𝟙 (C.X 0)) +
          C.d 0 1 ≫ (-e.homotopyInvHomId.hom 1 0) := by
          simpa [Preadditive.comp_neg, add_assoc, add_left_comm, add_comm]
    _ = e.inv.f 0 ≫ e.hom.f 0 + C.d 0 1 ≫ (-e.homotopyInvHomId.hom 1 0) := by
          have h0 :
              e.inv.f 0 ≫ e.hom.f 0 =
                C.d 0 1 ≫ e.homotopyInvHomId.hom 1 0 + 𝟙 (C.X 0) := by
            have h := e.homotopyInvHomId.comm 0
            rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
              zero_add, add_zero] at h
            simpa [HomologicalComplex.comp_f] using h
          rw [h0]

/-- Helper for Lemma 15.29.4: any morphism out of a degree-zero single cochain complex vanishes in
positive degrees. -/
private theorem single₀_to_complex_f_succ
    {C : CochainComplex (ModuleCat.{max u v} R) ℕ} {X : ModuleCat.{max u v} R}
    (φ : (CochainComplex.single₀ (ModuleCat.{max u v} R)).obj X ⟶ C) (n : ℕ) :
    φ.f (n + 1) = 0 := by
  -- The source object in positive degree is zero, so every component there vanishes.
  exact
    (isZero_single_obj_X (ComplexShape.up ℕ) 0 X (n + 1) (by simp)).eq_of_src _ _

/-- Helper for Lemma 15.29.4: any morphism into a degree-zero single cochain complex vanishes in
positive degrees. -/
private theorem complex_to_single₀_f_succ
    {C : CochainComplex (ModuleCat.{max u v} R) ℕ} {X : ModuleCat.{max u v} R}
    (φ : C ⟶ (CochainComplex.single₀ (ModuleCat.{max u v} R)).obj X) (n : ℕ) :
    φ.f (n + 1) = 0 := by
  -- The target object in positive degree is zero, so every component there vanishes.
  exact
    (isZero_single_obj_X (ComplexShape.up ℕ) 0 X (n + 1) (by simp)).eq_of_tgt _ _

/-- Helper for Lemma 15.29.4: augmenting the degree-zero single complex by the identity produces
a contractible two-term cochain complex. -/
private theorem fromSingle₀AsComplex_single₀_id_homotopyEquivalent_zero
    (X : ModuleCat.{max u v} R) :
    Nonempty
      (HomotopyEquiv
        (CochainComplex.fromSingle₀AsComplex
          ((CochainComplex.single₀ (ModuleCat.{max u v} R)).obj X) X (𝟙 _)) 0) := by
  let E :=
    CochainComplex.fromSingle₀AsComplex
      ((CochainComplex.single₀ (ModuleCat.{max u v} R)).obj X) X (𝟙 _)
  have hIdZero : Homotopy (𝟙 E) 0 := by
    refine Homotopy.mkCoinductive (e := 𝟙 E) (zero := 𝟙 X) ?_ (one := 0) ?_ ?_
    · -- The degree-zero differential of the augmented single complex is the identity on `X`.
      simpa [E, CochainComplex.fromSingle₀AsComplex, CochainComplex.fromSingle₀Equiv,
        HomologicalComplex.single_obj_d]
    · -- In degree `1`, the only nonzero term comes from the degree-zero contraction component.
      rw [comp_zero, add_zero]
      simpa [E, CochainComplex.fromSingle₀AsComplex, CochainComplex.fromSingle₀Equiv,
        HomologicalComplex.single_obj_d]
    · intro n p
      -- From degree `2` onward the complex is supported on zero objects, so the recursive step is
      -- forced to be zero.
      refine ⟨0, ?_⟩
      exact (isZero_single_obj_X (ComplexShape.up ℕ) 0 X (n + 1) (by simp)).eq_of_tgt _ _
  -- Package the explicit contraction as a homotopy equivalence to the zero complex.
  exact ⟨{
    hom := 0
    inv := 0
    homotopyHomInvId := hIdZero.symm
    homotopyInvHomId := Homotopy.ofEq (by simp)
  }⟩

/-- Helper for Lemma 15.29.4: a contracting homotopy of the identity packages directly into a
homotopy equivalence with the zero complex. -/
private theorem homotopyEquivalent_zero_of_contracting_homotopy
    {C : CochainComplex (ModuleCat.{max u v} R) ℕ}
    (h : Homotopy (𝟙 C) 0) :
    Nonempty (HomotopyEquiv C 0) := by
  -- The only nontrivial side of the homotopy-equivalence data is the contraction of `𝟙 C`.
  exact ⟨{
    hom := 0
    inv := 0
    homotopyHomInvId := h.symm
    homotopyInvHomId := Homotopy.ofEq (by simp)
  }⟩

/-- Helper for Lemma 15.29.4: the alternating coface complex of the constant cosimplicial object
has the expected alternating `0/𝟙` differential. -/
private theorem constant_alternating_coface_d_eq (X : ModuleCat.{max u v} R) (n : ℕ) :
    ((alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
        ((CosimplicialObject.const (ModuleCat.{max u v} R)).obj X)).d n (n + 1) =
      if Even n then 0 else 𝟙 X := by
  -- Rewrite the constant differential as an alternating sum of identity maps and collapse the
  -- coefficient with `Fin.sum_neg_one_pow`.
  have hsum :
      (∑ x : Fin (n + 2), (-1 : ℤ) ^ (x : ℕ) • 𝟙 X) = if Even n then 0 else 𝟙 X := by
    rw [← Finset.sum_smul]
    simp [Fin.sum_neg_one_pow, Nat.even_add_one, -Nat.not_even_iff_odd]
  simpa [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
    AlternatingCofaceMapComplex.objD, CosimplicialObject.δ] using hsum

/-- Helper for Lemma 15.29.4: the degree-zero map from `single₀ X` to the constant alternating
coface complex satisfies the cocycle condition. -/
private theorem constant_alternating_coface_augmentation_w
    (X : ModuleCat.{max u v} R) :
    𝟙 X ≫
      ((alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
        ((CosimplicialObject.const (ModuleCat.{max u v} R)).obj X)).d 0 1 = 0 := by
  -- Specialize the constant differential formula to degree `0`, where the differential vanishes.
  rw [Category.id_comp, constant_alternating_coface_d_eq (R := R) X 0]
  rfl

/-- Helper for Lemma 15.29.4: the canonical map `single₀ X ⟶ s(const X)` is concentrated in
degree `0`. -/
private noncomputable abbrev constant_alternating_coface_augmentation
    (X : ModuleCat.{max u v} R) :
    (CochainComplex.single₀ (ModuleCat.{max u v} R)).obj X ⟶
      (alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
        ((CosimplicialObject.const (ModuleCat.{max u v} R)).obj X) :=
  (CochainComplex.fromSingle₀Equiv
      ((alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
        ((CosimplicialObject.const (ModuleCat.{max u v} R)).obj X)) X).symm
    ⟨𝟙 X, constant_alternating_coface_augmentation_w (R := R) X⟩

/-- Helper for Lemma 15.29.4: the positive-degree components of the canonical map
`single₀ X ⟶ s(const X)` vanish. -/
private theorem constant_alternating_coface_augmentation_f_succ
    (X : ModuleCat.{max u v} R) (n : ℕ) :
    (constant_alternating_coface_augmentation (R := R) X).f (n + 1) = 0 := by
  rfl

/-- Helper for Lemma 15.29.4: the canonical projection from the constant alternating coface complex
to `single₀ X` is concentrated in degree `0`. -/
private noncomputable abbrev constant_alternating_coface_projection
    (X : ModuleCat.{max u v} R) :
    (alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
        ((CosimplicialObject.const (ModuleCat.{max u v} R)).obj X) ⟶
      (CochainComplex.single₀ (ModuleCat.{max u v} R)).obj X :=
  (CochainComplex.toSingle₀Equiv
      ((alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
        ((CosimplicialObject.const (ModuleCat.{max u v} R)).obj X)) X).symm
    (𝟙 X)

/-- Helper for Lemma 15.29.4: the projection-reinclusion on the constant alternating coface
complex is homotopic to the identity by the standard alternating contraction. -/
private theorem constant_alternating_coface_projection_homotopic_id
    (X : ModuleCat.{max u v} R) :
    Nonempty
      (Homotopy
        (constant_alternating_coface_projection (R := R) X ≫
          constant_alternating_coface_augmentation (R := R) X)
        (𝟙 ((alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
          ((CosimplicialObject.const (ModuleCat.{max u v} R)).obj X)))) := by
  -- TODO: package the source-faithful alternating contraction `0, -𝟙, 0, -𝟙, ...` as a homotopy
  -- of `(projection ≫ augmentation) - 𝟙` to zero, then transport it back with
  -- `Homotopy.equivSubZero`.
  sorry

/-- Helper for Lemma 15.29.4: the constant alternating coface complex is homotopy equivalent to
the degree-zero single complex on the same module. -/
private theorem constant_alternating_coface_homotopy_equiv_single₀
    (X : ModuleCat.{max u v} R) :
    Nonempty
      (HomotopyEquiv
        ((alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
          ((CosimplicialObject.const (ModuleCat.{max u v} R)).obj X))
        ((CochainComplex.single₀ (ModuleCat.{max u v} R)).obj X)) := by
  -- TODO: combine the explicit projection/inclusion pair with the contracting homotopy above and
  -- the strict `single₀`-side identity.
  sorry

/-- Helper for Lemma 15.29.4: the composite of the constant-side inclusion with the Čech
coaugmentation is exactly the ordinary alternating Čech augmentation. -/
private theorem alternatingCechComplexAugmentation_eq_constant_composite
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    let eConst :=
      Classical.choice
        (constant_alternating_coface_homotopy_equiv_single₀ (R := R) (ModuleCat.of R M))
    let eCech :=
      Classical.choose
        (alternating_cech_coaugmentation_map_isHomotopyEquivalence_of_isUnit_at (M := M) f i hi)
    eConst.symm.hom ≫ eCech.hom = alternatingCechComplexAugmentation f M := by
  -- TODO: once `eConst.symm.hom` is identified with the explicit constant augmentation, compare
  -- degree `0` with the Čech coaugmentation and use positive-degree vanishing on both sides.
  sorry

/-- Helper for Lemma 15.29.4: any augmentation coming from a homotopy equivalence
`single₀ X ≃ C` yields a contractible extended complex. -/
private theorem fromSingle₀AsComplex_homotopyEquivalent_zero_of_single₀_homotopy_equivalence
    {C : CochainComplex (ModuleCat.{max u v} R) ℕ} {X : ModuleCat.{max u v} R}
    (e : HomotopyEquiv ((CochainComplex.single₀ (ModuleCat.{max u v} R)).obj X) C) :
    Nonempty (HomotopyEquiv (CochainComplex.fromSingle₀AsComplex C X e.hom) 0) := by
  -- TODO: define the contracting homotopy degreewise by `e.inv.f 0` in degree `0` and the
  -- negated inverse-side homotopy components in higher degrees, then verify the commutativity
  -- relations using `single₀_degree_zero_retraction`, `single₀_degree_zero_id_decomposition`,
  -- `single₀_to_complex_f_succ`, and `complex_to_single₀_f_succ`.
  sorry

/-- Helper for Lemma 15.29.4: once the structural packaging route is complete, it yields an
actual contracting homotopy of the extended alternating Čech complex. -/
private theorem extended_alternating_cech_contracting_homotopy_of_isUnit_at_exists
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    Nonempty (Homotopy (𝟙 (extendedAlternatingCechComplex f M)) 0) := by
  -- TODO: after `extended_alternating_cech_contracting_homotopy_of_isUnit_at_aux` is completed,
  -- extract the contracting homotopy as the symmetry of its `homotopyHomInvId`.
  sorry

/-- Helper for Lemma 15.29.4: the unit-index Čech coaugmentation and the constant alternating
contraction combine to contract the extended alternating Čech complex. -/
private theorem extended_alternating_cech_contracting_homotopy_of_isUnit_at_aux
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    Nonempty (HomotopyEquiv (extendedAlternatingCechComplex f M) 0) := by
  let eConst :
      HomotopyEquiv
        ((alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
          ((CosimplicialObject.const (ModuleCat.{max u v} R)).obj (ModuleCat.of R M)))
        ((CochainComplex.single₀ (ModuleCat.{max u v} R)).obj (ModuleCat.of R M)) :=
    Classical.choice
      (constant_alternating_coface_homotopy_equiv_single₀ (R := R) (ModuleCat.of R M))
  let eCech :
      HomotopyEquiv
        ((alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
          ((CosimplicialObject.const (ModuleCat.{max u v} R)).obj (ModuleCat.of R M)))
        (alternatingCechComplex f M) :=
    Classical.choose
      (alternating_cech_coaugmentation_map_isHomotopyEquivalence_of_isUnit_at (M := M) f i hi)
  let eSingle :
      HomotopyEquiv
        ((CochainComplex.single₀ (ModuleCat.{max u v} R)).obj (ModuleCat.of R M))
        (alternatingCechComplex f M) :=
    eConst.symm.trans eCech
  have he :
      eSingle.hom = alternatingCechComplexAugmentation f M := by
    simpa [eSingle, eConst, eCech] using
      alternatingCechComplexAugmentation_eq_constant_composite (R := R) (M := M) f i hi
  -- Rewrite the augmentation in the owner definition to the homotopy-equivalence map `eSingle.hom`.
  simpa [extendedAlternatingCechComplex, he] using
    fromSingle₀AsComplex_homotopyEquivalent_zero_of_single₀_homotopy_equivalence
      eSingle

/-- Helper for Lemma 15.29.4: the source proof contracts the extended alternating Čech complex by
inserting the chosen unit index into each strictly increasing tuple of indices. -/
private noncomputable def extended_alternating_cech_contracting_homotopy_of_isUnit_at
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    Homotopy (𝟙 (extendedAlternatingCechComplex f M)) 0 :=
  Classical.choice
    (extended_alternating_cech_contracting_homotopy_of_isUnit_at_exists (R := R) (M := M) f i hi)

-- Proof sketch: follow the textbook contraction on the extended alternating Čech complex itself.
-- The chosen unit index `i` defines the homotopy by insertion into an ordered tuple, and the two
-- source-side cancellation cases yield a contraction of the identity.
/-- The extended alternating Čech complex is contractible as soon as one of the localizing
entries is a unit. -/
theorem extendedAlternatingCechComplex_homotopyEquivalent_zero_of_isUnit_at
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    Nonempty
      (HomotopyEquiv (extendedAlternatingCechComplex f M) 0) := by
  -- Route correction: package the direct source-style contraction instead of continuing the old
  -- augmentation-transport detour.
  exact
    homotopyEquivalent_zero_of_contracting_homotopy
      (extended_alternating_cech_contracting_homotopy_of_isUnit_at (M := M) f i hi)

-- Proof sketch: choose an index `i` for which `f i` is a unit and apply the indexed contractibility
-- statement.
/-- Lemma 15.29.4: if one of the localizing elements in the finite family `f` is a unit, then the
extended alternating Čech complex of the `R`-module `M` is homotopy equivalent to the zero
cochain complex. -/
@[stacks 0G6J]
theorem extendedAlternatingCechComplex_homotopyEquivalent_zero_of_exists_isUnit
    (f : Fin r → R) (hunit : ∃ i : Fin r, IsUnit (f i)) :
    Nonempty
      (HomotopyEquiv (extendedAlternatingCechComplex f M) 0) := by
  rcases hunit with ⟨i, hi⟩
  exact extendedAlternatingCechComplex_homotopyEquivalent_zero_of_isUnit_at f i hi

end
