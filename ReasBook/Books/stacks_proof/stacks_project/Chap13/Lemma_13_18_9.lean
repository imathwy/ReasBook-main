import Mathlib
import StacksProject_2024.Chap13.Definition_13_18_1
import StacksProject_2024.Chap13.Lemma_13_18_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory
open scoped ZeroObject

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling:
- primary domain: short exact sequences of bounded-below cochain complexes and compatible
  bounded-below injective resolutions;
- sampled owner declarations:
  `CategoryTheory.ShortComplex.Hom`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CochainComplex.PlusWithTermsIn.ι`,
  `CochainComplex.plus`,
  `CochainComplex.InjectivePlus`,
  `CochainComplex.InjectiveResolution`;
- best owner abstraction: the resolving row should be owned by
  `ShortComplex (InjectivePlus 𝒜)`, its comparison with the given short exact sequence by a
  single `ShortComplex.Hom`, and short exactness by `ShortComplex.ShortExact`;
- primitive data here: the short exact resolving row in `InjectivePlus 𝒜`, the morphism from `S`
  to its underlying short complex, and the quasi-isomorphism witnesses on the three vertical
  components;
- derived API here: the source-facing existence theorems below, with any columnwise
  `InjectiveResolution` view recovered directly from the canonical row and comparison morphism.

Source/core/bridge triage:
- `source-facing`: the injective-resolution diagram data above a bounded-below short exact
  sequence, together with its existence theorems;
- `core/canonical`: `ShortComplex (InjectivePlus 𝒜)`, `ShortComplex.Hom`,
  `ShortComplex.ShortExact`, `CochainComplex.InjectiveResolution`, and the generic
  extension-closure interface `ObjectProperty.prop_X₂_of_shortExact`;
- `bridge/view`: the `strictlyGE_zero` existence specializations below.
-/

local notation "injPlusι" => PlusWithTermsIn.ι (isInjective 𝒜)

section

variable [EnoughInjectives 𝒜]

/-- Helper for Lemma 13.18.9: the comparison map of an injective resolution is a quasi-isomorphism
by definition. -/
private theorem injectiveResolution_map_quasiIso {K : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) : QuasiIso I.ι := by
  -- This is exactly the bundled quasi-isomorphism field of `InjectiveResolution`.
  infer_instance

/-- Helper for Lemma 13.18.9: in a morphism between short exact rows of cochain complexes,
quasi-isomorphisms on the outer vertical maps force a quasi-isomorphism on the middle map. -/
theorem quasiIso_tau₂_of_shortExact
    {S T : ShortComplex (CochainComplex 𝒜 ℤ)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (hτ₁ : QuasiIso φ.τ₁) (hτ₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  -- Route correction: compare the derived triangles of the two short exact rows and apply the
  -- triangulated two-out-of-three lemma to the first and third components.
  let φQ := triangleOfSES.map hS hT φ
  have hSQ : triangleOfSES hS ∈ distTriang (DerivedCategory 𝒜) := by
    simpa using triangleOfSES_distinguished hS
  have hTQ : triangleOfSES hT ∈ distTriang (DerivedCategory 𝒜) := by
    simpa using triangleOfSES_distinguished hT
  have hQ₁ : IsIso φQ.hom₁ := by
    simpa [φQ] using ((isIso_Q_map_iff_quasiIso 𝒜 φ.τ₁).2 hτ₁)
  have hQ₃ : IsIso φQ.hom₃ := by
    simpa [φQ] using ((isIso_Q_map_iff_quasiIso 𝒜 φ.τ₃).2 hτ₃)
  have hQ₂ : IsIso φQ.hom₂ := by
    simpa [φQ] using (isIso₂_of_isIso₁₃ φQ hSQ hTQ hQ₁ hQ₃ : IsIso φQ.hom₂)
  exact (isIso_Q_map_iff_quasiIso 𝒜 φ.τ₂).1 (by simpa [φQ] using hQ₂)

/-- Helper for Lemma 13.18.9: bounded-below cochain complexes are closed under short exact
extensions. -/
private theorem plus_of_shortExact
    {S : ShortComplex (CochainComplex 𝒜 ℤ)} (hS : S.ShortExact)
    (hA : CochainComplex.plus 𝒜 S.X₁) (hC : CochainComplex.plus 𝒜 S.X₃) :
    CochainComplex.plus 𝒜 S.X₂ := by
  obtain ⟨a, hA'⟩ := (CochainComplex.plus_iff 𝒜 S.X₁).1 hA
  obtain ⟨c, hC'⟩ := (CochainComplex.plus_iff 𝒜 S.X₃).1 hC
  refine (CochainComplex.plus_iff 𝒜 S.X₂).2 ⟨min a c, ?_⟩
  -- Below the common lower bound, both outer terms vanish degreewise.
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  let Si : ShortComplex 𝒜 := S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
  let hSi : Si.ShortExact := by
    simpa using hS.map_of_exact (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
  have h₁ : CategoryTheory.Limits.IsZero (S.X₁.X i) := by
    let _ : S.X₁.IsStrictlyGE a := hA'
    exact S.X₁.isZero_of_isStrictlyGE a i (lt_of_lt_of_le hi (min_le_left _ _))
  have h₃ : CategoryTheory.Limits.IsZero (S.X₃.X i) := by
    let _ : S.X₃.IsStrictlyGE c := hC'
    exact S.X₃.isZero_of_isStrictlyGE c i (lt_of_lt_of_le hi (min_le_right _ _))
  -- Exactness with zero left term makes the right map monic, and a monomorphism into a zero
  -- object forces the middle term itself to be zero.
  have hmono : Mono Si.g := by
    exact (Si.exact_iff_mono (h₁.eq_of_src _ _)).1 hSi.exact
  letI : Mono Si.g := hmono
  simpa [Si] using CategoryTheory.Limits.IsZero.of_mono Si.g h₃

/-- Helper for Chap13 Lemma 13 18 9: the degreewise horseshoe data comes from extending the left
resolution map across `S.f`, descending its chain-map obstruction across `S.g`, and then
extending that descended obstruction across the termwise monomorphism `K.ι`. -/
private theorem leftLiftDescendsAlongCokernel
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (K : InjectiveResolution S.X₃)
    (hKmono : ∀ n : ℤ, Mono (K.ι.f n)) :
    ∃ (leftLift : ∀ n : ℤ, S.X₂.X n ⟶ (I : CochainComplex 𝒜 ℤ).X n)
      (delta : ∀ n : ℤ, S.X₃.X n ⟶ (I : CochainComplex 𝒜 ℤ).X (n + 1))
      (gamma : ∀ n : ℤ, (K : CochainComplex 𝒜 ℤ).X n ⟶ (I : CochainComplex 𝒜 ℤ).X (n + 1)),
        (∀ n : ℤ, S.f.f n ≫ leftLift n = I.ι.f n) ∧
          (∀ n : ℤ,
            S.g.f n ≫ delta n =
              S.X₂.d n (n + 1) ≫ leftLift (n + 1) -
                leftLift n ≫ (I : CochainComplex 𝒜 ℤ).d n (n + 1)) ∧
          ∀ n : ℤ, K.ι.f n ≫ gamma n = delta n := by
  let evalShort (n : ℤ) : ShortComplex 𝒜 :=
    S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
  have hEvalShort (n : ℤ) : (evalShort n).ShortExact := by
    -- Each degreewise row remains short exact after evaluation.
    simpa [evalShort] using hS.map_of_exact (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
  let leftLift (n : ℤ) : S.X₂.X n ⟶ (I : CochainComplex 𝒜 ℤ).X n :=
    let _ : Mono (S.f.f n) := by
      simpa [evalShort] using (hEvalShort n).mono_f
    Injective.factorThru (I.ι.f n) (S.f.f n)
  have leftLift_comp (n : ℤ) : S.f.f n ≫ leftLift n = I.ι.f n := by
    -- Injectivity of the target extends the left resolution map across the monomorphism `S.f`.
    let _ : Mono (S.f.f n) := by
      simpa [evalShort] using (hEvalShort n).mono_f
    dsimp [leftLift]
    exact Injective.comp_factorThru (I.ι.f n) (S.f.f n)
  let obstruction (n : ℤ) : S.X₂.X n ⟶ (I : CochainComplex 𝒜 ℤ).X (n + 1) :=
    S.X₂.d n (n + 1) ≫ leftLift (n + 1) -
      leftLift n ≫ (I : CochainComplex 𝒜 ℤ).d n (n + 1)
  have obstruction_comp_zero (n : ℤ) : S.f.f n ≫ obstruction n = 0 := by
    -- The obstruction vanishes on `S.X₁` because both rows are chain maps there.
    dsimp [obstruction]
    rw [Preadditive.comp_sub]
    simp_rw [Category.assoc]
    rw [S.f.comm_assoc, leftLift_comp, leftLift_comp, I.ι.comm]
    abel_nf
  let delta (n : ℤ) : S.X₃.X n ⟶ (I : CochainComplex 𝒜 ℤ).X (n + 1) :=
    let hExactEpi :
        (evalShort n).Exact ∧ Epi (evalShort n).g :=
      ⟨(hEvalShort n).exact, by simpa [evalShort] using (hEvalShort n).epi_g⟩
    let hCok :
        IsColimit (CokernelCofork.ofπ (evalShort n).g (evalShort n).zero) :=
      ((evalShort n).exact_and_epi_g_iff_g_is_cokernel).1 hExactEpi |>.some
    hCok.desc (CokernelCofork.ofπ (obstruction n) (obstruction_comp_zero n))
  have delta_fac (n : ℤ) :
      S.g.f n ≫ delta n =
        S.X₂.d n (n + 1) ≫ leftLift (n + 1) -
          leftLift n ≫ (I : CochainComplex 𝒜 ℤ).d n (n + 1) := by
    -- Exactness identifies `S.g` as the cokernel of `S.f`, so the obstruction descends uniquely.
    dsimp [delta]
    let hExactEpi :
        (evalShort n).Exact ∧ Epi (evalShort n).g :=
      ⟨(hEvalShort n).exact, by simpa [evalShort] using (hEvalShort n).epi_g⟩
    let hCok :
        IsColimit (CokernelCofork.ofπ (evalShort n).g (evalShort n).zero) :=
      ((evalShort n).exact_and_epi_g_iff_g_is_cokernel).1 hExactEpi |>.some
    simpa [obstruction, evalShort] using
      hCok.fac (CokernelCofork.ofπ (obstruction n) (obstruction_comp_zero n))
        WalkingParallelPair.one
  let gamma (n : ℤ) : (K : CochainComplex 𝒜 ℤ).X n ⟶ (I : CochainComplex 𝒜 ℤ).X (n + 1) :=
    let _ : Mono (K.ι.f n) := hKmono n
    Injective.factorThru (delta n) (K.ι.f n)
  have gamma_fac (n : ℤ) : K.ι.f n ≫ gamma n = delta n := by
    -- Injectivity of the left resolution terms extends the descended obstruction across `K.ι`.
    let _ : Mono (K.ι.f n) := hKmono n
    dsimp [gamma]
    exact Injective.comp_factorThru (delta n) (K.ι.f n)
  exact ⟨leftLift, delta, gamma, leftLift_comp, delta_fac, gamma_fac⟩

/-- Helper for Chap13 Lemma 13 18 9: the upper-right cross term in the raw injective horseshoe
differential vanishes after cancelling along the chosen right resolution and the cokernel map
of the original short exact row. -/
private theorem middleCrossZero
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (K : InjectiveResolution S.X₃)
    (hKmono : ∀ n : ℤ, Mono (K.ι.f n))
    (leftLift : ∀ n : ℤ, S.X₂.X n ⟶ (I : CochainComplex 𝒜 ℤ).X n)
    (delta : ∀ n : ℤ, S.X₃.X n ⟶ (I : CochainComplex 𝒜 ℤ).X (n + 1))
    (gamma : ∀ n : ℤ, (K : CochainComplex 𝒜 ℤ).X n ⟶ (I : CochainComplex 𝒜 ℤ).X (n + 1))
    (delta_fac : ∀ n : ℤ,
      S.g.f n ≫ delta n =
        S.X₂.d n (n + 1) ≫ leftLift (n + 1) -
        leftLift n ≫ (I : CochainComplex 𝒜 ℤ).d n (n + 1))
    (gamma_fac : ∀ n : ℤ, K.ι.f n ≫ gamma n = delta n) :
    ∀ n : ℤ,
      gamma n ≫ (I : CochainComplex 𝒜 ℤ).d (n + 1) (n + 1 + 1) +
        (K : CochainComplex 𝒜 ℤ).d n (n + 1) ≫ gamma (n + 1) = 0 := by
  -- Route correction: prove the cross term once in the raw cochain-complex world, before any
  -- attempt to package the middle complex as an `InjectivePlus`.
  let evalShort (n : ℤ) : ShortComplex 𝒜 :=
    S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
  have hEvalShort (n : ℤ) : (evalShort n).ShortExact := by
    -- Degreewise evaluation preserves short exactness of the given row.
    simpa [evalShort] using hS.map_of_exact (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
  intro n
  -- First move the cross term down to the cokernel side using the chosen monomorphism `K.ι`.
  let _ : Mono (K.ι.f n) := hKmono n
  apply (cancel_mono (K.ι.f n)).1
  rw [Category.assoc, gamma_fac, Category.assoc, K.ι.comm, Category.assoc, gamma_fac]
  -- Then descend along the epimorphism `S.g` to reach the normalized obstruction formula.
  let _ : Epi (S.g.f n) := by
    simpa [evalShort] using (hEvalShort n).epi_g
  apply (cancel_epi (S.g.f n)).1
  rw [Preadditive.comp_add, Category.assoc, delta_fac, S.g.comm_assoc, delta_fac]
  simp [Preadditive.comp_sub, Category.assoc]

/-- Helper for Chap13 Lemma 13 18 9: the raw biproduct middle complex inherits any common lower
bound of the two outer complexes. -/
private theorem middleComplexStrictlyGE
    (IC KC : CochainComplex 𝒜 ℤ)
    (middleD : ∀ n : ℤ, (IC.X n ⊞ KC.X n) ⟶ (IC.X (n + 1) ⊞ KC.X (n + 1)))
    (middleSq : ∀ n : ℤ, middleD n ≫ middleD (n + 1) = 0)
    (a : ℤ) (hIC : IC.IsStrictlyGE a) (hKC : KC.IsStrictlyGE a) :
    (CochainComplex.of (fun n ↦ IC.X n ⊞ KC.X n) middleD middleSq).IsStrictlyGE a := by
  -- The differential is irrelevant here; bounded-below is detected degreewise on objects.
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  let _ : IC.IsStrictlyGE a := hIC
  let _ : KC.IsStrictlyGE a := hKC
  have hIi : IsZero (IC.X i) := IC.isZero_of_isStrictlyGE a i hi
  have hKi : IsZero (KC.X i) := KC.isZero_of_isStrictlyGE a i hi
  simpa using (biprod_isZero_iff (IC.X i) (KC.X i)).2 ⟨hIi, hKi⟩

/-- Helper for Lemma 13.18.9: given chosen injective resolutions of the outer terms, the
horseshoe row can be built directly by the standard upper-triangular biproduct complex. The
helper also records that any common lower bound on the outer resolutions is inherited by the
middle one. -/
private theorem exists_split_injectiveRow_of_outerResolutions
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (K : InjectiveResolution S.X₃)
    (hKmono : ∀ n : ℤ, Mono (K.ι.f n)) :
    ∃ (J : InjectivePlus 𝒜) (f : I.complex ⟶ J) (g : J ⟶ K.complex) (hfg : f ≫ g = 0)
      (φ : S ⟶ (ShortComplex.mk f g hfg).map injPlusι),
        φ.τ₁ = I.ι ∧
          φ.τ₃ = K.ι ∧
          ((ShortComplex.mk f g hfg).map injPlusι).ShortExact ∧
          QuasiIso φ.τ₂ ∧
          ∀ a : ℤ,
            (I : CochainComplex 𝒜 ℤ).IsStrictlyGE a →
              (K : CochainComplex 𝒜 ℤ).IsStrictlyGE a →
                (J : CochainComplex 𝒜 ℤ).IsStrictlyGE a := by
  -- Route correction: the intended proof is the injective-side dual of `Lemma_13_19_9`,
  -- using a biproduct horseshoe complex built from factor-through maps and then
  -- `quasiIso_tau₂_of_shortExact` for the middle comparison.
  obtain ⟨leftLift, delta, gamma, leftLift_comp, delta_fac, gamma_fac⟩ :=
    leftLiftDescendsAlongCokernel (𝒜 := 𝒜) S hS I K hKmono
  let IC : CochainComplex 𝒜 ℤ := I
  let KC : CochainComplex 𝒜 ℤ := K
  let middleX : ℤ → 𝒜 := fun n ↦ IC.X n ⊞ KC.X n
  let middleD : ∀ n : ℤ, middleX n ⟶ middleX (n + 1) := fun n ↦
    biprod.lift
      (biprod.desc (IC.d n (n + 1)) (gamma n))
      (biprod.desc 0 (KC.d n (n + 1)))
  have middle_cross :
      ∀ n : ℤ,
        gamma n ≫ IC.d (n + 1) (n + 2) + KC.d n (n + 1) ≫ gamma (n + 1) = 0 :=
    middleCrossZero (𝒜 := 𝒜) S hS I K hKmono leftLift delta gamma delta_fac gamma_fac
  have middleSq : ∀ n : ℤ, middleD n ≫ middleD (n + 1) = 0 := by
    -- The upper-triangular differential squares to zero once the cross term vanishes.
    intro n
    apply biprod.hom_ext
    · simp [middleD, middle_cross, Category.assoc]
    · simp [middleD, Category.assoc]
  let JC : CochainComplex 𝒜 ℤ := CochainComplex.of middleX middleD middleSq
  have left_comm :
      ∀ n : ℤ, (biprod.inl : IC.X n ⟶ middleX n) ≫ middleD n =
        IC.d n (n + 1) ≫ (biprod.inl : IC.X (n + 1) ⟶ middleX (n + 1)) := by
    -- The left inclusion is a chain map because the differential is upper triangular.
    intro n
    simp [middleD]
  let f' : IC ⟶ JC :=
    CochainComplex.ofHom (fun n ↦ biprod.inl) left_comm
  have right_comm :
      ∀ n : ℤ, (biprod.snd : middleX n ⟶ KC.X n) ≫ KC.d n (n + 1) =
        middleD n ≫ (biprod.snd : middleX (n + 1) ⟶ KC.X (n + 1)) := by
    -- The right projection is a chain map for the same upper-triangular reason.
    intro n
    simp [middleD]
  let g' : JC ⟶ KC :=
    CochainComplex.ofHom (fun n ↦ biprod.snd) right_comm
  have hfg' : f' ≫ g' = 0 := by
    -- The composite of the inclusion and projection of the biproduct row is zero.
    ext n
    simp [f', g']
  have middle_map_comm :
      ∀ n : ℤ,
        biprod.lift (leftLift n) (S.g.f n ≫ K.ι.f n) ≫ middleD n =
          S.X₂.d n (n + 1) ≫
            biprod.lift (leftLift (n + 1)) (S.g.f (n + 1) ≫ K.ι.f (n + 1)) := by
    -- The comparison map satisfies the chain-map equation by `delta_fac` and the commutativity of
    -- the right resolution map.
    intro n
    apply biprod.hom_ext
    · simp_rw [Category.assoc]
      rw [biprod.lift_fst_assoc, delta_fac]
      simp [middleD]
    · simp [middleD, Category.assoc, K.ι.comm, S.g.comm_assoc]
  let middleMap : S.X₂ ⟶ JC :=
    CochainComplex.ofHom
      (fun n ↦ biprod.lift (leftLift n) (S.g.f n ≫ K.ι.f n)) middle_map_comm
  obtain ⟨aI, hI⟩ := I.exists_isStrictlyGE
  obtain ⟨aK, hK⟩ := K.exists_isStrictlyGE
  have hImin : IC.IsStrictlyGE (min aI aK) := by
    -- A smaller lower bound is still valid for a bounded-below complex.
    rw [CochainComplex.isStrictlyGE_iff] at hI ⊢
    intro i hi
    exact hI i (lt_of_lt_of_le hi (min_le_left _ _))
  have hKmin : KC.IsStrictlyGE (min aI aK) := by
    -- The same downgrade works for the right resolution.
    rw [CochainComplex.isStrictlyGE_iff] at hK ⊢
    intro i hi
    exact hK i (lt_of_lt_of_le hi (min_le_right _ _))
  have hJstrict : JC.IsStrictlyGE (min aI aK) := by
    -- The raw middle complex inherits the common lower bound degreewise.
    exact middleComplexStrictlyGE IC KC middleD middleSq (min aI aK) hImin hKmin
  have hJinj : ∀ n : ℤ, Injective (JC.X n) := by
    -- Each middle term is a biproduct of injective objects, hence injective.
    intro n
    dsimp [JC, middleX]
    infer_instance
  let J : InjectivePlus 𝒜 :=
    ⟨⟨JC, (CochainComplex.plus_iff 𝒜 JC).2 ⟨min aI aK, hJstrict⟩⟩, hJinj⟩
  let f : I.complex ⟶ J := f'
  let g : J ⟶ K.complex := g'
  have hfg : f ≫ g = 0 := by
    simpa [f, g] using hfg'
  have hrow_eval :
      ∀ n : ℤ,
        (((ShortComplex.mk f g hfg).map injPlusι).map
          (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).ShortExact := by
    -- Degreewise the lower row is the split biproduct short exact sequence.
    intro n
    simpa [f, g, hfg, f', g', J, JC, middleX, injPlusι] using
      (ShortComplex.Splitting.shortExact
        (ShortComplex.Splitting.ofHasBinaryBiproduct (IC.X n) (KC.X n)))
  have hrow : ((ShortComplex.mk f g hfg).map injPlusι).ShortExact := by
    -- Degreewise split exactness upgrades to exactness of cochain complexes.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact ?_
    intro n
    simpa [injPlusι] using hrow_eval n
  have hφ₁₂ : S.f ≫ middleMap = I.ι ≫ f := by
    -- The left square is the defining factor-through identity.
    ext n
    simp [middleMap, f, f', leftLift_comp, Category.assoc]
  have hφ₂₃ : middleMap ≫ g = S.g ≫ K.ι := by
    -- The right square is the tautological second component of `middleMap`.
    ext n
    simp [middleMap, g, g', Category.assoc]
  let φ : S ⟶ (ShortComplex.mk f g hfg).map injPlusι :=
    ShortComplex.homMk I.ι middleMap K.ι hφ₁₂ hφ₂₃
  have hφ₂ : QuasiIso φ.τ₂ := by
    -- The middle vertical map is a quasi-isomorphism by the outer-column comparison theorem.
    have hφ₁ : QuasiIso φ.τ₁ := by
      simpa [φ] using injectiveResolution_map_quasiIso I
    have hφ₃ : QuasiIso φ.τ₃ := by
      simpa [φ] using injectiveResolution_map_quasiIso K
    exact quasiIso_tau₂_of_shortExact hS hrow φ hφ₁ hφ₃
  refine ⟨J, f, g, hfg, φ, rfl, rfl, hrow, hφ₂, ?_⟩
  intro a hIa hKa
  -- Any common lower bound of the outer complexes is inherited by the biproduct middle complex.
  simpa [J, JC] using middleComplexStrictlyGE IC KC middleD middleSq a hIa hKa

-- Proof sketch: run the construction of `exists_injectiveResolutionDiagram_of_shortExact` starting
-- from the prescribed injective resolution of the left complex, then perform the pushout
-- reduction and the lifted-connecting-morphism construction relative to that fixed choice.
/-- Given a chosen injective resolution of the left complex, the diagram can be built with that
resolution as its left column, provided the outer terms of the short exact row are bounded below.
The middle term is then bounded below by short exactness. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.plus 𝒜 S.X₁) (hC : CochainComplex.plus 𝒜 S.X₃)
    (I : InjectiveResolution S.X₁) :
    ∃ (J K : InjectivePlus 𝒜) (f : I.complex ⟶ J) (g : J ⟶ K) (hfg : f ≫ g = 0)
      (φ : S ⟶ (ShortComplex.mk f g hfg).map injPlusι),
        φ.τ₁ = I.ι ∧
          ((ShortComplex.mk f g hfg).map injPlusι).ShortExact ∧
          QuasiIso φ.τ₂ ∧ QuasiIso φ.τ₃ := by
  have _hMiddle : CochainComplex.plus 𝒜 S.X₂ := plus_of_shortExact hS hA hC
  -- Route correction: choose the right injective resolution first, then apply the direct
  -- horseshoe construction for the two prescribed outer resolutions.
  obtain ⟨c, hC'⟩ := (CochainComplex.plus_iff 𝒜 S.X₃).1 hC
  obtain ⟨K, -, hKmono⟩ :=
    exists_injectiveResolution_strictlyGE_with_termwise_mono
      (𝒜 := 𝒜) (K := S.X₃) c hC'
  obtain ⟨J, f, g, hfg, φ, hφ₁, hφ₃, hrow, hφ₂, -⟩ :=
    exists_split_injectiveRow_of_outerResolutions (𝒜 := 𝒜) S hS I K hKmono
  refine ⟨J, K.complex, f, g, hfg, φ, hφ₁, hrow, hφ₂, ?_⟩
  -- The right column is the chosen injective resolution of `S.X₃`.
  simpa [hφ₃] using injectiveResolution_map_quasiIso K

-- Proof sketch: choose a bounded-below injective resolution of the left complex using
-- Lemma 13.18.3, then apply the prescribed-left-resolution theorem just proved above.
/-- Lemma 13.18.9: if `0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` is a short exact sequence of cochain complexes
whose outer terms are bounded below, then it extends to a commutative diagram whose vertical maps
are injective resolutions and whose lower row is again a short exact sequence of complexes. The
middle term is bounded below because bounded-below cochain complexes are closed under extensions.
-/
@[stacks 013T]
theorem exists_injectiveResolutionDiagram_of_shortExact
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.plus 𝒜 S.X₁) (hC : CochainComplex.plus 𝒜 S.X₃) :
    ∃ row : ShortComplex (InjectivePlus 𝒜), ∃ hom : S ⟶ row.map injPlusι,
      (row.map injPlusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧ QuasiIso hom.τ₂ ∧ QuasiIso hom.τ₃ := by
  -- Route correction: the source proof first fixes the left resolution and proves the stronger
  -- theorem; the present statement is only the wrapper that chooses such a resolution.
  obtain ⟨a, hA'⟩ := (CochainComplex.plus_iff 𝒜 S.X₁).1 hA
  obtain ⟨I, -, -⟩ :=
    exists_injectiveResolution_strictlyGE_with_termwise_mono
      (𝒜 := 𝒜) (K := S.X₁) a hA'
  -- Apply the prescribed-left-resolution theorem and then package its lower row.
  obtain ⟨J, K, f, g, hfg, φ, hφ₁, hrow, hφ₂, hφ₃⟩ :=
    exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution
      (S := S) hS hA hC I
  refine ⟨ShortComplex.mk f g hfg, φ, hrow, ?_, hφ₂, hφ₃⟩
  -- The left vertical map is the chosen injective-resolution map, hence a quasi-isomorphism.
  simpa [hφ₁] using injectiveResolution_map_quasiIso I

-- Proof sketch: choose the left and right injective resolutions using Lemma 13.18.3 with lower
-- bound `0`, so their targets are zero in negative degrees, and then carry out the same
-- upper-triangular construction of the middle resolution; the direct-sum model is also zero in
-- negative degrees.
-- Proof sketch: combine the prescribed-left-resolution construction with the bounded-below choice
-- from the previous theorem, using the given lower bound on the chosen left resolution to keep
-- the whole lower row zero in negative degrees.
/-- If the outer terms of the original sequence are zero in negative degrees and the chosen left
injective resolution is also zero in negative degrees, then the middle term is automatically zero
in negative degrees, and the diagram can be built with that prescribed left comparison map and
with the remaining resolving complexes zero in negative degrees. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution_strictlyGE_zero
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (hI : (I : CochainComplex 𝒜 ℤ).IsStrictlyGE 0)
    (hA : S.X₁.IsStrictlyGE 0) (hC : S.X₃.IsStrictlyGE 0) :
    ∃ (J K : InjectivePlus 𝒜) (f : I.complex ⟶ J) (g : J ⟶ K) (hfg : f ≫ g = 0)
      (φ : S ⟶ (ShortComplex.mk f g hfg).map injPlusι),
        φ.τ₁ = I.ι ∧
          ((ShortComplex.mk f g hfg).map injPlusι).ShortExact ∧
          QuasiIso φ.τ₂ ∧
          QuasiIso φ.τ₃ ∧
          (J : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
          (K : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 := by
  let _ := hA
  -- Use the same direct horseshoe construction, now with the right resolution chosen in degrees
  -- `≥ 0`, and inherit the common lower bound on the middle complex from the helper.
  obtain ⟨K, hK, hKmono⟩ :=
    exists_injectiveResolution_strictlyGE_with_termwise_mono
      (𝒜 := 𝒜) (K := S.X₃) 0 hC
  obtain ⟨J, f, g, hfg, φ, hφ₁, hφ₃, hrow, hφ₂, hbound⟩ :=
    exists_split_injectiveRow_of_outerResolutions (𝒜 := 𝒜) S hS I K hKmono
  refine ⟨J, K.complex, f, g, hfg, φ, hφ₁, hrow, hφ₂, ?_, hbound 0 hI hK, ?_⟩
  · -- The right column remains the chosen right injective resolution.
    simpa [hφ₃] using injectiveResolution_map_quasiIso K
  · -- The chosen right injective resolution was built to vanish in negative degrees.
    simpa using hK

-- Proof sketch: choose the left injective resolution strictly in degrees `≥ 0` using
-- Lemma 13.18.3, then invoke the prescribed-left-resolution strictlyGE-zero theorem.
/-- If the outer terms of the original short exact sequence are zero in negative degrees, then the
middle term is also zero in negative degrees, and the injective-resolution diagram can be chosen
so that all three lower resolving complexes are zero in negative degrees as well. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_strictlyGE_zero
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : S.X₁.IsStrictlyGE 0) (hC : S.X₃.IsStrictlyGE 0) :
    ∃ row : ShortComplex (InjectivePlus 𝒜), ∃ hom : S ⟶ row.map injPlusι,
      (row.map injPlusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧
        QuasiIso hom.τ₂ ∧
        QuasiIso hom.τ₃ ∧
        (row.X₁ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
        (row.X₂ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
        (row.X₃ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 := by
  -- Route correction: as in the source proof, first choose the left resolution in degrees `≥ 0`
  -- and only then appeal to the prescribed-left-resolution construction.
  obtain ⟨I, hI, -⟩ :=
    exists_injectiveResolution_strictlyGE_with_termwise_mono
      (𝒜 := 𝒜) (K := S.X₁) 0 hA
  -- Apply the prescribed strictly-nonnegative theorem and repackage its lower row.
  obtain ⟨J, K, f, g, hfg, φ, hφ₁, hrow, hφ₂, hφ₃, hJ, hK⟩ :=
    exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution_strictlyGE_zero
      (S := S) hS I hI hA hC
  refine ⟨ShortComplex.mk f g hfg, φ, hrow, ?_, hφ₂, hφ₃, ?_, hJ, hK⟩
  · -- The left column is the chosen injective resolution, so its comparison map is a quasi-isomorphism.
    simpa [hφ₁] using injectiveResolution_map_quasiIso I
  · -- The chosen left injective resolution was constructed to vanish in all negative degrees.
    simpa using hI

end

end CochainComplex
