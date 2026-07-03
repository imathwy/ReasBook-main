import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_77_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling:
- primary domain: vanishing of morphisms in derived categories and splitting distinguished
  triangles via the canonical binary-biproduct structure;
- sampled owner declarations:
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CochainComplex.derivedCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge`,
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`,
  `CategoryTheory.isSplitEpi_mor₂_of_distinguished_mor₃_eq_zero`;
- best owner abstractions: `HasProjectiveAmplitudeIn` is the chapter-level source-facing amplitude
  predicate, `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang` is the canonical
  split-triangle owner, so the source-facing compatibility data should remain the owner theorem's
  native pair of equations rather than a parallel local wrapper;
- primitive data: the amplitude witness on `L`, the homology-vanishing hypothesis on `K`, the
  distinguished-triangle maps, and the chosen isomorphism to a biproduct;
- derived API: vanishing of `Hom(L, K)`, existence of a compatible biproduct isomorphism, and the
  corresponding uniqueness statement.

Source/core/bridge triage:
- `source-facing`: the three clauses of Lemma `15.77.1`;
- `core/canonical`: `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
- `bridge/view`: the conjunction
  `f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g`, which exposes the source-facing
  compatibility equations without creating a second owner for split triangles.
-/

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

-- Proof sketch: choose a projective representative of `L` concentrated in degrees `[a, b]` from
-- `HasProjectiveAmplitudeIn`, replace `K` by a representative with zero terms in degrees `≥ a`
-- using the cohomology-vanishing hypothesis, and then apply Lemma `13.19.10` to conclude that
-- every map `L ⟶ K` in `D(R)` is zero.
/-- Lemma 15.77.1 (1): if `L` has projective-amplitude in `[a, b]` and the cohomology of `K`
vanishes in all degrees `i ≥ a`, then every morphism `L ⟶ K` in `D(R)` is zero. In particular,
this applies when `L` is perfect of tor-amplitude in `[a, b]`. -/
theorem hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge
    {K L : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a ≤ i → IsZero ((H i).obj K))
    (f : L ⟶ K) :
    f = 0 := sorry

-- Proof sketch: apply part `(1)` to the shifted target `K⟦(1 : ℤ)⟧` to deduce that the
-- connecting morphism `L ⟶ K⟦1⟧` of the distinguished triangle is zero. Lemma `13.4.11`
-- then gives a right inverse to `M ⟶ L`, and hence an isomorphism `M ≅ K ⊞ L` compatible with
-- the first and second maps of the triangle.
/-- Lemma 15.77.1 (2): if `L` has projective-amplitude in `[a, b]`, if the cohomology of `K`
vanishes in all degrees `i ≥ a + 1`, and if `K ⟶ M ⟶ L ⟶ K⟦1⟧` is a distinguished triangle in
`D(R)`, then there is an isomorphism `M ≅ K ⊞ L` compatible with the maps `K ⟶ M` and
`M ⟶ L`. -/
theorem exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ
    {K L M : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a + 1 ≤ i → IsZero ((H i).obj K))
    {f : K ⟶ M} {g : M ⟶ L} {δ : L ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang DMod) :
    ∃ e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g := sorry

-- Proof sketch: part `(2)` gives existence once the stronger cohomology-vanishing hypothesis
-- forces the connecting morphism to vanish. For uniqueness, compare two compatible splittings by
-- a morphism of distinguished triangles and use part `(1)` to show the relevant cross-Hom group
-- `Hom_{D(R)}(L, K)` vanishes, so the comparison morphism is unique.
/-- Lemma 15.77.1 (3): if `L` has projective-amplitude in `[a, b]`, if the cohomology of `K`
vanishes in all degrees `i ≥ a`, and if `K ⟶ M ⟶ L ⟶ K⟦1⟧` is a distinguished triangle in
`D(R)`, then there exists a unique isomorphism `M ≅ K ⊞ L` compatible with the maps
`K ⟶ M` and `M ⟶ L`. -/
theorem existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge
    {K L M : DMod} {a b : ℤ}
    (hL : HasProjectiveAmplitudeIn L a b)
    (hK : ∀ i : ℤ, a ≤ i → IsZero ((H i).obj K))
    {f : K ⟶ M} {g : M ⟶ L} {δ : L ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang DMod) :
    ∃! e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.snd = g := sorry

end

end CategoryTheory

/-! ### Lemma_15_77_2 (from Chap15) -/
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

/- Domain-style sampling:
- primary domain: localization of pseudo-coherent derived objects, truncation triangles in the
  standard `t`-structure, and control of the localized upper truncation by the chapter owners for
  perfectness, tor-amplitude, and compatible biproduct splittings;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeGE`,
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebraHomologyComparison`,
  `t.triangleLEGE_distinguished`,
  `existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge`;
- best owner abstraction: the source-facing localization theorem should state its conclusions
  directly in terms of the owner truncation triangle for
  `K ⊗[R]^L[Localization.Away f]`, together with the canonical owners
  `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, and
  `derivedTensorWithAlgebraHomologyComparison`, not via a second public package or local wrapper
  alias;
- primitive data: the localized object `K ⊗_R^{\mathbf L} R_f`, the canonical truncation triangle
  from `t.triangleLEGE_distinguished`, and its truncation maps;
- derived API: perfectness and tor-amplitude of `τ_{\ge i + 1}`, together with the
  unique compatible splitting of the localized truncation triangle.

Source/core/bridge triage:
- `source-facing`: the existential localization theorem below;
- `core/canonical`: `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, and
  `derivedTensorWithAlgebraHomologyComparison`, with the truncation triangle owned by
  `t.triangleLEGE_distinguished`;
- `bridge/view`: the residue-field specialization of
  `derivedTensorWithAlgebraHomologyComparison`, together with the native compatibility equations
  on the canonical truncation maps; the splitting itself should stay in the owner-level `∃! e`
  form from Lemma `15.77.1`.
-/

section

variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField

-- Proof sketch: apply the Stacks argument after replacing `K` by a bounded-above finite-free
-- representative supplied by pseudo-coherence. The surjectivity hypothesis yields a basis of the
-- middle cohomology after tensoring with `κ(𝔭)` that can be lifted to cycles. Use Algebra,
-- Lemma `10.79.4`, to localize away from some `f ∉ 𝔭` so that the degree-`i` differential splits
-- off a finite projective cokernel, which makes `τ_{\ge i + 1}` perfect with tor-amplitude in
-- `[i + 1, ∞]`. Then apply the canonical truncation triangle together with Lemma `15.77.1` to
-- obtain the unique compatible biproduct decomposition of the localized truncation triangle,
-- while keeping any auxiliary projective-amplitude bound internal to that construction.
/-- Lemma 15.77.2: let `R` be a commutative ring, let `𝔭` be a prime ideal of `R` represented by
`𝔭 : PrimeSpectrum R`, and let `K^•` be a pseudo-coherent object of `D(R)`. Assume the
canonical base-change map
`H^i(K^•) ⊗_R κ(𝔭) ⟶ H^i(K^• \otimes_R^{\mathbf L} κ(𝔭))`
is surjective in degree `i`. Then there exists `f ∈ R` with `f ∉ 𝔭` such that the upper
truncation `τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f)` is perfect and has tor-amplitude in
`[i + 1, ∞]`; moreover, the localized truncation triangle admits a unique splitting compatible
with the standard truncation maps. -/
theorem exists_localizationAway_split_of_residueField_homology_surjective
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hsurj : Epi (derivedTensorWithAlgebraHomologyComparison κ K i)) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
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
                ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away f])) := sorry

end

end

end CategoryTheory

/-! ### Lemma_15_77_3 (from Chap15) -/
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
local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: localization and three-term truncation splittings for pseudo-coherent derived
  objects, combining the chapter owners for perfectness and tor-amplitude with the module-level
  owners for finiteness, freeness, and single-degree embeddings of localized homology;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeGE`,
  `Module.Free`,
  `Module.Finite`,
  `DerivedCategory.singleFunctor`;
- best owner abstraction: this source-facing theorem should expose the localized upper-truncation
  properties, the finiteness/free-ness of the middle homology module, and the existence of the
  three-term decomposition directly, using the canonical owners
  `K ⊗[R]^L[Localization.Away f]`, `LocalizedModule.Away`, and
  `DerivedCategory.singleFunctor`, rather than local wrapper aliases;
- primitive data: the localized object, its lower and upper truncations, the localized middle
  homology module, and the three-term biproduct object;
- derived API: perfectness and tor-amplitude of the upper truncation, finiteness/free-ness of the
  middle term, and existence of the decomposition isomorphism.

Source/core/bridge triage:
- `source-facing`: the existential three-term localization theorem below;
- `core/canonical`: `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, `Module.Free`, and
  `Module.Finite`;
- `bridge/view`: the explicit isomorphism to the three-summand object, which is an existence claim
  and not a second owner abstraction.
-/

variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField

-- Proof sketch: apply Lemma `15.77.2` in degree `i` to split off
-- `τ_{\ge i + 1}(K \otimes_R^{\mathbf L} R_f)`, then apply the same lemma in degree `i - 1` to
-- the lower truncation to split off `H^i(K)_f[-i]`. The second application makes `H^i(K)_f`
-- finite projective; after shrinking once more, replace finite projective by finite free and
-- compose the two splittings.
/-- Lemma 15.77.3: let `R` be a commutative ring, let `𝔭` be a prime ideal of `R` represented by
`𝔭 : PrimeSpectrum R`, and let `K^•` be a pseudo-coherent object of `D(R)`. Assume the
canonical base-change maps
`H^i(K^•) ⊗_R κ(𝔭) ⟶ H^i(K^• \otimes_R^{\mathbf L} κ(𝔭))`
and
`H^(i - 1)(K^•) ⊗_R κ(𝔭) ⟶ H^(i - 1)(K^• \otimes_R^{\mathbf L} κ(𝔭))`
are surjective. Then there exists `f ∈ R` with `f ∉ 𝔭` such that
`τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f)` is perfect with tor-amplitude in `[i + 1, ∞]`,
the localized degree-`i` homology `H^i(K^•)_f` is a finite free `R_f`-module, and
`K^• \otimes_R^{\mathbf L} R_f` decomposes in `D(R_f)` as
`τ_{\le i - 1}(K^• \otimes_R^{\mathbf L} R_f) ⊕ H^i(K^•)_f[-i] ⊕
  τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f)`. -/
theorem exists_localizationAway_threeTermSplit_of_residueField_homology_surjective
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hsurj_i : Epi (derivedTensorWithAlgebraHomologyComparison κ K i))
    (hsurj_im1 : Epi (derivedTensorWithAlgebraHomologyComparison κ K (i - 1))) :
    ∃ f : R,
        ∃ e :
          K ⊗[R]^L[Localization.Away f] ≅
            ((t.truncLE (i - 1)).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                ((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) i).obj
                  (ModuleCat.of (Localization.Away f) (Away f ((H i).obj K))))) ⊞
              (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
        f ∉ 𝔭.asIdeal ∧
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
            HasTorAmplitudeGE
              ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
              (i + 1) ∧
              Module.Free (Localization.Away f) (Away f ((H i).obj K)) ∧
                Module.Finite (Localization.Away f) (Away f ((H i).obj K)) := sorry

end

end CategoryTheory

/-! ### Lemma_15_77_4 (from Chap15) -/
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
                ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away f])) := sorry

end

end CategoryTheory

/-! ### Lemma_15_77_5 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open DerivedCategory.TStructure
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

/- Domain-style sampling:
- primary domain: functorial Ext in the derived category, specifically the condition that the
  fixed-degree Ext functor on modules preserves monomorphisms;
- sampled owner declarations:
  `CategoryTheory.derivedExtToModuleFunctor`,
  `CategoryTheory.Functor.PreservesMonomorphisms`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge`;
- best owner abstraction: `(derivedExtToModuleFunctor K n).PreservesMonomorphisms` is the
  canonical owner-level form of the source hypothesis "Ext^n_R(K,-) sends injective maps to
  injective maps", so a separate local predicate would just duplicate that owner API;
- primitive data: the bounded-above object `K`, the degree `n`, and the canonical Ext functor
  `derivedExtToModuleFunctor K n`;
- derived API: the pointwise mono statements for the functorial maps
  `(derivedExtToModuleFunctor K n).map f`, the projective-amplitude conclusion for the upper
  truncation, and the compatible biproduct decomposition.

Source/core/bridge triage:
- `source-facing`: Lemma `15.77.5`;
- `core/canonical`: `Functor.PreservesMonomorphisms` applied to
  `derivedExtToModuleFunctor K n`;
- `bridge/view`: the explicit pointwise maps `(derivedExtToModuleFunctor K n).map f`, which
  remain available from the owner functor without a second local wrapper.
-/

-- Proof sketch: apply Lemma `15.69.2` to the truncation `τ_{\ge a+1}K` using the hypothesis that
-- `Ext^{-a}_R(K,-)` sends monomorphisms to monomorphisms, which forces the degree `-a` Ext of the
-- upper truncation to vanish against all modules. This gives projective-amplitude in `[a+1,b]`
-- for some `b`; then apply Lemma `15.77.1 (3)` to the canonical truncation triangle from
-- Remark `13.12.4`.
/-- Lemma 15.77.5: if `K` is an object of `D^-(R)` and `Ext^{-a}_R(K, -)` sends injective
`R`-module maps to injective maps, then the upper truncation `\tau_{\ge a + 1}K` has
projective-amplitude in `[a + 1, b]` for some `b`, and there is a unique isomorphism
`K \cong \tau_{\le a}K \oplus \tau_{\ge a + 1}K` compatible with the canonical truncation maps. -/
theorem existsUnique_truncation_biprod_and_projectiveAmplitude_of_ext_preserves_monos
    (K : D⁻((ModuleCat R))) (a : ℤ)
    (hExt : (derivedExtToModuleFunctor K.obj (-a)).PreservesMonomorphisms) :
    ∃ b : ℤ,
      HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b ∧
        ∃! e : K.obj ≅ (t.truncLE a).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
          ((t.truncLEι a).app K.obj) ≫ e.hom = biprod.inl ∧
            e.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj) := sorry

end

end CategoryTheory

/-! ### Lemma_15_77_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open DerivedCategory.TStructure
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: bounded-above derived-module objects, vanishing of a fixed-degree Ext functor
  against modules, and the induced gap splitting of canonical truncations in the standard
  `t`-structure;
- sampled owner declarations:
  `CategoryTheory.existsUnique_truncation_biprod_and_projectiveAmplitude_of_ext_preserves_monos`,
  `CategoryTheory.derivedExtToModuleFunctor`,
  `DerivedCategory.isLE_iff`,
  `CategoryTheory.TStructure.isLE_iff_isIso_truncLEι_app`;
- best owner abstraction: this lemma remains `source-facing`, but its canonical owner inputs are
  the zero-object condition on the degree-`-a` functor `derivedExtToModuleFunctor K.obj (-a)`
  and the canonical truncation API already used in Lemma `15.77.5`;
- primitive data: the bounded-above object `K`, the index `a`, and the owner-level vanishing
  condition `IsZero (derivedExtToModuleFunctor K.obj (-a))`;
- derived API: projective-amplitude of the upper truncation and the unique compatible biproduct
  decomposition with the degree-`a` gap.

Source/core/bridge triage:
- `source-facing`: Lemma `15.77.6`;
- `core/canonical`: `derivedExtToModuleFunctor`, `Functor.PreservesMonomorphisms`,
  `DerivedCategory.IsLE`, and the truncation-transition API of the standard `t`-structure;
- `bridge/view`: the native compatibility equations for the canonical splitting, without
  introducing a second owner.
-/

-- Proof sketch: view the hypothesis as the canonical zero-object condition on
-- `derivedExtToModuleFunctor K.obj (-a)`, hence in particular as the owner-level
-- mono-preservation hypothesis from Lemma `15.77.5`. Apply that lemma to obtain the canonical
-- splitting `K ≅ τ_{\le a}K ⊞ τ_{\ge a + 1}K` and projective-amplitude for the upper truncation.
-- The vanishing in degree `-a` forces `H^a(K) = 0`, so `τ_{\le a}K` identifies with
-- `τ_{\le a - 1}K`, giving the stated gap decomposition.
/-- Lemma 15.77.6: if `K` is an object of `D^-(R)` and `Ext^{-a}_R(K, M)` vanishes for every
`R`-module `M`, then there is a unique isomorphism
`K \cong \tau_{\le a - 1}K \oplus \tau_{\ge a + 1}K` compatible with the canonical truncation
maps, and the upper truncation `\tau_{\ge a + 1}K` has projective-amplitude in `[a + 1, b]` for
some `b`. -/
theorem existsUnique_truncation_gap_biprod_and_projectiveAmplitude_of_ext_vanishing
    (K : D⁻((ModuleCat R))) (a : ℤ)
    (hExt : IsZero (derivedExtToModuleFunctor K.obj (-a))) :
    ∃ b : ℤ,
      HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b ∧
        ∃! e : K.obj ≅ (t.truncLE (a - 1)).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
          ((t.truncLEι (a - 1)).app K.obj) ≫ e.hom = biprod.inl ∧
            e.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj) := sorry

end

end CategoryTheory
