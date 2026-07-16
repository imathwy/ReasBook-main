import stacks_proof.stacks_project.Chap10.Lemma_10_24_5.Index

open CategoryTheory LinearMap LocalizedModule IsLocalizedModule

universe u v

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

local notation "Away" => LocalizedModule.Away

namespace AwayModuleGlueing

variable {f : Fin n → R} (glue : AwayModuleGlueing f)

/-- Helper for Chap10 Lemma 10 24 5: the localization of the glued compatibility map with its
source and target localization maps fixed explicitly. -/
private noncomputable abbrev localizedCompatibilityMap
    (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) (∀ j : Fin n, glue.localModule j) →ₗ[R]
      Away (f i) (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) :=
  IsLocalizedModule.map (.powers (f i))
    (LocalizedModule.mkLinearMap (.powers (f i)) (∀ j : Fin n, glue.localModule j))
    (LocalizedModule.mkLinearMap (.powers (f i))
      (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)))
    glue.compatibilityMap

/-- Helper for Chap10 Lemma 10 24 5: the standard compatibility map is the difference of the
left and right branch lifts on each `(j,k)` component. -/
private theorem standardCompatibilityMap_apply_lifts
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (y : ∀ t : Fin n, Away (f t) (glue.localModule i)) :
    ((awayLocalizationCompatibilityMap (M := glue.localModule i) f y) j) k =
      glue.standard_target_left_lift i j k (y j) -
        glue.standard_target_right_lift i j k (y k) := by
  -- This is the componentwise definition of the standard Cech compatibility map.
  rfl

/-- Helper for Chap10 Lemma 10 24 5: on canonical generators, the localized glued compatibility
map and the transported standard compatibility map agree on each `(j,k)` component. -/
private theorem localizedCompatibilityMap_generator_component
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : ∀ j : Fin n, glue.localModule j) :
    ((glue.localized_target_comparison i)
        (localizedCompatibilityMap glue i (LocalizedModule.mk x 1)) j) k =
      ((awayLocalizationCompatibilityMap (M := glue.localModule i) f)
        ((glue.localized_middle_comparison i) (LocalizedModule.mk x 1)) j) k := by
  -- First rewrite both localized comparison maps on the canonical generator.
  have hlocalized :
      localizedCompatibilityMap glue i (LocalizedModule.mk x 1) =
        LocalizedModule.mk (glue.compatibilityMap x) 1 :=
    IsLocalizedModule.map_apply
      (S := .powers (f i))
      (f := LocalizedModule.mkLinearMap (.powers (f i)) (∀ j : Fin n, glue.localModule j))
      (g := LocalizedModule.mkLinearMap (.powers (f i))
        (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)))
      (h := glue.compatibilityMap)
      x
  rw [hlocalized]
  have htarget :
      ((glue.localized_target_comparison i) (LocalizedModule.mk (glue.compatibilityMap x) 1) j) k =
        glue.localized_target_component_equiv i j k
          (LocalizedModule.mk ((glue.compatibilityMap x) j k) 1) :=
    glue.localized_target_comparison_apply_mk_one i j k (glue.compatibilityMap x)
  refine htarget.trans ?_
  rw [standardCompatibilityMap_apply_lifts]
  have hmiddle_j :
      (glue.localized_middle_comparison i) (LocalizedModule.mk x 1) j =
        glue.local_piece_overlap_equiv i j (LocalizedModule.mk (x j) 1) := by
    simpa only using glue.localized_middle_comparison_apply_mk_one i j x
  have hmiddle_k :
      (glue.localized_middle_comparison i) (LocalizedModule.mk x 1) k =
        glue.local_piece_overlap_equiv i k (LocalizedModule.mk (x k) 1) := by
    simpa only using glue.localized_middle_comparison_apply_mk_one i k x
  rw [hmiddle_j, hmiddle_k]
  -- Then unfold the glued compatibility component and use the left/right branch normal forms.
  simp only [AwayModuleGlueing.compatibilityMap, LinearMap.pi_apply]
  rw [LinearMap.sub_apply]
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  have hmk_sub :
      (LocalizedModule.mk
          ((LocalizedModule.mk (x j) 1 : Away (f j * f k) (glue.localModule j)) -
            ((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk (x k) 1 : Away (f j * f k) (glue.localModule k))) 1 :
        Away (f i) (Away (f j * f k) (glue.localModule j))) =
        LocalizedModule.mk
            (LocalizedModule.mk (x j) 1 : Away (f j * f k) (glue.localModule j)) 1 -
          LocalizedModule.mk
            (((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk (x k) 1 : Away (f j * f k) (glue.localModule k))) 1 := by
    rw [← LocalizedModule.mkLinearMap_apply (.powers (f i))
      (Away (f j * f k) (glue.localModule j))]
    rw [map_sub]
    simp only [LocalizedModule.mkLinearMap_apply]
  simp only [LocalizedModule.mkLinearMap_apply]
  refine (congrArg (glue.localized_target_component_equiv i j k) hmk_sub).trans ?_
  refine ((glue.localized_target_component_equiv i j k).toLinearMap.map_sub _ _).trans ?_
  have hleft_branch :
      (glue.localized_target_component_equiv i j k).toLinearMap
          (LocalizedModule.mk
            (LocalizedModule.mk (x j) 1 : Away (f j * f k) (glue.localModule j)) 1) =
        glue.standard_target_left_lift i j k
          (glue.local_piece_overlap_equiv i j (LocalizedModule.mk (x j) 1)) := by
    simpa only using glue.localized_target_component_equiv_apply_left_branch_generator i j k (x j)
  have hright_branch :
      (glue.localized_target_component_equiv i j k).toLinearMap
          (LocalizedModule.mk
            (((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk (x k) 1 : Away (f j * f k) (glue.localModule k))) 1) =
        glue.standard_target_right_lift i j k
          (glue.local_piece_overlap_equiv i k (LocalizedModule.mk (x k) 1)) := by
    simpa only using glue.localized_target_component_equiv_apply_right_branch_generator i j k (x k)
  rw [hleft_branch, hright_branch]

/-- Helper for Chap10 Lemma 10 24 5: after localizing away from `f i`, the glued compatibility
map is identified with the standard unit-case Cech differential on `glue.localModule i`. -/
private theorem localized_compatibility_eq_standard
    (glue : AwayModuleGlueing f) (i : Fin n) :
    ((glue.localized_target_comparison i).toLinearMap) ∘ₗ
        localizedCompatibilityMap glue i =
      (awayLocalizationCompatibilityMap (M := glue.localModule i) f) ∘ₗ
        (glue.localized_middle_comparison i).toLinearMap := by
  -- Compare maps out of the localized middle product after precomposing with the canonical
  -- localization map; the target comparison supplies the localized target structure.
  let targetMk :=
    LocalizedModule.mkLinearMap (.powers (f i))
      (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j))
  letI : IsLocalizedModule (.powers (f i))
      ((glue.localized_target_comparison i).toLinearMap.comp targetMk) :=
    IsLocalizedModule.of_linearEquiv (S := .powers (f i)) (f := targetMk)
      (glue.localized_target_comparison i)
  apply IsLocalizedModule.linearMap_ext (S := .powers (f i))
    (f := LocalizedModule.mkLinearMap (.powers (f i)) (∀ j : Fin n, glue.localModule j))
    (f' := ((glue.localized_target_comparison i).toLinearMap.comp targetMk))
  apply LinearMap.ext
  intro x
  ext j k
  -- The remaining goal is the generator-level component calculation isolated above.
  exact localizedCompatibilityMap_generator_component glue i j k x

/-- Helper for Chap10 Lemma 10 24 5: the middle comparison sends localized glued-kernel elements
to the standard unit-case kernel. -/
private theorem localizedMiddleComparison_mem_standardKernel
    (glue : AwayModuleGlueing f) (i : Fin n)
    (x : LinearMap.ker (localizedCompatibilityMap glue i)) :
    glue.localized_middle_comparison i x.1 ∈
      LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f) := by
  -- Transport the zero localized compatibility value through the comparison theorem.
  rw [LinearMap.mem_ker]
  have hmap := LinearMap.congr_fun (localized_compatibility_eq_standard glue i) x.1
  have hleft :
      (((glue.localized_target_comparison i).toLinearMap) ∘ₗ
          localizedCompatibilityMap glue i) x.1 = 0 := by
    rw [LinearMap.comp_apply, LinearMap.mem_ker.mp x.2]
    exact (glue.localized_target_comparison i).toLinearMap.map_zero
  exact hmap.symm.trans hleft

/-- Helper for Chap10 Lemma 10 24 5: the inverse middle comparison sends standard-kernel elements
back to the localized glued kernel. -/
private theorem localizedMiddleComparison_symm_mem_localizedKernel
    (glue : AwayModuleGlueing f) (i : Fin n)
    (y : LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f)) :
    (glue.localized_middle_comparison i).symm y.1 ∈
      LinearMap.ker (localizedCompatibilityMap glue i) := by
  -- Apply the target comparison to the candidate value and use injectivity of the target
  -- comparison equivalence.
  rw [LinearMap.mem_ker]
  let z := (glue.localized_middle_comparison i).symm y.1
  have hmap := LinearMap.congr_fun (localized_compatibility_eq_standard glue i) z
  have hright :
      ((awayLocalizationCompatibilityMap (M := glue.localModule i) f) ∘ₗ
          (glue.localized_middle_comparison i).toLinearMap) z = 0 := by
    have hz : (glue.localized_middle_comparison i).toLinearMap z = y.1 := by
      exact (glue.localized_middle_comparison i).apply_symm_apply y.1
    rw [LinearMap.comp_apply, hz, LinearMap.mem_ker.mp y.2]
  have htarget :
      (((glue.localized_target_comparison i).toLinearMap) ∘ₗ
          localizedCompatibilityMap glue i) z = 0 :=
    hmap.trans hright
  have hzero :
      (glue.localized_target_comparison i) (localizedCompatibilityMap glue i z) = 0 := by
    exact htarget
  apply (glue.localized_target_comparison i).injective
  exact hzero.trans (glue.localized_target_comparison i).toLinearMap.map_zero.symm

/-- Helper for Chap10 Lemma 10 24 5: the middle comparison restricted to the two kernels. -/
private noncomputable def localizedMiddleComparisonKernelMap
    (glue : AwayModuleGlueing f) (i : Fin n) :
    LinearMap.ker (localizedCompatibilityMap glue i) →ₗ[R]
      LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f) :=
  ((glue.localized_middle_comparison i).toLinearMap.comp
    (LinearMap.ker (localizedCompatibilityMap glue i)).subtype).codRestrict
      (LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f))
      (localizedMiddleComparison_mem_standardKernel glue i)

/-- Helper for Chap10 Lemma 10 24 5: the inverse middle comparison restricted to the two kernels. -/
private noncomputable def localizedMiddleComparisonKernelInverseMap
    (glue : AwayModuleGlueing f) (i : Fin n) :
    LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f) →ₗ[R]
      LinearMap.ker (localizedCompatibilityMap glue i) :=
  (((glue.localized_middle_comparison i).symm.toLinearMap).comp
    (LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f)).subtype).codRestrict
      (LinearMap.ker (localizedCompatibilityMap glue i))
      (localizedMiddleComparison_symm_mem_localizedKernel glue i)

/-- Helper for Chap10 Lemma 10 24 5: the restricted middle comparison is right-inverse to its
restricted inverse on the standard kernel. -/
private theorem localizedMiddleComparisonKernelMap_comp_inverse
    (glue : AwayModuleGlueing f) (i : Fin n) :
    (localizedMiddleComparisonKernelMap glue i).comp
        (localizedMiddleComparisonKernelInverseMap glue i) = LinearMap.id := by
  -- Subtype extensionality reduces the inverse law to the inverse law for the ambient linear
  -- equivalence.
  apply LinearMap.ext
  intro y
  exact Subtype.ext <| by
    simpa [localizedMiddleComparisonKernelMap, localizedMiddleComparisonKernelInverseMap] using
      (glue.localized_middle_comparison i).apply_symm_apply y.1

/-- Helper for Chap10 Lemma 10 24 5: the restricted inverse is right-inverse to the restricted
middle comparison on the localized glued kernel. -/
private theorem localizedMiddleComparisonKernelInverse_comp_map
    (glue : AwayModuleGlueing f) (i : Fin n) :
    (localizedMiddleComparisonKernelInverseMap glue i).comp
        (localizedMiddleComparisonKernelMap glue i) = LinearMap.id := by
  -- Again, the subtype carrier equality is exactly the inverse law in the ambient comparison.
  apply LinearMap.ext
  intro x
  exact Subtype.ext <| by
    simpa [localizedMiddleComparisonKernelMap, localizedMiddleComparisonKernelInverseMap] using
      (glue.localized_middle_comparison i).symm_apply_apply x.1

/-- Helper for Chap10 Lemma 10 24 5: localizing the glued kernel away from `f i` identifies it
with the standard unit-case kernel on the distinguished `i`-th local piece. -/
noncomputable def localized_middle_comparison_kernel_equiv
    (glue : AwayModuleGlueing f) (i : Fin n) :
    LinearMap.ker (localizedCompatibilityMap glue i) ≃ₗ[R]
      LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f) :=
  LinearEquiv.ofLinear
    (localizedMiddleComparisonKernelMap glue i)
    (localizedMiddleComparisonKernelInverseMap glue i)
    (localizedMiddleComparisonKernelMap_comp_inverse glue i)
    (localizedMiddleComparisonKernelInverse_comp_map glue i)

/-- Helper for Chap10 Lemma 10 24 5: the canonical map from the glued kernel to the localized
kernel of the compatibility map. -/
noncomputable def localized_kernel_localization_map
    (glue : AwayModuleGlueing f) (i : Fin n) :
    glue.gluedModule →ₗ[R]
      LinearMap.ker (localizedCompatibilityMap glue i) :=
  LinearMap.toKerIsLocalized
    (.powers (f i))
    (LocalizedModule.mkLinearMap (.powers (f i)) (∀ j : Fin n, glue.localModule j))
    (LocalizedModule.mkLinearMap (.powers (f i))
      (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)))
    glue.compatibilityMap

/-- Helper for Chap10 Lemma 10 24 5: the canonical map from the glued kernel to the localized
kernel is itself an `f i`-localization map. -/
theorem localized_kernel_localization_map_isLocalized
    (glue : AwayModuleGlueing f) (i : Fin n) :
    IsLocalizedModule (.powers (f i)) (localized_kernel_localization_map glue i) := by
  -- The map is exactly mathlib's canonical localization map on the kernel of
  -- `glue.compatibilityMap`.
  exact
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization.Away (f i))
      (p := .powers (f i))
      (f := LocalizedModule.mkLinearMap (.powers (f i)) (∀ j : Fin n, glue.localModule j))
      (f' := LocalizedModule.mkLinearMap (.powers (f i))
        (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)))
      glue.compatibilityMap

/-- Helper for Chap10 Lemma 10 24 5: localizing the glued kernel away from `f i` identifies it
with the standard unit-case kernel on the distinguished `i`-th local piece. -/
noncomputable def localized_kernel_comparison
    (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) glue.gluedModule ≃ₗ[R]
      LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f) :=
  letI : IsLocalizedModule (.powers (f i)) (localized_kernel_localization_map glue i) :=
    localized_kernel_localization_map_isLocalized glue i
  (IsLocalizedModule.iso (.powers (f i)) (localized_kernel_localization_map glue i)).trans
    (localized_middle_comparison_kernel_equiv glue i)

/-- Helper for Chap10 Lemma 10 24 5: under the kernel comparison, the distinguished standard
coordinate agrees with the localized projection map. -/
theorem localized_kernel_comparison_apply_mk_one
    (glue : AwayModuleGlueing f) (i : Fin n) (m : glue.gluedModule) :
    ((localized_kernel_comparison glue i) (LocalizedModule.mk m 1)).1 =
      glue.localized_middle_comparison i (LocalizedModule.mk m 1) := by
  -- The localization comparison sends `m/1` to the canonical kernel localization of `m`, and the
  -- restricted middle comparison then forgets to the ambient middle comparison.
  letI : IsLocalizedModule (.powers (f i)) (localized_kernel_localization_map glue i) :=
    localized_kernel_localization_map_isLocalized glue i
  rw [localized_kernel_comparison, LinearEquiv.trans_apply, IsLocalizedModule.iso_mk_one]
  rfl

/-- Helper for Chap10 Lemma 10 24 5: on a glued family, the overlap comparison sends the `j`-th
local coordinate to the distinguished `i`-th coordinate. -/
private theorem local_piece_overlap_equiv_apply_glued_coordinate
    (glue : AwayModuleGlueing f) (i j : Fin n) (m : glue.gluedModule) :
    glue.local_piece_overlap_equiv i j (LocalizedModule.mk (glue.projection j m) 1) =
      (LocalizedModule.mk (glue.projection i m) 1 : Away (f j) (glue.localModule i)) := by
  have hcompat :
      (LocalizedModule.mk (glue.projection i m) 1 : Away (f i * f j) (glue.localModule i)) =
        (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
          (LocalizedModule.mk (glue.projection j m) 1 :
            Away (f i * f j) (glue.localModule j))) := by
    -- The `(i,j)` kernel equation is exactly the overlap-compatibility identity.
    apply sub_eq_zero.mp
    simpa [AwayModuleGlueing.projection, AwayModuleGlueing.compatibilityMap] using
      congrFun (congrFun (LinearMap.mem_ker.mp m.2) i) j
  have hsymm_j :
      (glue.localModuleAwayEquiv j).symm (glue.projection j m) =
        (LocalizedModule.mk (glue.projection j m) 1 : Away (f j) (glue.localModule j)) := by
    -- Collapse the trivial localization on the `j`-piece to identify the inverse image of
    -- `m_j` with its canonical generator.
    apply (glue.localModuleAwayEquiv j).injective
    simpa using (glue.localModuleAwayEquiv j).apply_symm_apply (glue.projection j m)
  -- Normalize the overlap comparison on the canonical localized glued coordinate.
  simp only [AwayModuleGlueing.local_piece_overlap_equiv, LinearEquiv.trans_apply]
  rw [awayLocalizeLinearEquiv_apply_mk_one, hsymm_j, awayMulLinearEquiv_apply_mk_mk,
    awayEqLinearEquiv_apply_mk_one]
  rw [← hcompat]
  rw [awayMulLinearEquiv_symm_apply_mk_one, awayLocalizeLinearEquiv_apply_mk_one,
    localModuleAwayEquiv_apply_mk_one]

/-- Helper for Chap10 Lemma 10 24 5: the localized projection map evaluates on a canonical glued
generator as the ordinary projection. -/
private theorem localizedProjection_apply_mk_one
    (glue : AwayModuleGlueing f) (i : Fin n) (m : glue.gluedModule) :
    glue.localizedProjection i (LocalizedModule.mk m 1) = glue.projection i m := by
  -- The localized projection is the localization of the ordinary projection map.
  simpa [AwayModuleGlueing.localizedProjection] using
    (IsLocalizedModule.map_apply
      (S := .powers (f i))
      (f := LocalizedModule.mkLinearMap (.powers (f i)) glue.gluedModule)
      (g := (LinearMap.id : glue.localModule i →ₗ[R] glue.localModule i))
      (h := glue.projection i)
      m)

/-- Helper for Chap10 Lemma 10 24 5: the distinguished coordinate is preserved by the explicit
kernel comparison between the localized glued kernel and the standard unit-case kernel. -/
theorem localizedProjection_eq_standard_coordinate
    (glue : AwayModuleGlueing f) (i : Fin n) :
    (glue.standardKernelCoordinate i) ∘ₗ (localized_kernel_comparison glue i).toLinearMap =
      (glue.localizedProjection i).restrictScalars R := by
  -- Both maps are maps out of the `f i`-localization of the glued module into the already
  -- localized `i`-th local piece, so it suffices to compare canonical generators.
  letI : IsLocalizedModule (.powers (f i))
      (LinearMap.id : glue.localModule i →ₗ[R] glue.localModule i) :=
    glue.localizedInstance i
  apply IsLocalizedModule.linearMap_ext (S := .powers (f i))
    (f := LocalizedModule.mkLinearMap (.powers (f i)) glue.gluedModule)
    (f' := (LinearMap.id : glue.localModule i →ₗ[R] glue.localModule i))
  apply LinearMap.ext
  intro m
  -- The kernel comparison turns `m/1` into the middle comparison, whose distinguished coordinate
  -- is the canonical localization of the ordinary projection.
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
  have hprojection :
      ((glue.localizedProjection i).restrictScalars R) (LocalizedModule.mk m 1) =
        glue.projection i m :=
    localizedProjection_apply_mk_one glue i m
  rw [hprojection]
  have hkernel :
      (LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f)).subtype
          ((localized_kernel_comparison glue i).toLinearMap (LocalizedModule.mk m 1)) =
        glue.localized_middle_comparison i (LocalizedModule.mk m 1) :=
    localized_kernel_comparison_apply_mk_one glue i m
  rw [hkernel]
  rw [LinearMap.proj_apply]
  rw [glue.localized_middle_comparison_apply_mk_one]
  have hoverlap :
      glue.local_piece_overlap_equiv i i (LocalizedModule.mk (m.1 i) 1) =
        (LocalizedModule.mk (glue.projection i m) 1 : Away (f i) (glue.localModule i)) := by
    simpa [AwayModuleGlueing.projection] using
      local_piece_overlap_equiv_apply_glued_coordinate glue i i m
  rw [hoverlap]
  exact localModuleAwayEquiv_apply_mk_one glue i (glue.projection i m)

end AwayModuleGlueing

-- Proof sketch: localize the defining kernel sequence of `glue.gluedModule` away from `f i`,
-- rewrite the localized compatibility map using the cocycle condition and the canonical
-- `R_(fᵢfⱼ)`-linear overlap isomorphisms, and reduce to the standard exact localization complex from
-- Lemma 10.24.1.
/-- Compatibility form of Lemma 10.24.5 (1): the localized projection map is bijective. -/
theorem localizedProjection_bijective
    {f : Fin n → R} (glue : AwayModuleGlueing f) (i : Fin n) :
    Function.Bijective (AwayModuleGlueing.localizedProjection glue i) := by
  -- The localized projection is the standard unit-case coordinate map transported through the
  -- explicit kernel comparison.
  have hcomp :
      Function.Bijective
        (((glue.standardKernelCoordinate i) ∘ₗ
          (AwayModuleGlueing.localized_kernel_comparison glue i).toLinearMap)) :=
    (glue.standard_kernel_coordinate_bijective i).comp
      (AwayModuleGlueing.localized_kernel_comparison glue i).bijective
  simpa [glue.localizedProjection_eq_standard_coordinate i] using hcomp

namespace AwayModuleGlueing

variable {f : Fin n → R} (glue : AwayModuleGlueing f)

/-- Chap10 Lemma 10 24 5: for a finite module gluing datum on the standard cover `D(f_i)`, the
natural projection from the glued module induces a canonical isomorphism after localizing away from
`f_i`, now stated in the source-facing category of `R_(f_i)`-modules. This is part (1). -/
@[stacks 00EQ]
noncomputable def localizedProjectionLinearEquiv (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) glue.gluedModule ≃ₗ[Localization.Away (f i)] glue.localModule i :=
  LinearEquiv.ofBijective (AwayModuleGlueing.localizedProjection glue i)
    (_root_.localizedProjection_bijective glue i)

/-- The canonical localized projection equivalence is obtained from the localized projection map by
applying `LinearEquiv.ofBijective`. -/
-- Proof sketch: unfold `localizedProjectionLinearEquiv`; the definition is exactly
-- `LinearEquiv.ofBijective` applied to `glue.localizedProjection i` and
-- `localizedProjection_bijective glue i`.
theorem localizedProjectionLinearEquiv_def (glue : AwayModuleGlueing f) (i : Fin n) :
    glue.localizedProjectionLinearEquiv i =
      LinearEquiv.ofBijective (glue.localizedProjection i)
        (_root_.localizedProjection_bijective glue i) := by
  -- This theorem is just the unfolded definition of the canonical linear equivalence.
  rfl

/-- The canonical localized projection equivalence is induced by the localized projection map. -/
@[simp] theorem localizedProjectionLinearEquiv_spec (glue : AwayModuleGlueing f) (i : Fin n) :
    (AwayModuleGlueing.localizedProjectionLinearEquiv glue i).toLinearMap =
      AwayModuleGlueing.localizedProjection glue i :=
  rfl

@[simp] theorem localizedProjectionLinearEquiv_toLinearMap (glue : AwayModuleGlueing f) (i : Fin n) :
    (glue.localizedProjectionLinearEquiv i).toLinearMap = glue.localizedProjection i :=
  rfl

-- Proof sketch: this is the pointwise form of
-- `localizedProjectionLinearEquiv_toLinearMap`, obtained by evaluating the underlying linear map at
-- `x`.
/-- Applying the canonical localized projection equivalence agrees with the localized projection map
itself. -/
@[simp] theorem localizedProjectionLinearEquiv_apply
    (glue : AwayModuleGlueing f) (i : Fin n) (x : Away (f i) glue.gluedModule) :
    glue.localizedProjectionLinearEquiv i x = glue.localizedProjection i x := by
  -- This is the pointwise form of the definitional equality of underlying maps.
  rfl

end AwayModuleGlueing

-- Proof sketch: membership of `m` in the kernel of `glue.compatibilityMap` means that every
-- `(i,j)`-component of the compatibility map vanishes. Unfolding that component gives exactly the
-- equality saying that the `R_(fᵢfⱼ)`-linear overlap isomorphism identifies the two localized
-- components.
/-- Lemma 10.24.5 (2): for an element of the glued module, the overlap isomorphisms identify its
localized `i`-th and `j`-th components on pairwise intersections. -/
@[stacks 00EQ]
theorem overlapIso_projection_mk_one
    {f : Fin n → R} (glue : AwayModuleGlueing f)
    (i j : Fin n) (m : glue.gluedModule) :
    (glue.overlapIso i j).toLinearEquiv
        ((LocalizedModule.mk (glue.projection i m) 1 : Away (f i * f j) (glue.localModule i))) =
      (LocalizedModule.mk (glue.projection j m) 1 : Away (f i * f j) (glue.localModule j)) := by
  have hcompat :
      (LocalizedModule.mk (glue.projection i m) 1 : Away (f i * f j) (glue.localModule i)) =
        (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
          (LocalizedModule.mk (glue.projection j m) 1 :
            Away (f i * f j) (glue.localModule j))) := by
    -- The `(i,j)` kernel component is exactly the overlap-compatibility equation.
    apply sub_eq_zero.mp
    simpa [AwayModuleGlueing.projection, AwayModuleGlueing.compatibilityMap] using
      congrFun (congrFun (LinearMap.mem_ker.mp m.2) i) j
  -- Apply the forward overlap isomorphism to the kernel equation.
  have hforward :=
    congrArg ((glue.overlapIso i j).toLinearEquiv) hcompat
  simpa using hforward

end
