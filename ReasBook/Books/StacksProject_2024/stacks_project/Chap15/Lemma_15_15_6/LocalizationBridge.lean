import Mathlib

universe u

noncomputable section

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {m n : ℕ}

/-- Helper for Lemma 15.15.6: localizing `R^r` at a prime `p` identifies it with
`(Localization.AtPrime p)^r` coordinatewise. -/
private def localizedFreeSectionsAtPrimeEquivR
    {p : Ideal R} [p.IsPrime] (r : ℕ) :
    LocalizedModule.AtPrime p (Fin r → R) ≃ₗ[R] (Fin r → Localization.AtPrime p) :=
  IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl (Fin r → R))
    (LinearMap.pi fun i : Fin r ↦
      (Algebra.linearMap R (Localization.AtPrime p)).comp (LinearMap.proj i))

/-- Helper for Lemma 15.15.6: on a denominator-`1` generator, the localized free-module
comparison applies the localization map in each coordinate. -/
private theorem localizedFreeSectionsAtPrimeEquivR_mk_apply
    {p : Ideal R} [p.IsPrime] (r : ℕ) (v : Fin r → R) (i : Fin r) :
    localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) r
        ((LocalizedModule.mkLinearMap p.primeCompl (Fin r → R)) v) i =
      algebraMap R (Localization.AtPrime p) (v i) := by
  -- Evaluate the universal localization comparison on the standard free generator.
  simpa [localizedFreeSectionsAtPrimeEquivR] using
    congrFun
      (IsLocalizedModule.linearEquiv_apply p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl (Fin r → R))
        (LinearMap.pi fun j : Fin r ↦
          (Algebra.linearMap R (Localization.AtPrime p)).comp (LinearMap.proj j))
        v)
      i

/-- Helper for Lemma 15.15.6: after identifying prime-localized free modules with coordinate
functions over `Localization.AtPrime p`, the localized map is the obvious matrix map. -/
private theorem localized_coordinate_map_intertwines
    {p : Ideal R} [p.IsPrime]
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) n).toLinearMap.comp
        (LocalizedModule.map p.primeCompl φ) =
      (((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
          (algebraMap R (Localization.AtPrime p))).toLin').restrictScalars R
        .comp (localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) m).toLinearMap := by
  apply IsLocalizedModule.linearMap_ext (S := p.primeCompl)
  intro v
  ext i
  have hmap :=
    LinearMap.congr_fun
      (IsLocalizedModule.map_comp p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl (Fin m → R))
        (LocalizedModule.mkLinearMap p.primeCompl (Fin n → R))
        φ)
      v
  -- Compare both sides on a denominator-`1` generator and read off the `i`-th coordinate.
  calc
    ((localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) n).toLinearMap
        ((LocalizedModule.map p.primeCompl φ)
          ((LocalizedModule.mkLinearMap p.primeCompl (Fin m → R)) v))) i
        =
      ((localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) n).toLinearMap
        ((LocalizedModule.mkLinearMap p.primeCompl (Fin n → R)) (φ v))) i := by
          simpa using congrArg
            (fun z : LocalizedModule.AtPrime p (Fin n → R) ↦
              ((localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) n).toLinearMap z) i)
            hmap
    _ = algebraMap R (Localization.AtPrime p) ((φ v) i) := by
          simpa using localizedFreeSectionsAtPrimeEquivR_mk_apply
            (R := R) (p := p) n (φ v) i
    _ =
      ((((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
            (algebraMap R (Localization.AtPrime p))).toLin')
          (fun j ↦ algebraMap R (Localization.AtPrime p) (v j))) i := by
          simp [Matrix.toLin'_apply, LinearMap.toMatrix, dotProduct]
    _ =
      ((((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
            (algebraMap R (Localization.AtPrime p))).toLin').restrictScalars R
          ((localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) m).toLinearMap
            ((LocalizedModule.mkLinearMap p.primeCompl (Fin m → R)) v))) i := by
          simp [localizedFreeSectionsAtPrimeEquivR_mk_apply]

/-- Helper for Lemma 15.15.6: the coordinatewise identification of the prime localization
conjugates the localized map to the restricted-scalar matrix map. -/
private theorem localized_coordinate_map_restrictScalars_eq_conj
    {p : Ideal R} [p.IsPrime]
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
        (algebraMap R (Localization.AtPrime p))).toLin').restrictScalars R =
      ((localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) n).toLinearMap.comp
          (LocalizedModule.map p.primeCompl φ)).comp
        (localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) m).symm.toLinearMap := by
  -- Route correction: keep only the `R`-linear localization equivalence and express the bridge
  -- as a conjugation for `restrictScalars R`, avoiding `extendScalarsOfIsLocalization`.
  ext x
  simpa [LinearMap.comp_apply] using
    LinearMap.congr_fun
      (localized_coordinate_map_intertwines (R := R) (p := p) φ)
      ((localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) m).symm x)

/-- Helper for Lemma 15.15.6: after localizing an injective free-module map at a prime and then
identifying the localization with coordinatewise sections, the resulting matrix map is still
injective. -/
theorem localized_coordinate_map_injective
    {p : Ideal R} [p.IsPrime]
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hφ : Function.Injective φ) :
    Function.Injective
      ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
        (algebraMap R (Localization.AtPrime p))).toLin' := by
  let eSource := localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) m
  let eTarget := localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) n
  have hkerLocalized :
      LinearMap.ker (LocalizedModule.map p.primeCompl φ) = ⊥ := by
    -- Localization preserves the zero kernel of an injective map.
    calc
      LinearMap.ker (LocalizedModule.map p.primeCompl φ) =
        Submodule.localized'
          (Localization.AtPrime p) p.primeCompl
          (LocalizedModule.mkLinearMap p.primeCompl (Fin m → R))
          (LinearMap.ker φ) := by
            symm
            simpa using
              (LinearMap.localized'_ker_eq_ker_localizedMap
                (S := Localization.AtPrime p)
                (p := p.primeCompl)
                (f := LocalizedModule.mkLinearMap p.primeCompl (Fin m → R))
                (f' := LocalizedModule.mkLinearMap p.primeCompl (Fin n → R))
                (g := φ))
      _ = ⊥ := by
            simpa [LinearMap.ker_eq_bot.mpr hφ]
  have hLocalized : Function.Injective (LocalizedModule.map p.primeCompl φ) :=
    LinearMap.ker_eq_bot.mp hkerLocalized
  have hconj :
      (((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
          (algebraMap R (Localization.AtPrime p))).toLin').restrictScalars R =
        (eTarget.toLinearMap.comp (LocalizedModule.map p.primeCompl φ)).comp
          eSource.symm.toLinearMap := by
    -- Rewrite the localized coordinate map as an `R`-linear conjugate of the localized module map.
    simpa [eSource, eTarget] using
      localized_coordinate_map_restrictScalars_eq_conj (R := R) (p := p) φ
  have hInjectiveRestrict :
      Function.Injective
        ((((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
            (algebraMap R (Localization.AtPrime p))).toLin').restrictScalars R) := by
    rw [hconj]
    exact eTarget.injective.comp (hLocalized.comp eSource.symm.injective)
  -- Transport injectivity across the localization equivalences.
  exact hInjectiveRestrict

end

end LinearMap
