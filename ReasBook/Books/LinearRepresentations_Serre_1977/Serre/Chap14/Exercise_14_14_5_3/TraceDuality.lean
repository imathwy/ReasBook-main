import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_5_3.FiniteFreeAverage

open scoped MonoidAlgebra

universe u v w x

noncomputable section

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Finite G]
variable {E : Type w} [AddCommGroup E] [Module k E] [Module k[G] E] [IsScalarTower k k[G] E]
variable {F : Type x} [AddCommGroup F] [Module k F] [Module k[G] F] [IsScalarTower k k[G] F]

/-- Helper for Exercise 14-14.5-3: a nonzero `k`-linear map `E → F` is detected by the trace
pairing against a suitable map `F → E`. -/
theorem linHom_trace_pairing_left_separates
    [FiniteDimensional k E] [FiniteDimensional k F]
    {u : E →ₗ[k] F} (hu : u ≠ 0) :
    ∃ v : F →ₗ[k] E, LinearMap.trace k E (v.comp u) ≠ 0 := by
  -- Choose a vector where `u` does not vanish and test against the corresponding rank-one map.
  obtain ⟨x, hx⟩ := not_forall.mp fun h ↦ hu <| LinearMap.ext h
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero k (V := F) hx
  refine ⟨ψ.smulRight x, ?_⟩
  calc
    LinearMap.trace k E ((ψ.smulRight x).comp u)
      = LinearMap.trace k E ((ψ.comp u).smulRight x) := by
          rfl
    _ = ψ (u x) := by
          simpa [LinearMap.trace_smulRight]
  exact hψ

/-- Helper for Exercise 14-14.5-3: a nonzero `k`-linear map `F → E` is detected by the trace
pairing against a suitable map `E → F`. -/
theorem linHom_trace_pairing_right_separates
    [FiniteDimensional k E]
    {v : F →ₗ[k] E} (hv : v ≠ 0) :
    ∃ u : E →ₗ[k] F, LinearMap.trace k E (v.comp u) ≠ 0 := by
  -- Use the symmetric rank-one test map on the source side.
  obtain ⟨y, hy⟩ := not_forall.mp fun h ↦ hv <| LinearMap.ext h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k (V := E) hy
  refine ⟨φ.smulRight y, ?_⟩
  calc
    LinearMap.trace k E (v.comp (φ.smulRight y))
      = LinearMap.trace k E (φ.smulRight (v y)) := by
          congr 1
          ext z
          simp [LinearMap.smulRight_apply]
    _ = φ (v y) := by
          simpa [LinearMap.trace_smulRight]
  exact hφ

/-- Helper for Exercise 14-14.5-3: the trace pairing on the two ordinary Hom spaces is the
canonical bilinear form used to identify the dual of `E →ₗ[k] F` with `F →ₗ[k] E`. -/
noncomputable def linHom_trace_pairing
    [FiniteDimensional k E] [FiniteDimensional k F] :
    (E →ₗ[k] F) →ₗ[k] (F →ₗ[k] E) →ₗ[k] k where
  toFun u :=
    { toFun := fun v ↦ LinearMap.trace k E (v.comp u)
      map_add' := by
        -- The trace is linear in the second variable.
        intro v w
        simpa [LinearMap.add_comp] using (LinearMap.trace k E).map_add (v.comp u) (w.comp u)
      map_smul' := by
        -- Scalar factors pull out of the trace.
        intro a v
        simpa [LinearMap.smul_comp] using (LinearMap.trace k E).map_smul a (v.comp u) }
  map_add' := by
    -- The same linearity holds in the first variable.
    intro u v
    ext w
    simpa [LinearMap.comp_add] using (LinearMap.trace k E).map_add (w.comp u) (w.comp v)
  map_smul' := by
    -- Scalar factors also pull out in the first variable.
    intro a u
    ext v
    simpa [LinearMap.comp_smul] using (LinearMap.trace k E).map_smul a (v.comp u)

/-- Helper for Exercise 14-14.5-3: the trace pairing between `E →ₗ[k] F` and `F →ₗ[k] E` is
perfect. -/
theorem linHom_trace_pairing_isPerfPair
    [FiniteDimensional k E] [FiniteDimensional k F] :
    (linHom_trace_pairing (k := k) (E := E) (F := F)).IsPerfPair := by
  -- The previously proved separation lemmas give injectivity in both variables.
  refine LinearMap.IsPerfPair.of_injective' ?_ ?_
  · intro u v huv
    by_contra huv_ne
    obtain ⟨w, hw⟩ :=
      linHom_trace_pairing_left_separates (k := k) (E := E) (F := F)
        (u := u - v) (sub_ne_zero.mpr huv_ne)
    have hzero :
        linHom_trace_pairing (k := k) (E := E) (F := F) (u - v) = 0 := by
      ext z
      have hz := congrArg (fun f => f z) huv
      simpa [linHom_trace_pairing, LinearMap.comp_sub] using sub_eq_zero.mpr hz
    exact hw <| by
      simpa [linHom_trace_pairing] using congrArg (fun f => f w) hzero
  · intro u v huv
    by_contra huv_ne
    obtain ⟨w, hw⟩ :=
      linHom_trace_pairing_right_separates (k := k) (E := E) (F := F)
        (v := u - v) (sub_ne_zero.mpr huv_ne)
    have hzero :
        (linHom_trace_pairing (k := k) (E := E) (F := F)).flip (u - v) = 0 := by
      ext z
      have hz := congrArg (fun f => f z) huv
      simpa [linHom_trace_pairing, LinearMap.sub_comp] using sub_eq_zero.mpr hz
    exact hw <| by
      simpa [linHom_trace_pairing, LinearMap.sub_comp] using congrArg (fun f => f w) hzero

/-- Helper for Exercise 14-14.5-3: the trace pairing evaluates by taking the trace of the
composition `v ∘ u`. -/
@[simp] lemma linHom_trace_pairing_apply
    [FiniteDimensional k E] [FiniteDimensional k F]
    (u : E →ₗ[k] F) (v : F →ₗ[k] E) :
    linHom_trace_pairing (k := k) (E := E) (F := F) u v =
      LinearMap.trace k E (v.comp u) := by
  rfl

/-- Helper for Exercise 14-14.5-3: on the unwrapped `k`-linear Hom spaces, the trace pairing
identifies the dual of `E →ₗ[k] F` with `F →ₗ[k] E`. -/
noncomputable def linHom_dual_linearEquiv_swap
    [FiniteDimensional k E] [FiniteDimensional k F] :
    Module.Dual k (E →ₗ[k] F) ≃ₗ[k] (F →ₗ[k] E) :=
  let p := linHom_trace_pairing (k := k) (E := E) (F := F)
  letI : p.IsPerfPair := linHom_trace_pairing_isPerfPair (k := k) (E := E) (F := F)
  p.flip.toPerfPair.symm

/-- Helper for Exercise 14-14.5-3: forgetting the `RestrictScalars` wrapper gives a canonical
`k`-linear equivalence between the wrapped and unwrapped module. -/
noncomputable def restrictScalars_linearEquiv (M : Type*) [AddCommGroup M] [Module k M]
    [Module k[G] M] [IsScalarTower k k[G] M] :
    RestrictScalars k k[G] M ≃ₗ[k] M where
  toFun := RestrictScalars.addEquiv k k[G] M
  invFun := (RestrictScalars.addEquiv k k[G] M).symm
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    calc
      RestrictScalars.addEquiv k k[G] M (a • x)
          = MonoidAlgebra.single (1 : G) a • RestrictScalars.addEquiv k k[G] M x := by
              simp
      _ = a • RestrictScalars.addEquiv k k[G] M x := by
            calc
              MonoidAlgebra.single (1 : G) a • RestrictScalars.addEquiv k k[G] M x
                  = (a • (1 : k[G])) • RestrictScalars.addEquiv k k[G] M x := by
                      simp [Algebra.smul_def]
              _ = a • ((1 : k[G]) • RestrictScalars.addEquiv k k[G] M x) := by
                    rw [smul_assoc]
              _ = a • RestrictScalars.addEquiv k k[G] M x := by
                    simp

/-- Helper for Exercise 14-14.5-3: forgetting the `RestrictScalars` wrapper does not change the
underlying element. -/
@[simp] lemma restrictScalars_linearEquiv_apply
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (x : RestrictScalars k k[G] M) :
    restrictScalars_linearEquiv (k := k) (G := G) M x = x := by
  rfl

/-- Helper for Exercise 14-14.5-3: rewrapping through `restrictScalars_linearEquiv` is also the
identity on underlying elements. -/
@[simp] lemma restrictScalars_linearEquiv_symm_apply
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    (x : M) :
    (restrictScalars_linearEquiv (k := k) (G := G) M).symm x = x := by
  rfl

/-- Helper for Exercise 14-14.5-3: forgetting the `RestrictScalars` wrappers on both source and
target identifies the owner linear-map space of `Representation.ofModule` with the ordinary
`k`-linear Hom space. -/
noncomputable def restrictScalars_linHom_linearEquiv
    [Module k E] [Module k[G] E] [IsScalarTower k k[G] E]
    [Module k F] [Module k[G] F] [IsScalarTower k k[G] F] :
    (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F) ≃ₗ[k] (E →ₗ[k] F) :=
  (restrictScalars_linearEquiv (k := k) (G := G) E).arrowCongr
    (restrictScalars_linearEquiv (k := k) (G := G) F)

/-- Helper for Exercise 14-14.5-3: forgetting the `RestrictScalars` wrappers on a linear map does
not change its underlying function. -/
@[simp] lemma restrictScalars_linHom_linearEquiv_apply
    [Module k E] [Module k[G] E] [IsScalarTower k k[G] E]
    [Module k F] [Module k[G] F] [IsScalarTower k k[G] F]
    (u : RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F) (x : E) :
    (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F) u) x = u x := by
  rfl

/-- Helper for Exercise 14-14.5-3: the owner-level trace pairing is the ordinary trace pairing
transported across the `RestrictScalars`-forgetful linear equivalences. -/
noncomputable def ofModule_linHom_trace_pairing
    [FiniteDimensional k E] [FiniteDimensional k F] :
    (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F) →ₗ[k]
      (RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] E) →ₗ[k] k :=
  (linHom_trace_pairing (k := k) (E := E) (F := F)).compl₁₂
    (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)).toLinearMap
    (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := F) (F := E)).toLinearMap

/-- Helper for Exercise 14-14.5-3: the wrapped trace pairing is the ordinary trace pairing after
forgetting the `RestrictScalars` wrappers on both Hom spaces. -/
@[simp] theorem ofModule_linHom_trace_pairing_apply
    [FiniteDimensional k E] [FiniteDimensional k F]
    (u : RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F)
    (v : RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] E) :
    ofModule_linHom_trace_pairing (k := k) (G := G) (E := E) (F := F) u v =
      linHom_trace_pairing (k := k) (E := E) (F := F)
        ((restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)) u)
        ((restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := F) (F := E)) v) := by
  rfl

/-- Helper for Exercise 14-14.5-3: the wrapped trace pairing is the trace of the transported
composition on the ordinary `k`-linear Hom spaces. -/
lemma ofModule_linHom_trace_pairing_eq_trace
    [FiniteDimensional k E] [FiniteDimensional k F]
    (u : RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F)
    (v : RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] E) :
    ofModule_linHom_trace_pairing (k := k) (G := G) (E := E) (F := F) u v =
      LinearMap.trace k E
        ((restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := F) (F := E) v).comp
          (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F) u)) := by
  -- This is just the unwrapped trace formula read through the forgetful linear equivalences.
  rw [ofModule_linHom_trace_pairing_apply, linHom_trace_pairing_apply]

/-- Helper for Exercise 14-14.5-3: forgetting the `RestrictScalars` wrappers preserves
composition of `k`-linear maps. -/
lemma restrictScalars_linHom_linearEquiv_comp
    {P : Type*} [AddCommGroup P] [Module k P] [Module k[G] P] [IsScalarTower k k[G] P]
    (u : RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F)
    (v : RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] P) :
    restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := P) (v.comp u) =
      (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := F) (F := P) v).comp
        (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F) u) := by
  rfl

/-- Helper for Exercise 14-14.5-3: rewrapping a `k`-linear map by the forgetful equivalence does
not change its underlying function. -/
@[simp] lemma restrictScalars_linHom_linearEquiv_symm_apply
    (u : E →ₗ[k] F) (x : RestrictScalars k k[G] E) :
    ((restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)).symm u) x = u x := by
  rfl

/-- Helper for Exercise 14-14.5-3: after forgetting `RestrictScalars`, the wrapped internal-Hom
action evaluates pointwise by precomposition and postcomposition with the two `ofModule` actions. -/
lemma restrictScalars_linHom_linearEquiv_linHom_apply_apply
    (g : G)
    (u : RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F)
    (x : RestrictScalars k k[G] E) :
    (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)
      (((Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F)) g) u)) x =
      ((Representation.ofModule (k := k) (G := G) F) g)
        (u (((Representation.ofModule (k := k) (G := G) E) g⁻¹) x)) := by
  -- Expanding the wrapped `linHom` action shows the expected conjugation formula pointwise.
  simp [restrictScalars_linHom_linearEquiv_apply, Representation.linHom_apply]

/-- Helper for Exercise 14-14.5-3: the double inverse appearing in the `ofModule` action reduces
to the original action. -/
lemma ofModule_inv_inv_apply
    (g : G) (x : RestrictScalars k k[G] E) :
    (Representation.ofModule (k := k) (G := G) E) g⁻¹⁻¹ x =
      (Representation.ofModule (k := k) (G := G) E) g x := by
  simp

/-- Helper for Exercise 14-14.5-3: after transporting the two internal-Hom actions to ordinary
`k`-linear maps, the trace pairing identity becomes a single cyclic permutation. -/
lemma ofModule_linHom_trace_transport
    [FiniteDimensional k E] [FiniteDimensional k F]
    (g : G)
    (u : RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F)
    (v : RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] E) :
    LinearMap.trace k E
      ((restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := F) (F := E) v).comp
        (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)
          (((Representation.linHom
            (Representation.ofModule (k := k) (G := G) E)
            (Representation.ofModule (k := k) (G := G) F)) g⁻¹) u))) =
    LinearMap.trace k E
        ((restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := F) (F := E)
            (((Representation.linHom
              (Representation.ofModule (k := k) (G := G) F)
              (Representation.ofModule (k := k) (G := G) E)) g) v)).comp
          (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F) u)) := by
  let u' := restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F) u
  let v' := restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := F) (F := E) v
  let actE (a : G) : E →ₗ[k] E :=
    (restrictScalars_linearEquiv (k := k) (G := G) E).toLinearMap.comp
      (((Representation.ofModule (k := k) (G := G) E) a).comp
        (restrictScalars_linearEquiv (k := k) (G := G) E).symm.toLinearMap)
  let actF (a : G) : F →ₗ[k] F :=
    (restrictScalars_linearEquiv (k := k) (G := G) F).toLinearMap.comp
      (((Representation.ofModule (k := k) (G := G) F) a).comp
        (restrictScalars_linearEquiv (k := k) (G := G) F).symm.toLinearMap)
  have hu :
      restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)
          (((Representation.linHom
            (Representation.ofModule (k := k) (G := G) E)
            (Representation.ofModule (k := k) (G := G) F)) g⁻¹) u) =
        (actF g⁻¹).comp (u'.comp (actE g)) := by
    -- Rewriting the `g⁻¹`-action on the internal Hom gives a conjugation formula with `g`.
    ext x
    simp [u', actE, actF, restrictScalars_linHom_linearEquiv_linHom_apply_apply,
      ofModule_inv_inv_apply, LinearMap.comp_apply]
  have hv :
      restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := F) (F := E)
          (((Representation.linHom
            (Representation.ofModule (k := k) (G := G) F)
            (Representation.ofModule (k := k) (G := G) E)) g) v) =
        (actE g).comp (v'.comp (actF g⁻¹)) := by
    -- The swapped internal-Hom action has the same transported conjugation shape.
    ext x
    simp [v', actE, actF, restrictScalars_linHom_linearEquiv_linHom_apply_apply,
      LinearMap.comp_apply]
  rw [hu, hv]
  -- Now the equality is exactly the cyclic symmetry of trace.
  simpa [u', v', actE, actF, LinearMap.comp_assoc] using
    (LinearMap.trace_comp_cycle' (R := k)
      (f := u')
      (g := v'.comp (actF g⁻¹))
      (h := actE g))

/-- Helper for Exercise 14-14.5-3: the wrapped trace pairing is invariant under the conjugation
actions on the two internal-Hom representations. -/
lemma ofModule_linHom_trace_pairing_action
    [FiniteDimensional k E] [FiniteDimensional k F]
    (g : G)
    (u : RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F)
    (v : RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] E) :
    ofModule_linHom_trace_pairing (k := k) (G := G) (E := E) (F := F)
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F)) g⁻¹ u) v =
    ofModule_linHom_trace_pairing (k := k) (G := G) (E := E) (F := F) u
      ((Representation.linHom
        (Representation.ofModule (k := k) (G := G) F)
        (Representation.ofModule (k := k) (G := G) E)) g v) := by
  -- Unfold the wrapped pairing, rewrite both actions on ordinary Hom spaces, and apply the trace
  -- transport lemma.
  rw [ofModule_linHom_trace_pairing_apply, ofModule_linHom_trace_pairing_apply,
    linHom_trace_pairing_apply, linHom_trace_pairing_apply]
  exact ofModule_linHom_trace_transport (k := k) (G := G) (E := E) (F := F) g u v

/-- Helper for Exercise 14-14.5-3: transport the unwrapped trace-pairing duality across the
`RestrictScalars`-forgetful linear equivalences. -/
noncomputable def ofModule_linHom_dual_linearEquiv_swap
    [FiniteDimensional k E] [FiniteDimensional k F] :
    Module.Dual k (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F) ≃ₗ[k]
      (RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] E) :=
  ((restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)).dualMap.symm.trans
    (linHom_dual_linearEquiv_swap (k := k) (E := E) (F := F))).trans
    (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := F) (F := E)).symm

/-- Helper for Exercise 14-14.5-3: under the transported duality equivalence, the wrapped trace
pairing evaluates a dual functional by ordinary application. -/
lemma ofModule_linHom_dual_linearEquiv_swap_apply
    [FiniteDimensional k E] [FiniteDimensional k F]
    (φ : Module.Dual k (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F))
    (u : RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F) :
    ofModule_linHom_trace_pairing (k := k) (G := G) (E := E) (F := F) u
      (ofModule_linHom_dual_linearEquiv_swap (k := k) (G := G) (E := E) (F := F) φ) =
        φ u := by
  let p := linHom_trace_pairing (k := k) (E := E) (F := F)
  letI : p.IsPerfPair := linHom_trace_pairing_isPerfPair (k := k) (E := E) (F := F)
  -- After forgetting the wrappers, this is exactly the evaluation formula for the unwrapped
  -- perfect trace pairing.
  rw [ofModule_linHom_trace_pairing_apply]
  rw [linHom_trace_pairing_apply]
  convert
    (LinearMap.apply_toPerfPair_flip
      (p := p)
      ((restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)).symm.dualMap φ)
      ((restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)) u)) using 1

/-- Helper for Exercise 14-14.5-3: the transported duality equivalence intertwines the dual
internal-Hom action with the swapped internal-Hom action. -/
lemma ofModule_linHom_dual_linearEquiv_swap_intertwines
    [FiniteDimensional k E] [FiniteDimensional k F] :
    let e := ofModule_linHom_dual_linearEquiv_swap (k := k) (G := G) (E := E) (F := F)
    ∀ g : G, e.toLinearMap.comp ((ofModule_linHom_rep (k := k) (G := G) E F).dual g) =
      ((ofModule_linHom_rep (k := k) (G := G) F E) g).comp e.toLinearMap := by
  intro e g
  let q := linHom_trace_pairing (k := k) (E := E) (F := F)
  letI : q.IsPerfPair := linHom_trace_pairing_isPerfPair (k := k) (E := E) (F := F)
  -- After forgetting the wrappers, injectivity of the ordinary perfect trace pairing reduces the
  -- problem to checking equality of all trace evaluations.
  apply LinearMap.ext
  intro φ
  apply (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := F) (F := E)).injective
  apply (LinearMap.IsPerfPair.bijective_right q).1
  ext u
  let u' := (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)).symm u
  have hpair :
      ofModule_linHom_trace_pairing (k := k) (G := G) (E := E) (F := F) u'
          (e (((ofModule_linHom_rep (k := k) (G := G) E F).dual g) φ)) =
        ofModule_linHom_trace_pairing (k := k) (G := G) (E := E) (F := F) u'
          (((ofModule_linHom_rep (k := k) (G := G) F E) g) (e φ)) := by
    -- Move the group action across the pairing, then both sides reduce to the same evaluation.
    rw [← ofModule_linHom_trace_pairing_action (k := k) (G := G) (E := E) (F := F)
      (g := g) (u := u') (v := e φ)]
    rw [ofModule_linHom_dual_linearEquiv_swap_apply]
    rw [ofModule_linHom_dual_linearEquiv_swap_apply]
    simp [Representation.dual_apply, Module.Dual.transpose_apply, u']
  simpa [q, u', ofModule_linHom_trace_pairing_apply] using hpair

/-- Helper for Exercise 14-14.5-3: the trace pairing yields a representation equivalence between
the dual internal-Hom representation and the swapped internal-Hom representation. -/
theorem dual_linHom_ofModule_equiv_linHom_swap_nonempty
    [FiniteDimensional k E] [FiniteDimensional k F] :
    Nonempty (((ofModule_linHom_rep (k := k) (G := G) E F).dual).Equiv
      (ofModule_linHom_rep (k := k) (G := G) F E)) := by
  -- Route correction: instead of rebuilding a wrapped perfect-pairing instance, transport the
  -- already proved unwrapped duality and package its equivariance as a representation equivalence.
  refine ⟨Representation.Equiv.mk
    (ofModule_linHom_dual_linearEquiv_swap (k := k) (G := G) (E := E) (F := F)) ?_⟩
  simpa using
    ofModule_linHom_dual_linearEquiv_swap_intertwines
      (k := k) (G := G) (E := E) (F := F)

/-- Helper for Exercise 14-14.5-3: the transported trace perfect pairing identifies the dual of
the internal-Hom representation with the swapped internal-Hom representation. -/
noncomputable def dual_linHom_ofModule_equiv_linHom_swap
    [FiniteDimensional k E] [FiniteDimensional k F] :
    ((ofModule_linHom_rep (k := k) (G := G) E F).dual).Equiv
      (ofModule_linHom_rep (k := k) (G := G) F E) :=
  Classical.choice (dual_linHom_ofModule_equiv_linHom_swap_nonempty
    (k := k) (G := G) (E := E) (F := F))

/-- Helper for Exercise 14-14.5-3: the intertwining space for the two canonical `ofModule`
representations has the same `k`-dimension as the corresponding `k[G]`-linear Hom space. -/
theorem ofModule_intertwining_finrank_eq
    [FiniteDimensional k E] [FiniteDimensional k F] :
    Module.finrank k
        (Representation.IntertwiningMap
          (Representation.ofModule (k := k) (G := G) E)
          (Representation.ofModule (k := k) (G := G) F)) =
      Module.finrank k (E →ₗ[k[G]] F) := by
  -- This is the direct finrank consequence of the already constructed intertwining/Hom
  -- equivalence.
  exact
    (ofModule_intertwining_equiv_linearMap (k := k) (G := G) (E := E) (F := F)).finrank_eq

/-- Helper for Exercise 14-14.5-3: the frozen internal-Hom representation is definitionally the
canonical `linHom` representation on the two `ofModule` representations. -/
@[simp] lemma ofModule_linHom_rep_rfl :
    ofModule_linHom_rep (k := k) (G := G) E F =
      Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F) := by
  -- This is just the abbreviation unfolded once, recorded as a rewrite-friendly helper for the
  -- later invariant-space transport step.
  rfl

/-- Helper for Exercise 14-14.5-3: dualizing the frozen internal-Hom representation also unfolds
to the exact dual internal-Hom representation. -/
@[simp] lemma ofModule_linHom_rep_dual_rfl :
    (ofModule_linHom_rep (k := k) (G := G) E F).dual =
      (Representation.linHom
        (Representation.ofModule (k := k) (G := G) E)
        (Representation.ofModule (k := k) (G := G) F)).dual := by
  rfl

end
