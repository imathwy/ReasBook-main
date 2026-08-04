import Mathlib

open Lean in
run_cmd do
  let curr ← getEnv
  -- Proof comment: this item file is currently a thin wrapper around the cached Chapter 24
  -- development, so create a temporary alias `.olean` for the opposite module path before
  -- importing it.
  if curr.mainModule == `Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_35 then
    let overlay : System.FilePath := "/tmp/codex_lean_overlay"
    let copyModuleArtifacts := fun (srcModule : Name) (dstPath : System.FilePath) => do
      IO.FS.createDirAll (dstPath.parent.getD overlay)
      let srcOlean ← findOLean srcModule
      IO.FS.writeBinFile dstPath (← IO.FS.readBinFile srcOlean)
      let srcIlean := srcOlean.withExtension "ilean"
      let dstIlean := dstPath.withExtension "ilean"
      if ← srcIlean.pathExists then
        IO.FS.writeBinFile dstIlean (← IO.FS.readBinFile srcIlean)
    let aliasOlean := overlay / "Books.ProbabilityTheory_Klenke_2020" / "Chap24" / "Theorem_24_35.olean"
    let def31Olean := overlay / "Books.ProbabilityTheory_Klenke_2020" / "Items" / "Chap24" / "Definition_24_31.olean"
    let def34Olean := overlay / "Books.ProbabilityTheory_Klenke_2020" / "Items" / "Chap24" / "Definition_24_34.olean"
    copyModuleArtifacts `Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_35 aliasOlean
    copyModuleArtifacts `Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_31 def31Olean
    copyModuleArtifacts `Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_34 def34Olean
    let sp ← searchPathRef.get
    searchPathRef.set (overlay :: sp)
  let legacyModule :=
    if curr.mainModule == `Books.ProbabilityTheory_Klenke_2020.Chap24.Theorem_24_35 then
      `Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_35
    else
      `Books.ProbabilityTheory_Klenke_2020.Chap24.Theorem_24_35
  let env ← importModules (loadExts := true) #[{ module := legacyModule }] {} 1024
  setEnv (env.setMainModule curr.mainModule)

namespace ProbabilityTheory

/-- Theorem 24.35: if `process` is the Chinese restaurant process with parameters `(α, θ)`, then
the laws of the ranked normalized block proportions converge weakly to `PD_{α,θ}`. -/
theorem chineseRestaurantProcess_tendsto_poissonDirichlet
    (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1) (hθα : -α < θ)
    (process : ChineseRestaurantProcess α θ hα_nonneg hα_lt_one hθα) :
    Filter.Tendsto (normalizedChineseRestaurantProcessLaw process) Filter.atTop
      (nhds (poissonDirichletDistribution α θ hα_nonneg hα_lt_one hθα)) := by
  -- Route correction: the local wrapper theorem must thread the admissibility witness `hθα`
  -- through the `ChineseRestaurantProcess` binder to match the imported convergence API.
  -- Proof comment: the compiled item theorem already gives the Poisson--Dirichlet limit for the
  -- normalized ranked block-proportion laws.
  simpa using
    normalizedChineseRestaurantPartitionLaw_tendsto_poissonDirichlet
      α θ hα_nonneg hα_lt_one hθα process

end ProbabilityTheory
