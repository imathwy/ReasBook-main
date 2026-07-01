import Lake
open Lake DSL

package «ReasBook» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩,
    ⟨`weak.linter.style.longLine, false⟩,
    ⟨`weak.linter.style.emptyLine, false⟩,
    ⟨`weak.linter.style.cdot, false⟩,
    ⟨`weak.linter.style.maxHeartbeats, false⟩,
    ⟨`weak.linter.unnecessarySimpa, false⟩
  ]

require mathlib from
  FilePath.mk ".." / ".shared-lake" / ".lake" / "packages" / "mathlib"

-- Register doc-gen4's `docs` facet in this main project.
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.30.0"

require subverso from git "https://github.com/leanprover/subverso" @ "v4.30.0"
require MD4Lean from git "https://github.com/acmepjz/md4lean" @ "main"

@[default_target]
lean_lib «ReasBook» where

lean_lib Books where

lean_lib Papers where

-- Books from ALLBOOKS
lean_lib AchimKlenkeLean where
lean_lib BauschkeLean where
lean_lib CombinatorialGroupTheory where
lean_lib FirstOrderMethodsinOptimization where
lean_lib MayConciseRevised where
lean_lib Nesterov where
lean_lib OptimizationResearch where
lean_lib Reaslib where
lean_lib RiemannSurfaces where
lean_lib Serre where
lean_lib SmoothManifoldsLee where
lean_lib cartan where
lean_lib chapter1_reference_format where
lean_lib stacks_project where
lean_lib stacks_proof where

lean_exe "literate-extract" where
  root := `LiterateExtract
  supportInterpreter := true

module_facet literate mod : System.FilePath := do
  let ws ← getWorkspace

  let exeJob ← «literate-extract».fetch
  let modJob ← mod.olean.fetch

  let buildDir := ws.root.buildDir
  let hlFile := mod.filePath (buildDir / "literate") "json"

  exeJob.bindM fun exeFile =>
    modJob.mapM fun _oleanPath => do
      buildFileUnlessUpToDate' (text := true) hlFile <|
        proc {
          cmd := exeFile.toString
          args :=  #[mod.name.toString, hlFile.toString]
          env := ← getAugmentedEnv
        }
      pure hlFile

library_facet literate lib : Array System.FilePath := do
  let mods ← (← lib.modules.fetch).await
  let modJobs ← mods.mapM (·.facet `literate |>.fetch)
  let out ← modJobs.mapM (·.await)
  pure (.pure out)
