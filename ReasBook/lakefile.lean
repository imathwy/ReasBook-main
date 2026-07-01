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

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

-- Register doc-gen4's `docs` facet in this main project.
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.30.0"

require subverso from git "https://github.com/leanprover/subverso" @ "verso-v4.30.0"
require MD4Lean from git "https://github.com/acmepjz/md4lean" @ "main"

@[default_target]
lean_lib «ReasBook» where

lean_lib Books where

lean_lib Papers where

-- Books from ALLBOOKS (sources live under Books/<LibName>/)
lean_lib AchimKlenkeLean where
  srcDir := "Books"
lean_lib BauschkeLean where
  srcDir := "Books"
lean_lib CombinatorialGroupTheory where
  srcDir := "Books"
lean_lib FirstOrderMethodsinOptimization where
  srcDir := "Books"
lean_lib MayConciseRevised where
  srcDir := "Books"
lean_lib Nesterov where
  srcDir := "Books"
lean_lib OptimizationResearch where
  srcDir := "Books"
lean_lib Reaslib where
  srcDir := "Books"
lean_lib RiemannSurfaces where
  srcDir := "Books"
lean_lib Serre where
  srcDir := "Books"
lean_lib SmoothManifoldsLee where
  srcDir := "Books"
lean_lib cartan where
  srcDir := "Books"
lean_lib chapter1_reference_format where
  srcDir := "Books"
lean_lib stacks_project where
  srcDir := "Books"
lean_lib stacks_proof where
  srcDir := "Books"

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
