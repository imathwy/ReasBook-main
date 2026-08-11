import Lean
import Lean.Util.FoldConsts

open Lean Core

/-- A project whose compiled environment should be inspected for theorem-map data. -/
structure ProjectSpec where
  id : String
  rootModule : String
  deriving FromJson

/-- Input accepted by the theorem-map environment extractor. -/
structure ExtractConfig where
  projects : Array ProjectSpec
  deriving FromJson

/-- Declaration metadata exported from a compiled Lean environment. -/
structure RawDeclaration where
  name : String
  moduleName : String
  line : Nat
  kind : String
  docString : String
  dependencies : Array String
  deriving ToJson

/-- Environment data for one ReasBook project. -/
structure RawProject where
  id : String
  rootModule : String
  declarations : Array RawDeclaration
  deriving ToJson

/-- Whether a Lean module belongs to the requested ReasBook project. -/
private def moduleBelongsTo (projectId : String) (moduleName : Name) : Bool :=
  moduleName.toString.splitOn "." |>.contains projectId

/-- A stable display category for a Lean constant. -/
private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The imported module in which a declaration was compiled. -/
private def moduleOf? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.const2ModIdx[declName]?
  env.allImportedModuleNames[moduleIdx.toNat]?

/-- Direct constant dependencies that stay inside one ReasBook project. -/
private def projectDependencyNames (env : Environment) (projectId : String)
    (info : ConstantInfo) : Array String :=
  info.getUsedConstantsAsSet.toArray.filterMap fun name => do
    let moduleName ← moduleOf? env name
    if moduleBelongsTo projectId moduleName then
      some name.toString
    else
      none

/-- Convert one environment constant to exported metadata when it belongs to a project. -/
private def extractDeclaration? (env : Environment) (spec : ProjectSpec)
    (name : Name) (info : ConstantInfo) : CoreM (Option RawDeclaration) := do
  let some moduleName := moduleOf? env name
    | return none
  unless moduleBelongsTo spec.id moduleName do
    return none
  let docString := (← findDocString? env name (includeBuiltin := false)).getD ""
  let ranges? ← findDeclarationRanges? name
  let line := ranges?.map (·.range.pos.line) |>.getD 1
  return some {
    name := name.toString
    moduleName := moduleName.toString
    line
    kind := declarationKind info
    docString
    dependencies := projectDependencyNames env spec.id info
  }

/-- Extract every imported and locally added declaration for one project. -/
private def extractProjectCore (spec : ProjectSpec) : CoreM (Array RawDeclaration) := do
  let env ← getEnv
  let mut declarations := #[]
  for (name, info) in env.constants.map₁ do
    if let some declaration ← extractDeclaration? env spec name info then
      declarations := declarations.push declaration
  for (name, info) in env.constants.map₂ do
    if let some declaration ← extractDeclaration? env spec name info then
      declarations := declarations.push declaration
  return declarations

/-- Import a project's root module and run its metadata extraction. -/
private unsafe def extractProject (spec : ProjectSpec) : IO RawProject := do
  let env ← importModules #[{ module := spec.rootModule.toName }] {}
  let context : Core.Context := {
    fileName := "<theorem-map-extract>"
    fileMap := default
  }
  let state : Core.State := { env }
  let (declarations, _) ← CoreM.toIO (extractProjectCore spec) context state
  return { id := spec.id, rootModule := spec.rootModule, declarations }

/-- Decode an extractor configuration from JSON. -/
private def parseConfig (path : System.FilePath) : IO ExtractConfig := do
  let text ← IO.FS.readFile path
  let json ← match Json.parse text with
    | .ok value => pure value
    | .error message => throw <| IO.userError s!"Invalid extractor JSON: {message}"
  match fromJson? json with
  | .ok config => pure config
  | .error message => throw <| IO.userError s!"Invalid extractor config: {message}"

/-- Export project declaration metadata as JSON for the generic theorem-map generator. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    let [configPath, outputPath] := args
      | throw <| IO.userError "Usage: Extract.lean CONFIG.json OUTPUT.json"
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let config ← parseConfig configPath
    let projects ← config.projects.mapM extractProject
    if let some parent := (outputPath : System.FilePath).parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile outputPath (toJson projects).pretty
    IO.println s!"Exported {projects.size} theorem-map project environments"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"theorem-map extractor failed: {error}"
    return (1 : UInt32)
