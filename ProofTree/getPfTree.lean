import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import TrainingData.InfoTree.TacticInvocation.Basic
import TrainingData.Utils.Range
import TrainingData.TreeParser
import Mathlib.Data.String.Defs
import Mathlib.Lean.CoreM
-- import Batteries.Lean.Util.Path
import Batteries.Data.String.Basic
import Mathlib.Tactic.Change
import Cli
import ProofTree.Utils
open Lean Elab IO Meta
open Cli System Std




def trainingData (args : Cli.Parsed) : IO UInt32 := do
    searchPathRef.set compile_time_search_path%

    let module := args.positionalArg! "module" |>.as! ModuleName
    let infos ← getElabDeclInfo (← moduleInfoTrees module)
    let trees ← getInvocationTrees module
    let hash ← generateRandomHash

    let mut idJsons : List (String × Json) := []
    let mut thmAnnotatedTrees_enum : List (String × List (Nat × InfoTree)) := []

    for (idx,t) in trees.enum do
      for tac in t.tactics do
        match getElabDeclOfTacticInvocation infos tac with
        | some elabDeclInfo => do
          let json ← tac.trainingData' elabDeclInfo module hash
          if not <| thmAnnotatedTrees_enum.any (fun (s,_) => s==json.1) then
            thmAnnotatedTrees_enum := (json.1,[(idx,t)]) :: thmAnnotatedTrees_enum
          else
            thmAnnotatedTrees_enum := thmAnnotatedTrees_enum.map (fun (s,ts) => if (s==json.1 && (not (ts.any (fun (i,_) => i==idx)))) then (s,(idx,t)::ts) else (s,ts))
          idJsons := json :: idJsons
        | none => pure ()


    let thmAnnotatedTrees : List (String × List InfoTree) := thmAnnotatedTrees_enum.map (fun (s,ts) => (s,ts.map (fun (_,t) =>t) |>.reverse))
    let parsedTrees : List (String × (IO (List Result))) := thmAnnotatedTrees.map (fun (s,ts) => (s,ts.filterMapM (BetterParser)))

    -- let mut PTs := []
    for (_,results) in parsedTrees.reverse do
      let results ← results
      let steps := results.bind (fun result => result.steps)

      let PT_real : ProofTree := getProofTree steps |>.get!
      IO.println s!"ProofTree: \n{PT_real}"



    return 0


/-- Setting up command line options and help text for `lake exe training_data`. -/
def training_data : Cmd := `[Cli|
  training_data VIA trainingData; ["0.0.1"]
"Export training data from the given file."

  ARGS:
    module : ModuleName; "Lean module to compile and export training data."
]

/-- `lake exe training_data` -/
def main (args : List String) : IO UInt32 :=
  training_data.validate args


#eval main ["ProofTree.Basic"]
