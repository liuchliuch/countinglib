import Counting.Algorithm.KarpLubyRequest.Whole.Clients
import Counting.Algorithm.KarpLubyRequest.Whole.Runtime
import Counting.Algorithm.KarpLubyRequest.Whole.Accuracy
import Counting.Algorithm.KarpLubyRequest.Preparation.RuntimeArithmetic
import Counting.Algorithm.KarpLubyRequest.Preparation.Clients
import Counting.Algorithm.KarpLubyRequest.Whole.Composition
import Counting.Algorithm.KarpLubyRequest.Evaluation.Cost
import Counting.Algorithm.KarpLubyRequest.Preparation.RawSemantics
import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Clients
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let imported := env.header.moduleNames
  let mut total := 0
  let mut foreign := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := imported[idx.toNat]!
      if owner.toString.startsWith "Counting.Algorithm.KarpLubyRequest" then
        total := total + 1
        unless name.toString.startsWith "Counting.Algorithm.KarpLubyRequest." ||
            name.toString.startsWith "_private.Counting.Algorithm.KarpLubyRequest." do
          foreign := foreign + 1
          IO.println s!"FOREIGN {owner} {name}"
  IO.println s!"DEVELOPMENT_OWNERSHIP {total} declarations, {foreign} foreign public names"

