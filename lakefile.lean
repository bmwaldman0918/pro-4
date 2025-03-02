import Lake
open Lake DSL

package «pro-4» where
  -- add package configuration options here

lean_lib «Pro4» where
  -- add library configuration options here

@[default_target]
lean_exe «pro-4» where
  root := `Main

require "leanprover-community" / "mathlib"
