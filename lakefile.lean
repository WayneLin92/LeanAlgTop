import Lake
open Lake DSL

package «ss» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Ss» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
