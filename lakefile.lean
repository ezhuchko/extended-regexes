import Lake
open Lake DSL

package regex {
  -- add package configuration options here
}

@[default_target]
lean_lib Regex

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"