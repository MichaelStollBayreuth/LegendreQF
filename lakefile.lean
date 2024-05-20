import Lake
open Lake DSL

package «legendre_QF» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LegendreQF» {
  -- add any library configuration options here
}
