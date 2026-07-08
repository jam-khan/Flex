import Lake
open Lake DSL

package «Flex» where
  version := v!"0.1.0"

require aesop from git
  "https://github.com/leanprover-community/aesop" @ "3426969888a264d3f69b6f30ab50aa11f28eb38d"

@[default_target]
lean_lib «Flex» where

lean_lib «Demo» where

lean_lib «Tests» where

lean_exe «flex» where
  root := `Main
