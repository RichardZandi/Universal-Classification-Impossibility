import Lake
open Lake DSL

package UCI where
  -- add package configuration options here

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git" @ "v4.20.0"

require godelnumbering from
  git "https://github.com/RichardZandi/godelnumbering" @ "main"

require Kleene2 from
  git "https://github.com/RichardZandi/kleene2" @ "main"


@[default_target]
lean_lib UCI where
  roots := #[`UCI.UCICore]
