import Lake
open Lake DSL
package rc01 where
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.32.1"
@[default_target] lean_lib RC01Proof
