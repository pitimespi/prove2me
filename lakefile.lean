import Lake
open Lake DSL

package «prove2me» where
  leanOptions := #[⟨`autoImplicit, false⟩]

lean_lib «Definitions» where
lean_lib «Theorems» where
@[default_target]
lean_lib «Solutions» where
