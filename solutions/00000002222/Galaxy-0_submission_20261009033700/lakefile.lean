import Lake
open Lake DSL
package «tlmc2222» where
  leanOptions := #[⟨`warningAsError, true⟩]
@[default_target]
lean_lib Main where
  globs := #[.one `Main, .one `Basic, .one `Cert00, .one `Cert01, .one `Cert02, .one `Cert03, .one `Cert04, .one `Cert05, .one `Cert06, .one `Cert07, .one `Cert08, .one `Cert09, .one `Cert10, .one `Cert11, .one `Cert12, .one `Cert13, .one `Cert14, .one `Cert15, .one `Cert16, .one `Cert17, .one `Cert18, .one `Cert19]
