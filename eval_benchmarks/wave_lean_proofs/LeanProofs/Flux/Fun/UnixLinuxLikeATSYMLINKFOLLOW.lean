import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

--rust const: libc::AT_SYMLINK_FOLLOW
abbrev unix_linux_like_AT_SYMLINK_FOLLOW : Int := 1024

end F
