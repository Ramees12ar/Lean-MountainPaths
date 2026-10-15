# Mountain paths: returns and peaks (my answer)

All four theorems are proved in `Task/MountainPaths.lean`.

- The five definitions and the four theorem statements are exactly as the task gives them.
- There is no `sorry`, `admit`, `native_decide` or new axiom anywhere.
- `#print axioms` on each theorem shows only `propext`, `Classical.choice` and `Quot.sound`.

It uses Lean `leanprover/lean4:v4.33.0-rc1` and Mathlib commit
`9944fe2973b8dc0b86949101ed98232c07cd54a0`, which should be at `/opt/mathlib4`.

To check it, run this inside this folder:

```sh
lake build
```
