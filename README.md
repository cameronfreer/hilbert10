# hilbert10

A Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4) library on
Hilbert's tenth problem.

The repository is currently a scaffold: the build, the root import spine, and CI are
wired up, but the mathematical content has not landed yet.

## Building

The project pins Lean `v4.32.0` and the mathlib revision at that tag
(`81a5d257c8e410db227a6665ed08f64fea08e997`), so it builds against exactly one mathlib,
shared with the other projects in this workspace.

```bash
lake exe cache get   # mathlib build cache
lake build
```

## Layout

```
Hilbert10.lean       root import spine
Hilbert10/Basic.lean placeholder module
```

## License

Apache-2.0. See [LICENSE](LICENSE).
