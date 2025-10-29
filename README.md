# Lean 4 Tutorials

While opening the workspace for the first time using VSCode or Cursor, the IDE will guide you through the installation of Lean4. Then, make sure that the following command succeeds.

```sh
lake build --wfail
```

The flag `--wfail` treats warnings (e.g. `sorry`) as errors.
