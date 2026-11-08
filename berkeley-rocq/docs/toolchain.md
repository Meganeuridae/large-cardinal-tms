# Toolchain and reproducibility

The verification pins are Rocq 9.3.0, its Stdlib 9.2.0, and OCaml 5.5.2.
Python 3.9+ uses only its standard library. There are no pip dependencies.

With an initialized opam installation, create a local switch and install the
specified packages:

```sh
opam switch create . 5.5.2
eval "$(opam env --switch=. --set-switch)"
opam install rocq-core.9.3.0 rocq-stdlib.9.2.0
python3 verify.py
```

The [official Rocq runtime package](https://opam.ocaml.org/packages/rocq-runtime/rocq-runtime.9.3.0/)
and [Stdlib package](https://opam.ocaml.org/packages/rocq-stdlib/rocq-stdlib.9.2.0/)
publish the source-archive SHA-256 values recorded in `toolchain.lock.json`.
`rocq-core.9.3.0` requires the matching runtime. The local `_opam/` directory
is excluded from Git and the distributable archive. Install tools before
going offline; the verification command itself performs no downloads.

The reference local installation is Homebrew `rocq 9.3.0_1`, compiled with
OCaml 5.5.2 and bundled Stdlib 9.2.0. Package-manager use is optional: any
installation meeting the enforced version and source checks is acceptable.
The opam/Ubuntu CI recipe is included; local macOS verification does not
establish that a hosted CI run has occurred.

The verifier reads `rocq --config` to find `COQLIB/user-contrib/Stdlib` and
checks all 582 `.v` files against `pins/stdlib-sources.json`. If a distribution
installs Stdlib elsewhere, set `BERKELEY_STDLIB` to its `Stdlib` directory;
the same hashes are still enforced, and the directory is explicitly mapped
to the logical namespace during compilation and checking. This check pins
installed source contents; a sound Rocq/Stdlib installation remains part of
the toolchain trust boundary. It is not a bit-reproducible compiler bootstrap.

Every verification deletes and recreates only this package's `.build/`.
Compilation uses no previously compiled project objects. Do not run two
verification commands concurrently in the same package directory. The
reference audit took several minutes; memory and duration depend on the host.
Logs and the final JSON report contain relative project module names, not
machine-specific source paths. `_CoqProject` points to the staged libraries
for inspection after a successful build.

## Optional LaTeX build

The mathematical handout is not an input to the Rocq proof. A prebuilt,
visually checked PDF accompanies its complete LaTeX source. Rebuild it with
Tectonic 0.17.0:

```sh
tectonic --outdir docs docs/axiomatization.tex
```

Tectonic may download its TeX bundle on first use. This documentation build
is separate from the offline proof-verification command; neither LaTeX nor
Tectonic is required to check the theorem. The TeX bundle is not pinned by
the mathematical verification manifest, and PDF byte reproducibility is
not claimed.
