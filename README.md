# Large-cardinal Turing machines

Verified Turing machines for consistency statements involving large cardinals.

| Project | Machine | Theory and verification |
| --- | --- | --- |
| [Berkeley1399](berkeley-rocq/) | 1,399 working states, two symbols, blank tape | Rocq verification of halting iff finite inconsistency of the specified first-order presentation of ZF plus a Berkeley cardinal. |

The [Berkeley package README](berkeley-rocq/README.md) gives the exact theorem,
machine hashes, toolchain pins, and proof scope. Its
[LaTeX axiomatization](berkeley-rocq/docs/axiomatization.tex) and
[one-page PDF](berkeley-rocq/docs/axiomatization.pdf) spell out the theory.

With the pinned toolchain installed, verify from the repository root:

```sh
python3 berkeley-rocq/verify.py
```

[GitHub Actions verification](https://github.com/Meganeuridae/large-cardinal-tms/actions/workflows/berkeley-rocq.yml)
performs the clean Rocq build, assumption audits, independent kernel check,
verifier negative controls, and machine/certificate reproduction.

See [third-party attribution and license information](berkeley-rocq/THIRD_PARTY.md).
