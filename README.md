<h1 align="center">Slopes of overconvergent 3-adic modular forms of weight zero</h1>

<p align="center">
  <a href="https://github.com/mt0-svg/calegari-slopes/releases/latest/download/calegari-slopes.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.23608428"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23608428.svg"></a>
  <a href="https://mt0-svg.github.io/calegari-slopes/run.html"><img alt="Lean Proved" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fcalegari-slopes%2Fbadges%2Flean.json"></a>
  <a href="https://mt0-svg.github.io/calegari-slopes/run.html"><img alt="Lean Comparator" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fcalegari-slopes%2Fbadges%2Fcomparator.json"></a>
  <a href="https://mt0-svg.github.io/calegari-slopes/run.html"><img alt="Computation Certificates" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fcalegari-slopes%2Fbadges%2Fcertificates.json"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

We prove a conjecture of Calegari: the slopes of the Atkin operator $`U_3`$ on $`3`$-adic overconvergent cusp forms of tame level $`1`$ and weight $`0`$ are the numbers $`2i+2v_3((2i)!/i!)`$ for $`i\ge1`$, each with multiplicity one. The proof establishes an identity conjectured by Loeffler, which writes the matrix of $`U_3`$ as a lower unitriangular matrix times a diagonal matrix times an upper unitriangular matrix, all with explicit entries. The rows of the upper factor satisfy a recurrence in the column index whose coefficients are affine in the square of the row index, and this pencil structure gives the identity without any summation formula. A contraction then produces one eigenvector for each slope, and an estimate on the matrix shows that there are no other generalized eigenvectors. The matrix of $`U_3`$ comes from Ramanujan's differential equations for Eisenstein series. The proof is formalized in Lean 4.

This is Calegari's conjecture as recorded by Smithline ([CRM Proc. Lecture Notes 36, 2004](https://doi.org/10.1090/crmp/036/21)) and stated by Loeffler in Section 3 of [IMRN 2007](https://doi.org/10.1093/imrn/rnm050) ([arXiv:math/0701168](https://arxiv.org/abs/math/0701168)), together with the factorization of the matrix of $`U_3`$ that Loeffler conjectured in the same paper, with the explicit factors of his 2008 note ([archived copy](https://web.archive.org/web/20231213140513/http://homepages.warwick.ac.uk/~masiao/maths/3adicU.pdf)).

```lean
theorem CalegariSlopes.Final.calegari_conjecture_overconvergent :
    ∃ ev : ℕ+ → K, (∀ i, ‖ev i‖ = (3 : ℝ) ^ (-(Overconvergent.slope i : ℤ))) ∧
      ∀ μ : K, μ ≠ 0 → FiniteDimensional K (genEig μ) ∧
        Module.finrank K (genEig μ) = Nat.card {i : ℕ+ // ev i = μ}

theorem CalegariSlopes.Newton.calegari_conjecture (n : ℕ) :
    Summable (fun S : {S : Finset ℕ+ // S.card = n} => principalMinor S.1) ∧ c n ≠ 0 ∧
      Padic.valuation (c n) = ∑ i ∈ Finset.Icc 1 n, (slope i : ℤ)
```

Here `K` is $`\mathbb{C}_3`$ and `genEig μ` is the generalized eigenspace of $`U_3`$ for $`\mu`$ on the space of overconvergent cusp forms, written through their $`q`$-expansions; the second theorem gives the valuations of the coefficients of the characteristic series of the matrix of $`U_3`$ (Corollary 7.1 of the paper).

## What is checked

- **Lean 4.** The two theorems above have no hypothesis. They are proved with the axioms `propext`, `Classical.choice` and `Quot.sound` alone, with no `sorry` and no `native_decide`, and so is each of the other numbered statements of the paper, Conjecture 1.1 aside. Comparator compares each theorem with the statement file that states it. The two above have theirs in `CalegariSlopes/Challenge.lean` and `CalegariSlopes/ChallengeMatrix.lean`, which import only Mathlib. Lemma 8.1 and Theorem 8.2 are stated in `CalegariSlopes/ChallengeConj5.lean`, which also imports the definitions of Loeffler's factors (`CalegariSlopes/ADB/Defs.lean`), while Corollaries 8.3 and 8.4 are stated in `CalegariSlopes/ChallengeConj5Spectral.lean`, which also imports the definitions of the sequence spaces and of the eigenvectors of Theorem 2.4(a) (`CalegariSlopes/Spectral/Defs.lean`) and of the matrices $`u^{(r)}`$ (`CalegariSlopes/Conj5/SpectralDefs.lean`). nanoda, a second implementation of the Lean kernel, checks the proofs again. Each formalized proof in the paper ends with the name of the declaration that proves it, and [`STATEMENTS.md`](STATEMENTS.md) lists the Lean declarations and scripts of each numbered statement.
- **Data.** The table of the coefficients $`u_{ij}`$, $`0\le i,j\le 38`$, in the proof of Lemma 5.3 comes from a PARI/GP script (`code/utab/gen_utab.gp`) that the proof does not trust, because the Lean kernel checks by evaluation that the table satisfies the recurrence defining $`u`$.
- **Numbers of the paper.** The PARI/GP scripts of `code/gp/` recompute the numbers that the paper prints outside Lean and the two linear systems of Section 4, and compare them with their recorded outputs.

`ci.yml` reuses an earlier build when it finds one in the cache or in the archive of the latest release, and it compiles only what changed since; the Lean kernel checked each declaration when its module was compiled. The workflow fails on any other axiom, scans the sources for `sorry`, `admit` and `native_decide`, runs Comparator on the four statement files (`config*.json`) with nanoda replaying every declaration the theorems depend on, Mathlib included, and reruns the PARI/GP scripts. `release.yml` releases a tagged commit that has a green CI run started by hand. It attaches the PDF that `paper.yml` builds from the tagged sources, the logs of that CI run, and the Lake build that Comparator checked. A run started by hand on `main` writes the three badges.

## Layout

| Path | Content |
| --- | --- |
| `CalegariSlopes/` | the Lean proof (Lean and Mathlib `v4.34.1`): `Final.lean` proves the main theorem and `Newton/Main.lean` Corollary 7.1; `ADB/` is Section 5 and Appendix A, `Bridge/` Sections 2 and 4, `Spectral/` Sections 2 and 6, `Newton/` Sections 3 and 7, `Conj5/` Section 8 |
| `CalegariSlopes/Statement.lean`, `CalegariSlopes/Target.lean` | the definitions of the two statements |
| `CalegariSlopes/Challenge*.lean`, `CalegariSlopes/Solution*.lean`, `config*.json` | the statements with `sorry`, their proofs, and the Comparator configurations |
| `paper/` | the TeX source |
| `code/utab/` | the script that wrote the table of Lemma 5.3, with its recorded output |
| `code/gp/` | the scripts of the numbers of the paper, with their recorded outputs |
| `code/formal-proof/` | the scripts of the CI: build, axioms, badges |

## Check and reuse

Fast check, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -f .lake/build/lib/lean/CalegariSlopes/Challenge*.* .lake/build/ir/CalegariSlopes/Challenge*.*
# then Comparator with each config*.json, as .github/workflows/ci.yml runs it
# (with nanoda, one and a half to five minutes each on four cores)
```

Full check, from source (about four minutes on four cores, Mathlib aside):

```sh
lake exe cache get && lake build
```

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "calegari-slopes"
git = "https://github.com/mt0-svg/calegari-slopes"
rev = "v1.0.0"
```

then `lake update calegari-slopes`, `lake exe cache get` and `lake build`, which downloads the build archive of the release.

The PARI/GP scripts (the recorded outputs come from PARI/GP 2.17.4, the CI job `gp` reruns them under 2.17.2; a few seconds each), from their directories:

```sh
cd code/gp && gp -q numbers.gp < /dev/null | diff - numbers.out && gp -q systems.gp < /dev/null | diff - systems.out
cd code/utab && gp -q gen_utab.gp < /dev/null | diff - gen_utab.out && git diff --exit-code ../../CalegariSlopes/ADB/UTab.lean
```

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and [landrun](https://github.com/zouuup/landrun): the check of the statements in CI.
- [nanoda](https://github.com/ammkrn/nanoda_lib) of Chris Bailey (Apache 2.0), commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`: the second implementation of the Lean kernel, built by the CI, which Comparator runs to check again every declaration the theorems depend on.
- [fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem) (Apache 2.0, Copyright 2026 Anthropic, PBC), commit `6e837e75`: Ramanujan's equations on $`q`$-expansions with integer coefficients, in `CalegariSlopes/Bridge/RamanujanPort.lean`, ported from `P2M/Sol/S_EisensteinSeries_ramanujan_system_qExpansion_int.lean` (namespace and imports changed, the harness commands of `P2M/Util.lean` replaced by plain Lean, the theorem `solution` renamed `ramanujan_system_int` and one lemma renamed, `derivative ℤ` written `derivative (R := ℤ)`, three tactic lines that do nothing removed; no proof changed).
- [PhD](https://github.com/WilliamCoram/PhD) of William Coram (Apache 2.0), commit `659ce26088bc541137cc28cc13ebbf0e3c9fbcc3`: the norm of a sum with a strictly dominant term and the ultrametric bound on determinants, in `CalegariSlopes/Newton/Proofs.lean` (`norm_tsum_eq_of_dominant` and `norm_det_le_pow_of_row_bound`, from `PhD/Main/TateFredholm/06_Slopes.lean`; section variables written as binders, one hypothesis renamed, two lemma names updated to this Mathlib, docstrings replaced by an attribution).
- [PARI/GP](https://pari.math.u-bordeaux.fr/): the table of Lemma 5.3 and the numbers of the paper.

## Citation

```bibtex
@misc{calegari-slopes,
  title     = {Slopes of overconvergent 3-adic modular forms of weight zero},
  author    = {{mt0-svg}},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23608428},
  url       = {https://doi.org/10.5281/zenodo.23608428}
}
```

## Contact

Questions and corrections: [open an issue](https://github.com/mt0-svg/calegari-slopes/issues/new/choose).

## License

Apache 2.0 (`LICENSE`, `NOTICE`).
