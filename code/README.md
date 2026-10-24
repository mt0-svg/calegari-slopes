# Code

| Path | What it does | Paper |
| --- | --- | --- |
| `utab/gen_utab.gp` | writes `CalegariSlopes/ADB/UTab.lean`, the table of the coefficients $`u_{ij}`$ of $`F`$ for $`0\le i,j\le 38`$, one natural number per row; the Lean kernel checks the table against the recurrence that defines $`u`$, so the proof does not trust this script; output `gen_utab.out` | Lemma 5.3 |
| `gp/numbers.gp` | the numbers that the paper prints and no Lean declaration states, from the definitions of Section 1 (the first coefficients of $`j^{-1}`$, $`g`$ and $`u`$, entries of $`A`$, $`B`$, $`D`$, the slopes, the coefficients of Section 8); output `numbers.out` | Sections 1, 2, 4, 5, 7, 8 |
| `gp/systems.gp` | the two linear systems printed in Section 4, as polynomial identities: each line prints the difference of the two sides, which is $`0`$; output `systems.out` | Theorems 4.4 and 4.5 |
| `formal-proof/` | the scripts of the CI: `clean_build.sh` (the build in dependency order), `main_axioms.lean` (the axioms of the main theorems), `facts.lean` (the badges), `to-module.pl` (the module headers) | Section 9 |

Each script runs from its directory with PARI/GP 2.17 in a few seconds: `gp -q numbers.gp < /dev/null | diff - numbers.out`, and the same for the others; the CI job `gp` runs all three and checks that `UTab.lean` is unchanged.
