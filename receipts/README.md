# Reproduction scripts for *Likely and Allowed*

Exact integer and rational arithmetic only; no floating point. The one script that samples instances (`r7_visited_futures.py`) uses a fixed seed. Each script writes a JSON receipt whose SHA-256 digest is computed over the receipt body before the digest field is added, so a rerun that reproduces the digest reproduces every number.

Run everything with `python3 run_release.py`. It writes `MANIFEST.json` with every digest and pass flag. `r1`–`r7` check the results named in their headers; `base/` holds Receipts A–I, small exhaustive checks of individual results; `la_core.py` holds the shared exact-arithmetic utilities. `r8_extensions.py` (with its helper `r8_helper.py`) checks the extension results of Sections 4, 5, 6 and 9 and is run separately: `python3 r8_extensions.py`. Appendix A of the paper says which script checks which result.
