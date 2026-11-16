# RC01 R1 reproducibility baseline
Frozen theory: research/rc01/resolution_r1/STAGE_08_CANONICAL_THEORY_FREEZE_2026-11-17.md, blob e8030a6d046b3b1946afb9644b077ea63c3cfb94, commit a204d6db5367d3a655b3997a9a034fff4e72cc09.
Run from this directory on Python 3.13.5 with latexmk, pdflatex and bibtex8, amsmath, graphicx, natbib installed:
    python -m venv .venv
    . .venv/bin/activate
    python -m pip install -r requirements.txt
    make clean && make
Output: build/main.pdf (scaffold only), build/window.pdf, build/summary.tex, build/welfare.csv, three exact logs. make verify needs only Python. Original archived scripts and logs are extracted into build/originals after hash verification. The six primary files in originals.zip retain their historical blobs; archive blob 1ca8ac66f4b33c6eeb3a75558c4ac67cf0bfa71e. Existing baseline scripts and logs remain under ../../research/rc01/verification; run them separately (Python/SymPy) and compare archived stdout.
Formal code: formal/ is a byte-identical tree copied from formal/rc01 at c8bff78c20af069e421bf20166173b3a02bb1b03. No rerun or merge of Draft PR #1. Instructions: cd formal; lake exe cache get; lake build --wfail; lake env lean RC01Proof.lean > lean-audit.log; python3 audit.py. Inspect scope certificate in research/rc01/resolution_r1/FORMAL_VERIFICATION_CERTIFICATE_2026-11-17.md. This certifies selected mathematical steps, not whole model.
The bibliography contains a single pipeline test entry, not full literature coverage. Stage10 must build the cited bibliography based on source checks. Figures and numerical tables generated rather than edited manually. Full proof and scope register in freeze file; author contribution, provenance and counterexamples in research/rc01; do not delete/overwrite archives. No new GitHub Actions run; local-equivalent build performed. environment-tested.txt records observed environment, not a fully hashed lockfile across OS.
