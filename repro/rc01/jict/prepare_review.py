"""Prepare flat anonymous JICT review source; do not submit automatically."""
from pathlib import Path
import shutil, subprocess, sys, zipfile
here=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(here/'scripts'/'manuscript_exhibits.py')],check=True)
paper=here/'paper'
stage=here/'build'/'flat'
stage.mkdir(parents=True,exist_ok=True)
for name in ('main.tex','references.bib'):
    shutil.copyfile(paper/name,stage/name)
for name in ('Fig1.pdf','Fig2.pdf','summary.tex'):
    shutil.copyfile(here/'build'/name,stage/name)
subprocess.run(['latexmk','-bibtex','-e','$bibtex = "bibtex8 %O %B"','-pdf','-interaction=nonstopmode','-halt-on-error','main.tex'],cwd=stage,check=True)
with zipfile.ZipFile(here/'build'/'anonymous_review_source.zip','w',zipfile.ZIP_DEFLATED) as z:
    for name in ('main.tex','references.bib','main.bbl','Fig1.pdf','Fig2.pdf','summary.tex'):
        z.write(stage/name,name)
print(stage/'main.pdf')
