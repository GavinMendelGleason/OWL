PAPER=/home/gavin/Documents/code/agda/OWL/
LIBRARY=/home/gavin/Documents/code/agda/agda-stdlib-0.9/src/

all:
	agda --include-path=$(PAPER) --include-path=$(LIBRARY) --latex OWL.lagda
	cd latex && \
	dlbibtex && \
	rubber -d OWL.tex

# 

html:
	agda --html OWL.lagda
