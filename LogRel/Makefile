
main.pdf:
	agda --latex PeterCastCalculus.lagda
	agda --latex PeterPrecision.lagda
	agda --latex PeterLogRel.lagda
	agda --latex PeterFundamental.lagda
	agda --latex PeterGG.lagda
	cd latex/LogRel; /Library/TeX/texbin/pdflatex main; /Library/TeX/texbin/bibtex main
	cd latex/LogRel; /Library/TeX/texbin/pdflatex main; /Library/TeX/texbin/bibtex main
	cd latex/LogRel; /Library/TeX/texbin/pdflatex main; /Library/TeX/texbin/bibtex main
