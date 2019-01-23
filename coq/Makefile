COQ_FLAGS = -Q . F4

main:		extraction.vo fence4.hs clipPolygon.hs
		ghc -o fence4 fence4.hs

extraction.vo:	extraction.v clipping.vo
		coqc $(COQ_FLAGS) extraction.v # Creates clipPolygon.hs

clipping.vo:	clipping.v viewports.vo
		coqc $(COQ_FLAGS) clipping.v

viewports.vo:	viewports.v geometry.vo
		coqc $(COQ_FLAGS) viewports.v

geometry.vo:	geometry.v misc.vo
		coqc $(COQ_FLAGS) geometry.v

misc.vo:	misc.v
		coqc $(COQ_FLAGS) misc.v

clean:
		rm -rf *.glob *.vo *.o *.hi clipPolygon.hs fence4
