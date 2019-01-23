main:
	$(MAKE) -C coq
	$(MAKE) -C haskell
	$(MAKE) -C cpp

clean:
	$(MAKE) -C coq clean
	$(MAKE) -C haskell clean
	$(MAKE) -C cpp clean
