.PHONY: compare clean stoke rocksalt spacesearch

build: src/racket/* lib/SpaceSearch/src/racket/* src/racket/vericq.rkt
	cp lib/SpaceSearch/src/racket/* src/racket/
	raco make src/racket/main.rkt
	chmod +x src/racket/main.rkt 

src/racket/vericq.rkt: src/coq/*.v src/racket/header.rkt spacesearch
	cd src/coq; find . -name '*.v' -exec coq_makefile \
	                   -R . Main \
	                   -R ../../lib/SpaceSearch/src/coq SpaceSearch \
	                   -o Makefile {} +
	make -j4 -C src/coq
	cp src/racket/header.rkt src/racket/vericq.rkt
	tail -n +4 src/coq/vericq.scm >> src/racket/vericq.rkt
	sed -i.bak "s/(define __ (lambda (_) __))/(define __ 'underscore)/g" src/racket/vericq.rkt
	sed -i.bak 's/(error "AXIOM TO BE REALIZED")/void/g' src/racket/vericq.rkt
	rm src/racket/vericq.rkt.bak

spacesearch:
	make -C lib/SpaceSearch

clean:
	make -C src/coq clean || true
	rm -f src/coq/Makefile
	rm -f src/coq/vericq.scm src/racket/vericq.rkt
	rm -rf src/racket/compiled 

cleaner: clean
	make -C lib/SpaceSearch clean
