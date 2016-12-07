Running
=======

Checkout the project with:

    git clone --recursive git@github.com:uwplse/VeriCQ

Build with: 

    docker build -t cq .

Verify a couple of instruction variants with:

    docker run cq

Development
===========

Run development environment console:
    
    docker rm -f cq; docker run --name cq --entrypoint /bin/bash -v $(pwd):/cq -ti cq

If you like the `fish` shell (i do) run:

    docker rm -f cq; docker run --name cq --entrypoint /usr/bin/fish -v (pwd):/cq -ti cq

Build project in development environment console:
    
    make -C /cq

Connect emacs to development environment locally:

    emacs /docker:cq:/cq/src/coq/VeriCQ.v

Connect emacs to development environment remotely:

    emacs "/ssh:user@machine|docker:cq:/cq/src/coq/VeriCQ.v"

Make sure your emacs has `ProofGeneral` and `docker-tramp` installed, and
`enable-remote-dir-locals` must be set.

