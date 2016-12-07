FROM ubuntu:14.04.2
MAINTAINER Konstantin Weitz <konstantin.weitz@gmail.com>

# install basic tools
RUN apt-get update && \
    apt-get install -y \
      binutils \
      curl \
      fish \
      git \
      g++ \
      make \
      python \
      python-pip \
      vim \
      wget

# install z3
RUN git clone https://github.com/Z3Prover/z3.git && \
    cd z3; python scripts/mk_make.py && \
           cd build; make; make install

# install coq
RUN apt-get update && \
    apt-get install -y \
      camlp5 \
      libpcre-ocaml-dev \
      libpcre3-dev \
      pkg-config && \
    curl -O https://coq.inria.fr/distrib/8.5pl2/files/coq-8.5pl2.tar.gz && \
    tar -xvf coq-*.tar.gz && \
    cd coq-*; ./configure \
                     -bindir /usr/local/bin \
                     -libdir /usr/local/lib/coq \
                     -configdir /etc/xdg/coq \
                     -datadir /usr/local/share/coq \
                     -mandir /usr/local/share/man \
                     -docdir /usr/local/share/doc/coq \
                     -emacs /usr/local/share/emacs/site-lisp \
                     -coqdocdir /usr/local/share/texmf/tex/latex/misc && \
                   make -j4; make install

# install racket
RUN wget http://mirror.racket-lang.org/installers/6.6/racket-6.6-x86_64-linux.sh -O install.sh && \
    chmod +x install.sh && \
    ./install.sh --in-place --create-links /usr --dest /usr/racket && \
    rm install.sh

# install rosette
RUN apt-get update && \
    apt-get install -y \
      libcairo2-dev \
      libpango1.0-dev \
      libjpeg-dev && \
    git clone https://github.com/emina/rosette.git && \
    cd rosette; git checkout 2.2 && \
                raco pkg install
 
# enable rosette debugging
RUN cd rosette && \
# debug errors during symbolic execution
#   sed -i "s/;(printf/(printf/g" rosette/base/core/effects.rkt && \
# debug formula sent to solver
#   sed -i "s/;(fprintf/(fprintf/g" rosette/solver/smt/smtlib2.rkt && \
    raco pkg remove rosette && \
    raco pkg install

# ENTRYPOINT /cq/src/test.sh

# install
ADD . /cq
RUN make -C /cq
