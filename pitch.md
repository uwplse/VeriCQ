Verifying Solver Aided Systems (Konstantin Weitz): Many systems build on
automated solvers. These systems reduce problems in an application domain
(ranging from optimal scheduling, to data-race detection) to the domain of a
highly optimized solver like Z3.  However, this reduction is rarely formally
verified in practice, leaving the soundness of the system in question. Can we
develop a system, e.g. a database query optimizer, that is both formally
verified, but that can also be executed very efficiently using an SMT solver?
