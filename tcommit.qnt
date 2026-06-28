// quint verify tcommit.qnt --main TCommit3 --invariant=AllInvariants --apalache-config=no-deadlocks.json

module TCommit {
  type RmState = Working | Prepared | Committed | Aborted

  const RM: Set[str]
  var rmState: str -> RmState

  action init = {
    rmState' = RM.mapBy(_ => Working)
  }

  val canCommit: bool =
    RM.forall(rm => rmState.get(rm).in(Set(Prepared, Committed)))

  val notCommitted: bool =
    RM.forall(rm => rmState.get(rm) != Committed)

  action prepare(rm) = all {
    rmState.get(rm) == Working,
    rmState' = rmState.set(rm, Prepared),
  }

  action decide(rm) = any {
    all {
      rmState.get(rm) == Prepared,
      canCommit,
      rmState' = rmState.set(rm, Committed),
    },
    all {
      rmState.get(rm).in(Set(Working, Prepared)),
      notCommitted,
      rmState' = rmState.set(rm, Aborted),
    },
  }

  action step = {
    nondet rm = RM.oneOf()
    any { prepare(rm), decide(rm) }
  }

  val TCTypeOK: bool = rmState.keys() == RM

  val TCConsistent: bool =
    RM.forall(rm1 => RM.forall(rm2 =>
      not(rmState.get(rm1) == Aborted and rmState.get(rm2) == Committed)))
}

module TCommit3 {
  import TCommit(RM = Set("r1", "r2", "r3")).*
  val AllInvariants: bool = TCTypeOK and TCConsistent   // the INVARIANTS line, bundled into one bool
}
