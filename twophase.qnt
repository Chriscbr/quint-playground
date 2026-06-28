// quint verify twophase.qnt --main TwoPhase3 --invariant=AllInvariants

module TwoPhase {
  type RmState = Working | Prepared | Committed | Aborted
  type TmState = TMInit | TMCommitted | TMAborted

  type Message =
    | MsgPrepared(str)
    | MsgCommit
    | MsgAbort

  const RM: Set[str]

  var rmState: str -> RmState
  var tmState: TmState
  var tmPrepared: Set[str]
  var msgs: Set[Message]

  action init = all {
    rmState' = RM.mapBy(_ => Working),
    tmState' = TMInit,
    tmPrepared' = Set(),
    msgs' = Set(),
  }

  action TMRcvPrepared(rm) = all {
    tmState == TMInit,
    msgs.contains(MsgPrepared(rm)),
    tmPrepared' = tmPrepared.union(Set(rm)),
    rmState' = rmState, tmState' = tmState, msgs' = msgs,
  }

  action TMCommit = all {
    tmState == TMInit,
    tmPrepared == RM,
    tmState' = TMCommitted,
    msgs' = msgs.union(Set(MsgCommit)),
    rmState' = rmState, tmPrepared' = tmPrepared,
  }

  action TMAbort = all {
    tmState == TMInit,
    tmState' = TMAborted,
    msgs' = msgs.union(Set(MsgAbort)),
    rmState' = rmState, tmPrepared' = tmPrepared,
  }

  action RMPrepare(rm) = all {
    rmState.get(rm) == Working,
    rmState' = rmState.set(rm, Prepared),
    msgs' = msgs.union(Set(MsgPrepared(rm))),
    tmState' = tmState, tmPrepared' = tmPrepared,
  }

  action RMChooseToAbort(rm) = all {
    rmState.get(rm) == Working,
    rmState' = rmState.set(rm, Aborted),
    tmState' = tmState, tmPrepared' = tmPrepared, msgs' = msgs,
  }

  action RMRcvCommitMsg(rm) = all {
    msgs.contains(MsgCommit),
    rmState' = rmState.set(rm, Committed),
    tmState' = tmState, tmPrepared' = tmPrepared, msgs' = msgs,
  }

  action RMRcvAbortMsg(rm) = all {
    msgs.contains(MsgAbort),
    rmState' = rmState.set(rm, Aborted),
    tmState' = tmState, tmPrepared' = tmPrepared, msgs' = msgs,
  }

  action step = {
    nondet rm = RM.oneOf()
    any {
      TMCommit,
      TMAbort,
      TMRcvPrepared(rm),
      RMPrepare(rm),
      RMChooseToAbort(rm),
      RMRcvCommitMsg(rm),
      RMRcvAbortMsg(rm),
    }
  }

  val TPTypeOK: bool = rmState.keys() == RM and tmPrepared.subseteq(RM)

  // copied from tcommit.qnt
  val TCConsistent: bool =
    RM.forall(rm1 => RM.forall(rm2 =>
      not(rmState.get(rm1) == Aborted and rmState.get(rm2) == Committed)))
}

module TwoPhase3 {
  import TwoPhase(RM = Set("r1", "r2", "r3")).*
  val AllInvariants: bool = TPTypeOK and TCConsistent
}
