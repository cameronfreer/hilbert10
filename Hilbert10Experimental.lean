/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10
-- route evidence: the spikes the register-machine construction was validated on
import Hilbert10Experimental.Spike.DecLoop
import Hilbert10Experimental.Spike.DecLoopDioph
import Hilbert10Experimental.Spike.Sequences
import Hilbert10Experimental.Spike.SelectorSlice
import Hilbert10Experimental.Spike.SelectorSliceDioph
import Hilbert10Experimental.Spike.SelectorProgram
import Hilbert10Experimental.Spike.SelectorProgramGlobal
import Hilbert10Experimental.Spike.SelectorProgramDioph
-- staged for elsewhere
import Hilbert10Experimental.HaltingComplete

/-!
# Staging area

Work in progress and route evidence. This root is **not** imported by `Hilbert10.lean`; see
`scripts/check_sorry_boundary.py` for the policy and issue #31 for why the boundary exists.

It imports `Hilbert10` and then only what is *not* in the spine. Before v1's promotion the list
was the other way round — every module named individually — which stopped saying anything once
most of them had been promoted. What is listed here is now exactly the staged material:

* the one-register and fixed-slice spikes the register-machine route was validated on, kept as
  regression evidence for a construction whose general form (`SelectorRegs*`) is now public;
* `HaltingComplete`, which is outside the endpoint closure (#24).
-/
