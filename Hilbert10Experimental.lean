/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Internal.ForMathlib.BinarySubmask
import Hilbert10.Internal.ForMathlib.PairingEnumeration
import Hilbert10.Internal.ForMathlib.PrimrecInt
import Hilbert10.Internal.ForMathlib.ChooseDigit
import Hilbert10.Internal.ForMathlib.SubmaskChoose
import Hilbert10.Internal.ForMathlib.PrimrecNat
import Hilbert10Experimental.HaltingComplete
import Hilbert10.Internal.ForMathlib.RightRename
import Hilbert10Experimental.PackedRun
import Hilbert10.PolyBridge
import Hilbert10.NormalForm
import Hilbert10.PolynomialCodeComp
import Hilbert10.ExistsCodeRepresents
import Hilbert10.Instantiate
import Hilbert10.Specialization
import Hilbert10.Internal.CleanScratch
import Hilbert10Experimental.CodeComp
import Hilbert10Experimental.CodeMachine
import Hilbert10Experimental.CodePair
import Hilbert10Experimental.CodePrec
import Hilbert10Experimental.CodeRfind
import Hilbert10Experimental.ConfigCoding
import Hilbert10Experimental.ConfigCodingDioph
import Hilbert10.DiophToRE
import Hilbert10.Internal.ExpDioph
import Hilbert10.Internal.ExpDiophChoose
import Hilbert10Experimental.AcceptsDioph
import Hilbert10.Internal.BlockPacking
import Hilbert10.Internal.RegisterMachine
import Hilbert10.Internal.RegisterMachineComp
import Hilbert10Experimental.RunWidth
import Hilbert10.Internal.RegisterMachineMacros
import Hilbert10.Internal.RegisterMachinePair
import Hilbert10.Internal.RegisterMachinePairing
import Hilbert10.Internal.RegisterMachineRealises
import Hilbert10.Internal.RegisterMachineUnpair
import Hilbert10Experimental.Spike.DecLoop
import Hilbert10Experimental.Spike.DecLoopDioph
import Hilbert10Experimental.Spike.Sequences
import Hilbert10Experimental.SelectorMask
import Hilbert10Experimental.Spike.SelectorSlice
import Hilbert10Experimental.Spike.SelectorSliceDioph
import Hilbert10Experimental.Spike.SelectorProgram
import Hilbert10Experimental.Spike.SelectorProgramGlobal
import Hilbert10Experimental.Spike.SelectorProgramDioph
import Hilbert10Experimental.SelectorRegs
import Hilbert10Experimental.SelectorRegsGlobal
import Hilbert10Experimental.SelectorRegsDioph
import Hilbert10Experimental.TupleCoding
import Hilbert10Experimental.DPRM
import Hilbert10Experimental.Endpoints

/-!
# Staging area

Work in progress and material staged for upstreaming to mathlib. This root is **not**
imported by `Hilbert10.lean`; see `scripts/check_sorry_boundary.py` for the policy and
issue #31 for why the boundary exists.
-/
