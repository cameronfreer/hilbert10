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
import Hilbert10.Internal.PackedRun
import Hilbert10.PolyBridge
import Hilbert10.NormalForm
import Hilbert10.PolynomialCodeComp
import Hilbert10.ExistsCodeRepresents
import Hilbert10.Instantiate
import Hilbert10.Specialization
import Hilbert10.Internal.CleanScratch
import Hilbert10.Internal.CodeMachine
import Hilbert10.Internal.CodePair
import Hilbert10.Internal.CodePrec
import Hilbert10.Internal.CodeRfind
import Hilbert10.Internal.ConfigCoding
import Hilbert10.Internal.ConfigCodingDioph
import Hilbert10.DiophToRE
import Hilbert10.Internal.ExpDioph
import Hilbert10.Internal.ExpDiophChoose
import Hilbert10.Internal.AcceptsDioph
import Hilbert10.Internal.BlockPacking
import Hilbert10.Internal.RegisterMachine
import Hilbert10.Internal.RegisterMachineComp
import Hilbert10.Internal.RunWidth
import Hilbert10.Internal.RegisterMachineMacros
import Hilbert10.Internal.RegisterMachinePair
import Hilbert10.Internal.RegisterMachinePairing
import Hilbert10.Internal.RegisterMachineRealises
import Hilbert10.Internal.RegisterMachineUnpair
import Hilbert10Experimental.Spike.DecLoop
import Hilbert10Experimental.Spike.DecLoopDioph
import Hilbert10Experimental.Spike.Sequences
import Hilbert10.Internal.SelectorMask
import Hilbert10Experimental.Spike.SelectorSlice
import Hilbert10Experimental.Spike.SelectorSliceDioph
import Hilbert10Experimental.Spike.SelectorProgram
import Hilbert10Experimental.Spike.SelectorProgramGlobal
import Hilbert10Experimental.Spike.SelectorProgramDioph
import Hilbert10.Internal.SelectorRegs
import Hilbert10.Internal.SelectorRegsGlobal
import Hilbert10.Internal.SelectorRegsDioph
import Hilbert10.Internal.TupleCoding
import Hilbert10.DPRM
import Hilbert10.Endpoints

/-!
# Staging area

Work in progress and material staged for upstreaming to mathlib. This root is **not**
imported by `Hilbert10.lean`; see `scripts/check_sorry_boundary.py` for the policy and
issue #31 for why the boundary exists.
-/
