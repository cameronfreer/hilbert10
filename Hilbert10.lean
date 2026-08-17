/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Basic
import Hilbert10.PolynomialCode
import Hilbert10.PolynomialCodePrimcodable
import Hilbert10.PolynomialCodeDenote
import Hilbert10.ExistsCode
import Hilbert10.NatSolvable
-- promoted in #52's tranche 2; the internal dependencies under `Hilbert10.Internal.*` are
-- reached transitively, which is what puts them inside the gates' root closure
import Hilbert10.PolyBridge
import Hilbert10.PolynomialCodeComp
import Hilbert10.NormalForm
import Hilbert10.ExistsCodeRepresents
import Hilbert10.Instantiate
import Hilbert10.Specialization
import Hilbert10.DiophToRE
-- tranche 3a: the exponential-Diophantine layer and block packing
import Hilbert10.Internal.ExpDiophChoose
import Hilbert10.Internal.BlockPacking
-- tranche 3b: the register machine, its realisation contracts and macros
import Hilbert10.Internal.RegisterMachinePair
-- tranche 3c: the partial-recursive-code compiler and the packed-run interface
import Hilbert10.Internal.CodeMachine
import Hilbert10.Internal.AcceptsDioph
