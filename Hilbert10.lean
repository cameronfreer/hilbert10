/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Hilbert10.Basic
-- the wire format
import Hilbert10.PolynomialCode
import Hilbert10.PolynomialCodePrimcodable
import Hilbert10.PolynomialCodeDenote
import Hilbert10.PolynomialCodeInt
import Hilbert10.Internal.CodeAlgebra
import Hilbert10.Internal.CodeAlgebraComp
-- the two reductions between the natural and integer formulations
import Hilbert10.SubUV
import Hilbert10.Internal.SubUVComp
import Hilbert10.FourSquares
import Hilbert10.Internal.FourSquaresComp
import Hilbert10.PolynomialCodeComp
import Hilbert10.Instantiate
import Hilbert10.ExistsCode
import Hilbert10.NatSolvable
import Hilbert10.IntSolvable
-- the normal form and the reduction to `NatSolvable`
import Hilbert10.PolyBridge
import Hilbert10.NormalForm
import Hilbert10.ExistsCodeRepresents
import Hilbert10.Specialization
-- DPRM and the H10 endpoints
import Hilbert10.Computability
import Hilbert10.DiophToRE
import Hilbert10.DPRM
import Hilbert10.DerivedDioph
import Hilbert10.Endpoints
-- worked examples, kept as regressions
import Hilbert10.Examples.DerivedDioph
