module

-- Слой Setup: 17 модулей.
public import Involution.Setup.ACDomain
public import Involution.Setup.ClassicalModes
public import Involution.Setup.ComplexAC
public import Involution.Setup.DirichletDomain
public import Involution.Setup.DirichletEnergy
public import Involution.Setup.IntervalOperator
public import Involution.Setup.IntervalRegularity
public import Involution.Setup.IntervalSobolev
public import Involution.Setup.IntervalTrace
public import Involution.Setup.L2Parity
public import Involution.Setup.L2Reflection
public import Involution.Setup.PhaseSelection
public import Involution.Setup.Reflection
public import Involution.Setup.SmoothPrimitive
public import Involution.Setup.WeakConstant
public import Involution.Setup.WeakDerivative
public import Involution.Setup.WeakPrimitive

-- Слой Folding: 10 модулей.
public import Involution.Folding.ComplexReduction
public import Involution.Folding.FoldedOperator
public import Involution.Folding.FoldedSobolev
public import Involution.Folding.FoldingIntegral
public import Involution.Folding.IntervalGluing
public import Involution.Folding.IntervalReflection
public import Involution.Folding.L2Folding
public import Involution.Folding.Reduction
public import Involution.Folding.Symmetrization
public import Involution.Folding.VariableOperator

-- Слой Model: 37 модулей.
public import Involution.Model.ACSpectral
public import Involution.Model.BlockInvariant
public import Involution.Model.BlockMultiplier
public import Involution.Model.BlockPerturbation
public import Involution.Model.BracketBounds
public import Involution.Model.CoefficientInverse
public import Involution.Model.CoefficientSqrt
public import Involution.Model.CompactEigenbasis
public import Involution.Model.CompactInverse
public import Involution.Model.DirichletGreen
public import Involution.Model.EigenvalueCounting
public import Involution.Model.EvenCoefficient
public import Involution.Model.EvenEigenbasis
public import Involution.Model.EvenNoJordan
public import Involution.Model.FiniteSynthesis
public import Involution.Model.FlattenedBounds
public import Involution.Model.GaugeOperators
public import Involution.Model.GaugeSimilarity
public import Involution.Model.ModelBasis
public import Involution.Model.ModelEigenbasis
public import Involution.Model.MultiplicationEquiv
public import Involution.Model.ParityBasis
public import Involution.Model.ParityDomain
public import Involution.Model.ParityGreen
public import Involution.Model.ParityMultiplier
public import Involution.Model.PositiveWeight
public import Involution.Model.RieszBasis
public import Involution.Model.ScalarDomain
public import Involution.Model.SchurMultiplier
public import Involution.Model.SobolevModes
public import Involution.Model.SobolevMultiplier
public import Involution.Model.SparseCuts
public import Involution.Model.SpectralGreen
public import Involution.Model.SubordinatePerturbation
public import Involution.Model.WeightedEigenbasis
public import Involution.Model.WeightedGreen
public import Involution.Model.WeightedSymmetry

-- Слой Estimates: 35 модулей.
public import Involution.Estimates.BracketCorollaries
public import Involution.Estimates.EigenvalueSector
public import Involution.Estimates.GaugeResolvent
public import Involution.Estimates.GeneralBrackets
public import Involution.Estimates.HalfSlope
public import Involution.Estimates.HalfSlopeProfile
public import Involution.Estimates.MarkusMatsaev
public import Involution.Estimates.MMCompact
public import Involution.Estimates.MMContour
public import Involution.Estimates.MMCore
public import Involution.Estimates.MMCuts
public import Involution.Estimates.MMEstimates
public import Involution.Estimates.MMGoodCut
public import Involution.Estimates.MMMinModulus
public import Involution.Estimates.MMOperators
public import Involution.Estimates.MMPointwise
public import Involution.Estimates.MMRiesz
public import Involution.Estimates.MMRieszBasis
public import Involution.Estimates.MMScalar
public import Involution.Estimates.MMSideInt
public import Involution.Estimates.MMTotal
public import Involution.Estimates.MMWindow
public import Involution.Estimates.MMWindowCut
public import Involution.Estimates.MMWoodbury
public import Involution.Estimates.NearlyEvenBrackets
public import Involution.Estimates.OddCoefficient
public import Involution.Estimates.OneSidedExample
public import Involution.Estimates.ProjectionBrackets
public import Involution.Estimates.RampNoBasis
public import Involution.Estimates.RampSpectrum
public import Involution.Estimates.ResolventAux
public import Involution.Estimates.ResolventBound
public import Involution.Estimates.RieszEigenCount
public import Involution.Estimates.SignDefiniteBrackets
public import Involution.Estimates.SobolevClosure

-- Слой Theorems: 2 модулей.
public import Involution.Theorems.BasisConditions
public import Involution.Theorems.MainTheorems

-- Слой Examples: 2 модулей.
public import Involution.Examples.Examples
public import Involution.Examples.MatrixInverse

/-!
  Оглавление библиотеки: все модули собраны по слоям теории
  (Setup → Folding → Model → Estimates → Theorems → Examples).
  Импорты стоят первыми: доккомментарий до них Lean не принимает.
-/
