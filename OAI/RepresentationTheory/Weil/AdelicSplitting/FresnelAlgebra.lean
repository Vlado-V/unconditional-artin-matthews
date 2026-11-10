module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.Generators
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! # Fresnel Algebra -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelAlgebra.Construction

noncomputable section

/-! The two Fourier-quadratic words have the same symplectic matrix. -/

def unitSymmetricMatrix (k : Type) [Field k] (N : ℕ) : Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N :=
  ⟨1, Matrix.isSymm_one⟩

def negativeUnitSymmetricMatrix (k : Type) [Field k] (N : ℕ) : Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N :=
  ⟨-1, Matrix.isSymm_one.neg⟩

theorem fresnel_symplectic_relation (k : Type) [Field k] (N : ℕ) :
    Local.Generators.Construction.weylSymplectic k N * Local.Generators.Construction.quadraticSymplectic (unitSymmetricMatrix k N) * Local.Generators.Construction.weylSymplectic k N =
      Local.Generators.Construction.quadraticSymplectic (negativeUnitSymmetricMatrix k N) * Local.Generators.Construction.weylSymplectic k N *
        Local.Generators.Construction.quadraticSymplectic (negativeUnitSymmetricMatrix k N) := by
  apply Subtype.ext
  change (Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 1 0 1 1) * Matrix.fromBlocks 0 1 (-1) 0 =
    (Matrix.fromBlocks 1 0 (-1) 1 * Matrix.fromBlocks 0 1 (-1) 0) * Matrix.fromBlocks 1 0 (-1) 1
  simp [Matrix.fromBlocks_multiply]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelAlgebra.Construction
