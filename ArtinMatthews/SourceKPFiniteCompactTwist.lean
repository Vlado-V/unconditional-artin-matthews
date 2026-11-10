module

public import ArtinMatthews.SourceKPCochainTwist
public import ArtinMatthews.SourceFiniteKPMultipliers
public import ArtinMatthews.SourceFiniteKPTameUnits
public import ArtinMatthews.SourceKPCompactCoChain
public import ArtinMatthews.SourceFiniteKP2CompactSection
public import ArtinMatthews.SourceKubotaCocycle
public import ArtinMatthews.SourceKubotaFullScalars
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The actual local multiplier after changing to the compact section
at tame places. The normalization makes it one on every pair of
integral matrices at those places. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceKPFinitePhase (g : GL (Fin 2) (P.adicCompletion K)) : rootsOfUnity 3 (P.adicCompletion K) :=
  if (6 : 𝓞 K) ∉ P.asIdeal then sourceKPCompactPhase (sourceKPFiniteVal K P)
    (sourceFiniteKPHilbert K hζ P) g else 1

theorem sourceKPFinitePhase_one : sourceKPFinitePhase K hζ P 1 = 1 := by
  by_cases h6 : (6 : 𝓞 K) ∉ P.asIdeal
  · rw [sourceKPFinitePhase, ite_eq_left h6]
    exact sourceKPCompactPhase_zero_left _ _ _ (by simp)
  · rw [sourceKPFinitePhase, ite_eq_right h6]

theorem sourceKPFinitePhase_scalar (u : (P.adicCompletion K)ˣ) :
    sourceKPFinitePhase K hζ P (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  by_cases h6 : (6 : 𝓞 K) ∉ P.asIdeal
  · rw [sourceKPFinitePhase, ite_eq_left h6]
    exact sourceKPCompactPhase_zero_left _ _ _ (by simp [GeneralLinearGroup.coe_scalar])
  · rw [sourceKPFinitePhase, ite_eq_right h6]

theorem sourceKPFinitePhase_zero_left (g : GL (Fin 2) (P.adicCompletion K)) (hg : g 1 0 = 0) :
    sourceKPFinitePhase K hζ P g = 1 := by
  by_cases h6 : (6 : 𝓞 K) ∉ P.asIdeal
  · rw [sourceKPFinitePhase, ite_eq_left h6]
    exact sourceKPCompactPhase_zero_left _ _ _ hg
  · rw [sourceKPFinitePhase, ite_eq_right h6]

theorem sourceKPFinitePhase_unit_left (g : GL (Fin 2) (P.adicCompletion K))
    (hg : sourceKPFiniteVal K P (g 1 0) = 1) : sourceKPFinitePhase K hζ P g = 1 := by
  by_cases h6 : (6 : 𝓞 K) ∉ P.asIdeal
  · rw [sourceKPFinitePhase, ite_eq_left h6]
    exact sourceKPCompactPhase_unit_left _ _ _ hg
  · rw [sourceKPFinitePhase, ite_eq_right h6]

def sourceKPFiniteTwistedMultiplier (g h : GL (Fin 2) (P.adicCompletion K)) :
    rootsOfUnity 3 (P.adicCompletion K) :=
  sourceKPCochainTwist (sourceKPFinitePhase K hζ P) (sourceFiniteKP2Multiplier K hζ P) g h

theorem sourceKPFiniteTwistedMultiplier_cocycle (g h k : GL (Fin 2) (P.adicCompletion K)) :
    sourceKPFiniteTwistedMultiplier K hζ P g h * sourceKPFiniteTwistedMultiplier K hζ P (g * h) k =
      sourceKPFiniteTwistedMultiplier K hζ P g (h * k) * sourceKPFiniteTwistedMultiplier K hζ P h k :=
  sourceKPCochainTwist_cocycle _ _ (sourceFiniteKP2Multiplier_cocycle K hζ P) g h k

theorem sourceKPFiniteTwistedMultiplier_one_left (g : GL (Fin 2) (P.adicCompletion K)) :
    sourceKPFiniteTwistedMultiplier K hζ P 1 g = 1 :=
  sourceKPCochainTwist_one_left _ _ (sourceKPFinitePhase_one K hζ P) (sourceFiniteKP2Multiplier_one_left K hζ P) g

theorem sourceKPFiniteTwistedMultiplier_one_right (g : GL (Fin 2) (P.adicCompletion K)) :
    sourceKPFiniteTwistedMultiplier K hζ P g 1 = 1 :=
  sourceKPCochainTwist_one_right _ _ (sourceKPFinitePhase_one K hζ P) (sourceFiniteKP2Multiplier_one_right K hζ P) g

theorem sourceKPFiniteTwistedMultiplier_of_integral (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (g h : GL (Fin 2) (P.adicCompletion K))
    (hg : SourceKPIntegralMatrix (sourceKPFiniteVal K P) g)
    (hh : SourceKPIntegralMatrix (sourceKPFiniteVal K P) h) :
    sourceKPFiniteTwistedMultiplier K hζ P g h = 1 := by
  let G : SourceFiniteKP2Integral K P := ⟨g, hg⟩
  let H : SourceFiniteKP2Integral K P := ⟨h, hh⟩
  have he := congrArg SourceFiniteKP2Cover.central ((sourceFiniteKP2CompactSection K hζ P h6).map_mul G H)
  unfold sourceKPFiniteTwistedMultiplier sourceKPCochainTwist
  simp only [sourceKPFinitePhase, ite_eq_left h6]
  exact div_eq_one.mpr he.symm

theorem sourceKPFiniteTwistedMultiplier_scalar_comm (g : GL (Fin 2) (P.adicCompletion K))
    (u : (P.adicCompletion K)ˣ) :
    sourceKPFiniteTwistedMultiplier K hζ P (GeneralLinearGroup.scalar (Fin 2) u) g =
      sourceKPFiniteTwistedMultiplier K hζ P g (GeneralLinearGroup.scalar (Fin 2) u) :=
  sourceKPCochainTwist_comm _ _ _ _
    (GeneralLinearGroup.scalar_commute u g) (sourceFiniteKP2Multiplier_scalar_comm K hζ P g u)

theorem sourceKPFiniteTwistedMultiplier_scalar_pair (u v : (P.adicCompletion K)ˣ) :
    sourceKPFiniteTwistedMultiplier K hζ P (GeneralLinearGroup.scalar (Fin 2) u)
      (GeneralLinearGroup.scalar (Fin 2) v) = 1 := by
  rw [sourceKPFiniteTwistedMultiplier, sourceKPCochainTwist, ← map_mul (GeneralLinearGroup.scalar (Fin 2)),
    sourceKPFinitePhase_scalar, sourceKPFinitePhase_scalar, sourceKPFinitePhase_scalar,
    sourceFiniteKP2Multiplier_scalar_pair, one_mul, one_mul, div_one]

end
end ArtinMatthews
