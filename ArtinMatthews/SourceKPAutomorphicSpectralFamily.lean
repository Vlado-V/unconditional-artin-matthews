module

public import ArtinMatthews.SourceKPAutomorphicDefectGenuine
public import ArtinMatthews.SourceHilbertSpectralResidue
public import ArtinMatthews.SourceKPCompactGenuineH1
public import ArtinMatthews.SourceKPCompactGenuineClosedForm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
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

/-! The spectral family formed with the actual adelic defect and genuine form. -/
namespace ArtinMatthews
open NumberField Filter HilbertResolvent
open scoped NumberField AdeleRing MatrixGroups Topology InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "rK" => (InfinitePlace.nrComplexPlaces K : ℝ)
local notation "j" => sourceKPCompactGenuineH1Mass K hζ
local notation "H" => SourceKPGenuineAutomorphicL2 K hζ
local notation "V" => SourceKPCompactGenuineH1 K hζ

include hζ in
theorem sourceKPAutomorphicSpectralRank_pos : 0 < rK := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  have h : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero,zero_add] at h
  exact Nat.cast_pos.mpr h

theorem sourceKPAutomorphicSpectralParameter_eq (s : ℂ) :
    spectralParameter rK s = (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2) := by
  simp only [spectralParameter,Complex.ofReal_natCast]

def sourceKPAutomorphicTruncatedContinuation {T : ℝ} (hT : 1 ≤ T) : ℂ → H :=
  spectralCorrection j rK (sourceKPAutomorphicGenuineDefectL2 K hζ hT)

def sourceKPAutomorphicExceptionalResidue {T : ℝ} (hT : 1 ≤ T) : H :=
  exceptionalResidue j rK (sourceKPAutomorphicGenuineDefectL2 K hζ hT)

def sourceKPAutomorphicExceptionalRegularized {T : ℝ} (hT : 1 ≤ T) : ℂ → H :=
  exceptionalDesingularizedCorrection j (sourceKPAutomorphicSpectralRank_pos K hζ)
    (sourceKPAutomorphicGenuineDefectL2 K hζ hT)

theorem sourceKPAutomorphicTruncatedContinuation_analytic_initial {T : ℝ} (hT : 1 ≤ T) :
    AnalyticOnNhd ℂ (sourceKPAutomorphicTruncatedContinuation K hζ hT) {s | 1/2 < s.re} :=
  spectralCorrection_analyticOnNhd j (sourceKPCompactGenuineH1Mass_opNorm_le K hζ)
    (sourceKPAutomorphicSpectralRank_pos K hζ) _
    (sourceKPAutomorphicGenuineDefectL2_analyticAt K hζ hT)

theorem sourceKPAutomorphicSpectralPencil_isUnit_initial {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    IsUnit (pencil ((j).adjoint.comp j) (spectralParameter rK s)) := by
  apply spectralPencil_isUnit_of_half_lt j (sourceKPCompactGenuineH1Mass_opNorm_le K hζ)
    (sourceKPAutomorphicSpectralRank_pos K hζ)
  push_cast at hs
  have hdeg : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
  linarith

theorem sourceKPAutomorphicExceptionalRegularized_value {T : ℝ} (hT : 1 ≤ T) :
    sourceKPAutomorphicExceptionalRegularized K hζ hT (1/6) =
      sourceKPAutomorphicExceptionalResidue K hζ hT :=
  exceptionalDesingularizedCorrection_value j (sourceKPAutomorphicSpectralRank_pos K hζ) _

theorem sourceKPAutomorphicTruncatedContinuation_eq_of_pencil {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1) (u : V)
    (hu : pencil ((j).adjoint.comp j) (spectralParameter rK s) u =
      -(j).adjoint (sourceKPAutomorphicGenuineDefectL2 K hζ hT s)) :
    sourceKPAutomorphicTruncatedContinuation K hζ hT s = j u := by
  let d := sourceKPAutomorphicGenuineDefectL2 K hζ hT s
  let B := pencil ((j).adjoint.comp j) (spectralParameter rK s)
  have hB : IsUnit B := sourceKPAutomorphicSpectralPencil_isUnit_initial K hζ hs
  have he : B (forcedVector j (spectralParameter rK s) d) = B u :=
    (forcedVector_solves j (spectralParameter rK s) d hB).trans hu.symm
  have hInv (v : V) : Ring.inverse B (B v) = v := by
    have h := congrArg (fun A : V →L[ℂ] V => A v) (Ring.inverse_mul_cancel B hB)
    exact h
  unfold sourceKPAutomorphicTruncatedContinuation
  rw [spectralCorrection_eq_j_forcedVector]
  exact congrArg (fun v : V => j v)
    ((hInv _).symm.trans ((congrArg (fun v : V => Ring.inverse B v) he).trans (hInv _)))

end
end ArtinMatthews
