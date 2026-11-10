module

public import ArtinMatthews.SourceKPAdeleLocalCover
public import ArtinMatthews.SourceKPCompactWeyl
public import ArtinMatthews.SourceKPProjectiveSections
public import ArtinMatthews.SourceKubotaMultipliers
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exact Weyl conjugate of an upper root in the genuine local
cubic cover, including its image in the full adelic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

theorem sourceGL2Weyl_upper_weyl {F : Type*} [Field F] (x : F) :
    sourceGL2Weyl * sourceGL2Upper x * sourceGL2Weyl = sourceGL2Lower x := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGL2Weyl, sourceGL2Upper, sourceGL2Lower, Matrix.mul_apply, Fin.sum_univ_two]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P

theorem sourceFiniteKP2Multiplier_weyl_upper_weyl (x : L) :
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Weyl * sourceGL2Upper x) sourceGL2Weyl = 1 := by
  change sourceKP2Multiplier (sourceFiniteKPHilbert K hζ P)
    (sourceGL2Weyl * sourceGL2Upper x) sourceGL2Weyl = 1
  rw [sourceKP2Multiplier_right_weyl_formula _ (sourceFiniteKPHilbert_minus_right K hζ P),
    sourceGL2Weyl_upper_weyl, sourceKubotaX_weyl_upper, div_one, map_mul,
    sourceGL2Weyl_det, sourceGL2Upper_det, mul_one]
  rw [map_div, sourceFiniteKPHilbert_diag, sourceFiniteKPHilbert_minus_right, div_one]

theorem sourceFiniteKP2ProjectiveLift_weyl_upper_weyl (x : L) :
    l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x) * l₀ sourceGL2Weyl = l₀ (sourceGL2Lower x) := by
  rw [sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _
    (sourceKP2Multiplier_weyl_upper (sourceFiniteKPHilbert K hζ P) x),
    sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _
      (sourceFiniteKP2Multiplier_weyl_upper_weyl K hζ P x), sourceGL2Weyl_upper_weyl]

theorem sourceKPAdelicLocalProjective_weyl_upper_weyl (x : L) :
    sourceKPAdelicLocalProjective K hζ P (l₀ sourceGL2Weyl) *
        sourceKPAdelicLocalProjective K hζ P (l₀ (sourceGL2Upper x)) *
        sourceKPAdelicLocalProjective K hζ P (l₀ sourceGL2Weyl) =
      sourceKPAdelicLocalProjective K hζ P (l₀ (sourceGL2Lower x)) := by
  rw [← map_mul, ← map_mul, sourceFiniteKP2ProjectiveLift_weyl_upper_weyl]

end
end ArtinMatthews
