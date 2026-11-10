module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicGram.PeriodicPoisson
public import OAI.NumberTheory.CubicGram.SquarefreeGauss
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
public import OAI.NumberTheory.CubicGram.CubeExtraction
public import OAI.NumberTheory.CubicGram.GaussCharacters
public import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof
public import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimePNTProofSplitting


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Two exact cubic-symbol values detect the unit and ramified factors.
Their values are computed from the finite Euler definition. -/
noncomputable section
namespace CubicFirstMoment

lemma primary_neg_two : primary (-2:Eisenstein) := ⟨-1,by ring⟩

lemma normNat_neg_two : normNat (-2:Eisenstein)=4 := by
  apply Nat.cast_injective (R := ℝ)
  rw [normNat_cast]
  change Complex.normSq (-2:ℂ) = (4:ℝ)
  norm_num

lemma cubicSymbol_neg_two_omega : cubicSymbol (-2:Eisenstein) omegaE = omega := by
  rw [cubicSymbol_omega_norm primary_neg_two,normNat_neg_two]
  norm_num

lemma cubicSymbol_neg_two_lambda : cubicSymbol (-2:Eisenstein) lambdaE = 1 := by
  have he : (-2:Eisenstein) ∣ lambdaE-1 := ⟨-omegaE,by dsimp [lambdaE]; ring⟩
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub he)]
  simpa using (cubicSymbol_pow_upper primary_neg_two (1:Eisenstein) 0)

lemma primary_seven_factor : primary (1+3*omegaE) := ⟨omegaE,by ring⟩

lemma normNat_seven_factor : normNat (1+3*omegaE)=7 := by
  apply Nat.cast_injective (R := ℝ)
  rw [normNat_cast]
  change Complex.normSq ((1:ℂ)+3*omega) = (7:ℝ)
  have h := coordinates_norm 1 3
  norm_num at h
  exact h

lemma primaryPrime_seven_factor : primaryPrime (1+3*omegaE) :=
  ⟨primary_seven_factor,prime_of_normNat_prime (by rw [normNat_seven_factor]; norm_num)⟩

lemma cubicSymbol_seven_factor_lambda : cubicSymbol (1+3*omegaE) lambdaE = omega^2 := by
  rw [cubicSymbol_prime primaryPrime_seven_factor]
  apply cubicSymbol_euler_value primaryPrime_seven_factor
    (residue_isUnit_of_isCoprime (primary_coprime_lambda primary_seven_factor)) (2:Fin 3)
  rw [normNat_seven_factor]
  norm_num only
  apply residue_eq_of_dvd_sub
  refine ⟨1+omegaE,?_⟩
  dsimp [lambdaE]
  ring

lemma cubicSymbol_seven_factor_omega : cubicSymbol (1+3*omegaE) omegaE = omega^2 := by
  rw [cubicSymbol_omega_norm primary_seven_factor,normNat_seven_factor]
  norm_num

end CubicFirstMoment

end

end OAI
