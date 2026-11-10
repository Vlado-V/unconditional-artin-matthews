module

public import ArtinMatthews.SourceKPLocalBorelEmbedding
public import ArtinMatthews.SourceKPTameBorelValues
public import ArtinMatthews.SourceKPAdelicExceptionalLocalNorm
public import ArtinMatthews.SourceKPAdelicParametricLocal
public import ArtinMatthews.SourceKPLocalTorusCharacter
public import ArtinMatthews.SourceKPProjectiveBruhatCells
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
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

/-! The genuine normalized uniformizer action has period three on
the full global torus carrier, by its actual cube character. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (π : (P.adicCompletion K)ˣ)

theorem sourceKPLocalUniformizer_diagonal_mul (j k : ℤ) :
    sourceFiniteKPProjectiveBorelDiagonal K hζ P (π^j) *
      sourceFiniteKPProjectiveBorelDiagonal K hζ P (π^k) =
        sourceFiniteKPProjectiveBorelDiagonal K hζ P (π^(j+k)) := by
  apply Subtype.ext
  change sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal (π^j)) *
    sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal (π^k)) =
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal (π^(j+k)))
  rw [sourceFiniteKP2ProjectiveLift_diagonal_mul]
  have hh : sourceFiniteKPHilbert K hζ P (π^j) (π^k) = 1 := by
    simp only [map_zpow, MonoidHom.zpow_apply, sourceFiniteKPHilbert_diag, one_zpow]
  rw [hh, one_pow, map_one, one_mul, zpow_add]

def sourceKPLocalUniformizerHom : Multiplicative ℤ →* SourceFiniteKPProjectiveBorel K hζ P where
  toFun j := sourceFiniteKPProjectiveBorelDiagonal K hζ P (π^j.toAdd)
  map_one' := by
    apply Subtype.ext
    change sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal (π^(0 : ℤ))) = 1
    rw [zpow_zero]
    change sourceFiniteKP2ProjectiveLift K hζ P ((sourceGL2DiagonalHom (P.adicCompletion K)) 1) = 1
    rw [map_one, sourceFiniteKP2ProjectiveLift_one]
  map_mul' j k := (sourceKPLocalUniformizer_diagonal_mul K hζ P π j.toAdd k.toAdd).symm

theorem sourceKPLocalUniformizer_diagonal_zpow (j : ℤ) :
    sourceFiniteKPProjectiveBorelDiagonal K hζ P (π^j) =
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P π)^j := by
  have h := map_zpow (sourceKPLocalUniformizerHom K hζ P π) (Multiplicative.ofAdd (1 : ℤ)) j
  have hd : (Multiplicative.ofAdd (1 : ℤ))^j = Multiplicative.ofAdd j := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, Int.cast_id, mul_one]
  rw [hd] at h
  change sourceFiniteKPProjectiveBorelDiagonal K hζ P (π^j) =
    (sourceFiniteKPProjectiveBorelDiagonal K hζ P (π^(1 : ℤ)))^j at h
  simpa only [zpow_one] using h

def sourceKPLocalUniformizerNormalizingCharacter (s : ℂ) : Multiplicative ℤ →* ℂ where
  toFun j := Complex.exp ((s+1/2) * (j.toAdd : ℂ) * (Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ))
  map_one' := by simp
  map_mul' j k := by
    change Complex.exp ((s+1/2) * ((j.toAdd+k.toAdd : ℤ) : ℂ) *
      (Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) = _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

def sourceKPLocalNormalizedUniformizerAction (s : ℂ) :
    Representation ℂ (Multiplicative ℤ) (SourceKPAdelicTorusInducedSpace K hζ s) where
  toFun j := sourceKPLocalUniformizerNormalizingCharacter K P s j •
    sourceKPAdelicLocalBorelRepresentation K hζ P s (sourceKPLocalUniformizerHom K hζ P π j)
  map_one' := by simp only [map_one, one_smul]
  map_mul' j k := by
    rw [map_mul (sourceKPLocalUniformizerNormalizingCharacter K P s),
      map_mul (sourceKPLocalUniformizerHom K hζ P π),
      map_mul (sourceKPAdelicLocalBorelRepresentation K hζ P s)]
    exact (smul_mul_smul_comm _ _ _ _).symm

def sourceKPLocalUniformizerCycle (s : ℂ) : (Module.End ℂ (SourceKPAdelicTorusInducedSpace K hζ s))ˣ :=
  (sourceKPLocalNormalizedUniformizerAction K hζ P π s).asGroupHom (Multiplicative.ofAdd (1 : ℤ))

theorem sourceKPLocalUniformizerCycle_val (s : ℂ) :
    (sourceKPLocalUniformizerCycle K hζ P π s : Module.End ℂ (SourceKPAdelicTorusInducedSpace K hζ s)) =
      Complex.exp ((s+1/2)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) •
        sourceKPAdelicLocalBorelRepresentation K hζ P s (sourceFiniteKPProjectiveBorelDiagonal K hζ P π) := by
  calc
    _ = sourceKPLocalNormalizedUniformizerAction K hζ P π s (Multiplicative.ofAdd (1 : ℤ)) :=
      Representation.asGroupHom_apply _ _
    _ = sourceKPLocalUniformizerNormalizingCharacter K P s (Multiplicative.ofAdd (1 : ℤ)) •
        sourceKPAdelicLocalBorelRepresentation K hζ P s
          (sourceKPLocalUniformizerHom K hζ P π (Multiplicative.ofAdd (1 : ℤ))) := rfl
    _ = _ := by
      have hc : sourceKPLocalUniformizerNormalizingCharacter K P s (Multiplicative.ofAdd (1 : ℤ)) =
          Complex.exp ((s+1/2)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) := by
        change Complex.exp ((s+1/2)*((1 : ℤ) : ℂ)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) = _
        rw [Int.cast_one, mul_one]
      have hd : sourceKPLocalUniformizerHom K hζ P π (Multiplicative.ofAdd (1 : ℤ)) =
          sourceFiniteKPProjectiveBorelDiagonal K hζ P π := by
        change sourceFiniteKPProjectiveBorelDiagonal K hζ P (π^(1 : ℤ)) = _
        rw [zpow_one]
      rw [hc, hd]

theorem sourceKPLocalUniformizer_generator (s : ℂ) :
    sourceKPAdelicLocalBorelRepresentation K hζ P s (sourceFiniteKPProjectiveBorelDiagonal K hζ P π) =
      Complex.exp (-(s+1/2)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) •
        (sourceKPLocalUniformizerCycle K hζ P π s : Module.End ℂ (SourceKPAdelicTorusInducedSpace K hζ s)) := by
  rw [sourceKPLocalUniformizerCycle_val, smul_smul, ← Complex.exp_add]
  rw [show -(s+1/2)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ) +
    (s+1/2)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ) = 0 by ring,
    Complex.exp_zero, one_smul]

theorem sourceKPLocalNormalizedUniformizerAction_three
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (s : ℂ) (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPLocalNormalizedUniformizerAction K hζ P π s (Multiplicative.ofAdd (3 : ℤ)) v = v := by
  have hc := sourceKPAdelicLocalBorelRepresentation_cube K hζ P s π v
  have hn : (sourceKPIdeleComplexNorm K (s+1/2)
      ((IdeleGroup.ofAdicCompletion (𝓞 K) K P π)^3) : ℂ) =
      Complex.exp (-3*(s+1/2)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) := by
    rw [sourceKPIdeleComplexNorm_cube, sourceKPIdeleAbsoluteNorm_ofAdicCompletion,
      sourceKPAdelicUniformizer_norm K P π hπ, Real.log_inv, Complex.ofReal_neg]
    congr 1
    ring
  change Complex.exp ((s+1/2)*(3 : ℂ)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) •
    sourceKPAdelicLocalBorelRepresentation K hζ P s
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P (π^(3 : ℕ))) v = v
  calc
    _ = Complex.exp ((s+1/2)*(3 : ℂ)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) •
        ((sourceKPIdeleComplexNorm K (s+1/2)
          ((IdeleGroup.ofAdicCompletion (𝓞 K) K P π)^3) : ℂ) • v) :=
      congrArg (fun w : SourceKPAdelicTorusInducedSpace K hζ s =>
        Complex.exp ((s+1/2)*(3 : ℂ)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) • w) hc
    _ = v := by
      rw [hn, smul_smul, ← Complex.exp_add]
      rw [show (s+1/2)*(3 : ℂ)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ) +
        -3*(s+1/2)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ) = 0 by ring,
        Complex.exp_zero, one_smul]

theorem sourceKPLocalUniformizerCycle_cube
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ)) (s : ℂ) :
    sourceKPLocalUniformizerCycle K hζ P π s ^ 3 = 1 := by
  have hdom : (Multiplicative.ofAdd (1 : ℤ))^3 = Multiplicative.ofAdd (3 : ℤ) := by
    apply Multiplicative.toAdd.injective
    change (3 : ℕ) • (1 : ℤ) = 3
    norm_num
  unfold sourceKPLocalUniformizerCycle
  rw [← map_pow, hdom]
  apply Units.ext
  apply LinearMap.ext
  intro v
  exact sourceKPLocalNormalizedUniformizerAction_three K hζ P π hπ s v

end
end ArtinMatthews
