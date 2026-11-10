module

public import ArtinMatthews.StandardLocalBall
public import ArtinMatthews.StandardLocalFourier
public import ArtinMatthews.StandardLocalBallDilation
public import ArtinMatthews.StandardLocalBallFourier
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

/-! The modulus of an actual finite-place dilation, with the absolute
value normalized by the residue cardinality. -/

namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory Set
open scoped NumberField ENNReal NNReal Pointwise
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

theorem sourceLocalBall_smul (n : ℤ) (t : (P.adicCompletion K)ˣ) :
    t • sourceLocalBall K P n =
      sourceLocalBall K P (n + WithZero.log (sourceLocalValuation K P (t : P.adicCompletion K))) := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  change (((t⁻¹ : (P.adicCompletion K)ˣ) : P.adicCompletion K) * x ∈
    sourceLocalBall K P n) ↔ _
  rw [Units.val_inv_eq_inv_val, ← div_eq_inv_mul]
  exact sourceLocalBall_div_mem K P n t x

theorem sourceLocalDistribHaarChar (t : (P.adicCompletion K)ˣ) :
    distribHaarChar (P.adicCompletion K) t = ‖(t : P.adicCompletion K)‖₊ := by
  let μ := sourceLocalSelfDual K P
  let : μ.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  have h := congrArg ENNReal.toReal (distribHaarChar_mul μ t (sourceLocalBall K P 0))
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, sourceLocalBall_smul] at h
  apply NNReal.coe_injective
  exact mul_right_cancel₀ (sourceLocalBall_volume_pos K P 0).ne'
    (h.trans (sourceLocalBall_dilation_volume K P μ 0 t))

theorem sourceLocalSelfDual_map_mul (t : (P.adicCompletion K)ˣ) :
    (sourceLocalSelfDual K P).map (fun x => (t : P.adicCompletion K) * x) =
      (‖((t⁻¹ : (P.adicCompletion K)ˣ) : P.adicCompletion K)‖₊ : ℝ≥0∞) •
        sourceLocalSelfDual K P := by
  let μ := sourceLocalSelfDual K P
  let : μ.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  ext1 s hs
  have hm : Measurable (fun x : P.adicCompletion K => (t : P.adicCompletion K) * x) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm hs, Measure.smul_apply, smul_eq_mul]
  have he : (fun x : P.adicCompletion K => (t : P.adicCompletion K) * x) ⁻¹' s = t⁻¹ • s := by
    change (fun x : P.adicCompletion K => t • x) ⁻¹' s = t⁻¹ • s
    simpa only [inv_inv] using preimage_smul_inv t⁻¹ s
  rw [he, ← distribHaarChar_mul μ, sourceLocalDistribHaarChar]

end
end ArtinMatthews.SourcePhysical
