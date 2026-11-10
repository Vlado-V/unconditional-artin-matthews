module

public import ArtinMatthews.SourceKPTameJacquetIntegralCore
public import ArtinMatthews.SourceJacquetHaarDilation
public import ArtinMatthews.SourceJacquetIntegrabilityDilation
public import ArtinMatthews.SourceKPTameJacquetShellIntegral
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

/-! The actual truncated Jacquet integral on the original x-balls.
After the change x = π^e H, the genuine Haar factor combines with
the pointwise modular and torus factors to give Q^(-2e/3). -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceLocalValuation K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "B" => sourceLocalBall K P.val
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)

def sourceKPTameJacquetTruncation (e N : ℕ) : ZMod 3 → ℂ :=
  ∫ x in B (N : ℤ), sourceKPTameJacquetIntegrand K hζ S₀ P e x ∂μ₀

theorem sourceKPTameJacquetScaledIntegral_ball (hP : P.val ∉ traceBadPlaces K) (e N : ℕ) :
    IntegrableOn (sourceKPTameJacquetScaledIntegrand K hζ S₀ P e) (B (N : ℤ)) μ₀ ∧
      (∫ H in B (N : ℤ), sourceKPTameJacquetScaledIntegrand K hζ S₀ P e H ∂μ₀) =
        sourceJacquetScale Q₀ ((e : ℝ) / 3) •
          (sourceJacquetBasis (-(e : ZMod 3)) + ∑ l ∈ Finset.Icc 1 N,
            (sourceJacquetScale Q₀ ((l : ℝ) / 3) * sourceJacquetActualShell K hζ S₀ P e l) •
              sourceJacquetBasis (-(e : ZMod 3) + 2 * (l : ZMod 3))) := by
  have hzero := sourceKPTameJacquetScaledIntegral_ball_zero K hζ S₀ P e
  have hshell l := sourceKPTameJacquetScaledIntegral_shell K hζ S₀ P hP e l
  have h := sourceJacquetBall_integral_shells K P.val
    (sourceKPTameJacquetScaledIntegrand K hζ S₀ P e) hzero.1 (fun l _ => (hshell l).1) N
  refine ⟨h.1, ?_⟩
  rw [h.2, hzero.2, smul_add, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have he : ((e : ℤ) : ZMod 3) = (e : ZMod 3) := Int.cast_natCast e
  have hl₀ : ((l : ℤ) : ZMod 3) = (l : ZMod 3) := Int.cast_natCast l
  have hb : ((2 * (l : ℤ) - (e : ℤ) : ℤ) : ZMod 3) = -(e : ZMod 3) + 2 * (l : ZMod 3) := by
    rw [Int.cast_sub, Int.cast_mul, he, hl₀, sub_eq_add_neg, add_comm]
    rfl
  rw [(hshell l).2, hb, smul_smul, ← mul_assoc,
    ← sourceJacquetScale_add (sourceJacquetPrimeNorm_pos K S₀ P), ← add_div]

theorem sourceKPTameJacquetTruncation_formula (hP : P.val ∉ traceBadPlaces K) (e N : ℕ) :
    IntegrableOn (sourceKPTameJacquetIntegrand K hζ S₀ P e) (B (N : ℤ)) μ₀ ∧
      sourceKPTameJacquetTruncation K hζ S₀ P e N =
        sourceJacquetScale Q₀ (-2 * (e : ℝ) / 3) •
          (sourceJacquetBasis (-(e : ZMod 3)) + ∑ l ∈ Finset.Icc 1 (N + e),
            (sourceJacquetScale Q₀ ((l : ℝ) / 3) * sourceJacquetActualShell K hζ S₀ P e l) •
              sourceJacquetBasis (-(e : ZMod 3) + 2 * (l : ZMod 3))) := by
  let t := π₀ ^ (e : ℤ)
  let f := sourceKPTameJacquetIntegrand K hζ S₀ P e
  have ht : ν₀ (t : L) = WithZero.exp (-(e : ℤ)) := by
    dsimp only [t]
    rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀]
  have hImage := sourceJacquetBall_mul_image K P.val ((N + e : ℕ) : ℤ) (-(e : ℤ)) t ht
  rw [show ((N + e : ℕ) : ℤ) + -(e : ℤ) = (N : ℤ) by omega] at hImage
  have h := sourceKPTameJacquetScaledIntegral_ball K hζ S₀ P hP e (N + e)
  have hf : (fun H : L => f ((t : L) * H)) = sourceKPTameJacquetScaledIntegrand K hζ S₀ P e := by
    funext H
    change f (((π₀ ^ (e : ℤ) : Lˣ) : L) * H) = f ((π₀ : L) ^ (e : ℤ) * H)
    rw [Units.val_zpow_eq_zpow_val]
  have hI := (sourceJacquetIntegrableOn_dilation_iff K P.val hP t (B ((N + e : ℕ) : ℤ)) f).mpr
    (hf.symm ▸ h.1)
  rw [hImage] at hI
  refine ⟨hI, ?_⟩
  change (∫ x in B (N : ℤ), f x ∂μ₀) = _
  rw [← hImage, sourceJacquetSetIntegral_dilation K P.val hP t _ f, hf, h.2,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change (‖(t : L)‖ : ℂ) • (_ : ZMod 3 → ℂ) = _
  rw [sourceJacquetDilation_norm K P.val (-(e : ℤ)) t ht, smul_smul,
    ← sourceJacquetScale_add (sourceJacquetPrimeNorm_pos K S₀ P)]
  rw [show (↑(-(e : ℤ)) : ℝ) + (e : ℝ) / 3 = -2 * (e : ℝ) / 3 by push_cast; ring]

end
end ArtinMatthews
