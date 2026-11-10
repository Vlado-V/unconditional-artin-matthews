module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusConvolution
public import ArtinMatthews.QuadraticHeckePrincipalNormSeries
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

namespace ArtinMatthews
open NumberField Set VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "NZ" => {J : Ideal (𝓞 F) // J ≠ ⊥}

/-- The literal finite norm cutoff on nonzero integral ideals. -/
def quadraticHeckeIdealNormBall (H : ℝ) : Finset NZ :=
  (HeckeIdealMobius.normCutoff F H).subtype (fun J => J ≠ ⊥)

theorem mem_quadraticHeckeIdealNormBall {H : ℝ} (hH : 0 ≤ H) (J : NZ) :
    J ∈ quadraticHeckeIdealNormBall F H ↔ (Ideal.absNorm J.val : ℝ) ≤ H := by
  rw [quadraticHeckeIdealNormBall, Finset.mem_subtype, HeckeIdealMobius.mem_normCutoff F hH]

theorem quadraticHeckeIdealNormTail_pointwise {q H σ u : ℝ}
    (hq : 0 < q) (hH : 0 < H) (hHq : H ≤ q) (huσ : u ≤ σ) :
    q ^ (-σ) ≤ H ^ (u - σ) * q ^ (-u) := by
  have hexp : u - σ ≤ 0 := sub_nonpos.mpr huσ
  have hp : q ^ (u - σ) ≤ H ^ (u - σ) :=
    Real.rpow_le_rpow_of_nonpos hH hHq hexp
  calc
    q ^ (-σ) = q ^ (u - σ) * q ^ (-u) := by
      rw [← Real.rpow_add hq]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hq.le _)

theorem quadraticHeckeIdealNormTail_sum {u σ H : ℝ}
    (hu : 1 < u) (huσ : u ≤ σ) (hH : 0 < H) :
    (∑' J : {J : NZ // H < (Ideal.absNorm J.val : ℝ)},
      (Ideal.absNorm J.val.val : ℝ) ^ (-σ)) ≤
      H ^ (u - σ) *
        ∑' J : NZ, (Ideal.absNorm J.val : ℝ) ^ (-u) := by
  let tail := {J : NZ | H < (Ideal.absNorm J.val : ℝ)}
  have hsum := (quadraticHeckePrincipalIdealNorm_summable F hu).subtype (fun J => J ∈ tail)
  have hlarge : Summable (fun J : tail =>
      H ^ (u - σ) * (Ideal.absNorm J.val.val : ℝ) ^ (-u)) :=
    hsum.mul_left _
  have hbound (J : tail) :
      (Ideal.absNorm J.val.val : ℝ) ^ (-σ) ≤
        H ^ (u - σ) * (Ideal.absNorm J.val.val : ℝ) ^ (-u) :=
    quadraticHeckeIdealNormTail_pointwise (quadraticHeckePrincipalIdealNorm_pos F J.val)
      hH J.property.le huσ
  have hsmall : Summable (fun J : tail => (Ideal.absNorm J.val.val : ℝ) ^ (-σ)) :=
    Summable.of_nonneg_of_le (fun J => Real.rpow_nonneg (Nat.cast_nonneg _) _) hbound hlarge
  calc
    _ ≤ ∑' J : tail, H ^ (u - σ) * (Ideal.absNorm J.val.val : ℝ) ^ (-u) :=
      hsmall.tsum_le_tsum hbound hlarge
    _ = H ^ (u - σ) * ∑' J : tail, (Ideal.absNorm J.val.val : ℝ) ^ (-u) :=
      tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.tsum_subtype_le (fun J : NZ => (Ideal.absNorm J.val : ℝ) ^ (-u))
        tail (fun J => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (quadraticHeckePrincipalIdealNorm_summable F hu))
      (Real.rpow_nonneg hH.le _)

end
end ArtinMatthews
