module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusMass
public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SourcePrimeIdealFactorization
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

/-! Actual Dedekind majorants for the exterior-prime coordinates. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]

def sourcePrimeExponentNonzeroIdealEmbedding (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    SourcePrimeExponents F S₀ ↪ {I : Ideal (𝓞 F) // I ≠ ⊥} where
  toFun e := ⟨sourcePrimeExponentIdeal F S₀ e, sourcePrimeExponentIdeal_ne_bot F S₀ e⟩
  inj' := fun _ _ h => sourcePrimeExponentIdeal_injective F S₀ (congrArg Subtype.val h)

theorem sourcePrimeExponentNorm_pos (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e : SourcePrimeExponents F S₀) : 0 < sourcePrimeExponentNorm F S₀ e := by
  rw [← sourcePrimeExponentIdeal_norm]
  exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (sourcePrimeExponentIdeal_ne_bot F S₀ e))

theorem sourcePrimeExponentNorm_summable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun e : SourcePrimeExponents F S₀ => (sourcePrimeExponentNorm F S₀ e : ℝ) ^ (-σ)) := by
  have hs := VaryingKummerAnalytic.HeckeIdealMobius.normSeries_summable F
    (show 0 < σ - 1 by linarith)
  have he : 1 + (σ - 1) = σ := by ring
  rw [he] at hs
  have h := hs.comp_injective (sourcePrimeExponentNonzeroIdealEmbedding F S₀).injective
  change Summable (fun e : SourcePrimeExponents F S₀ =>
    (Ideal.absNorm (sourcePrimeExponentIdeal F S₀ e) : ℝ) ^ (-σ)) at h
  simpa only [sourcePrimeExponentIdeal_norm] using h

theorem sourcePrimeExponent_summable_of_bound (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (f : SourcePrimeExponents F S₀ → ℂ) {σ : ℝ} (hσ : 1 < σ)
    (hf : ∀ e, ‖f e‖ ≤ (sourcePrimeExponentNorm F S₀ e : ℝ) ^ (-σ)) : Summable f :=
  Summable.of_norm_bounded (sourcePrimeExponentNorm_summable F S₀ hσ) hf

theorem sourcePrimeExponentNorm_tsum_le (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    {σ : ℝ} (hσ : 1 < σ) :
    (∑' e : SourcePrimeExponents F S₀, (sourcePrimeExponentNorm F S₀ e : ℝ) ^ (-σ)) ≤
      VaryingKummerAnalytic.HeckeIdealMobius.normSeries F (σ - 1) := by
  apply Summable.tsum_le_tsum_of_inj (sourcePrimeExponentNonzeroIdealEmbedding F S₀)
    (sourcePrimeExponentNonzeroIdealEmbedding F S₀).injective
  · intro I _
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro e
    change (sourcePrimeExponentNorm F S₀ e : ℝ) ^ (-σ) ≤
      (Ideal.absNorm (sourcePrimeExponentIdeal F S₀ e) : ℝ) ^ (-(1 + (σ - 1)))
    rw [sourcePrimeExponentIdeal_norm, show 1 + (σ - 1) = σ by ring]
  · exact sourcePrimeExponentNorm_summable F S₀ hσ
  · have h := VaryingKummerAnalytic.HeckeIdealMobius.normSeries_summable F
      (show 0 < σ - 1 by linarith)
    have he : 1 + (σ - 1) = σ := by ring
    simpa only [he] using h

end
end ArtinMatthews
