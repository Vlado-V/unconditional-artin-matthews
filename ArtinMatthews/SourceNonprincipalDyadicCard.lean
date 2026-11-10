module

public import ArtinMatthews.SourceNonprincipalFrequencyDyads
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

/-! Count the literal frequency dyads from their actual norm series.
The finite unit-class fiber and exterior ideal count are already in that
series. The exponent loss can be chosen arbitrarily small. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def sourceFrequencyRepresentativeNormMass (σ : ℝ) : ℝ :=
  ∑' i : SourceFrequencyRepresentativeIndex F S₀, (sourceFrequencyRepresentativeNorm F S₀ i : ℝ)^(-σ)

theorem sourceFrequencyRepresentativeNormMass_nonneg (σ : ℝ) :
    0 ≤ sourceFrequencyRepresentativeNormMass F S₀ σ :=
  tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem sourceNonprincipalFrequencyDyad_card_le (σ : ℝ) (hσ : 1 < σ) (j : ℕ) :
    (Fintype.card (SourceNonprincipalFrequencyDyad F S₀ j) : ℝ) ≤
      (sourceFrequencyRepresentativeNormMass F S₀ σ*(2 : ℝ)^σ)*((2 : ℝ)^j)^σ := by
  let D := SourceNonprincipalFrequencyDyad F S₀ j
  let f (i : SourceFrequencyRepresentativeIndex F S₀) : ℝ := (sourceFrequencyRepresentativeNorm F S₀ i : ℝ)^(-σ)
  let e : D ↪ SourceFrequencyRepresentativeIndex F S₀ :=
    ⟨fun i => i.val.val, fun _ _ h => Subtype.ext (Subtype.ext h)⟩
  let U : ℝ := (2 : ℝ)^j
  have hU : 0 < U := by dsimp [U]; positivity
  have h2U : 0 < 2*U := by positivity
  have hs : Summable f := sourceFrequencyRepresentativeNorm_summable F S₀ hσ
  have hfn (i : SourceFrequencyRepresentativeIndex F S₀) : 0 ≤ f i :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hp (i : D) : (2*U)^(-σ) ≤ f (e i) := by
    have hq : 0 < (sourceFrequencyRepresentativeNorm F S₀ i.val.val : ℝ) := by
      exact_mod_cast sourceFrequencyRepresentativeNorm_pos F S₀ i.val.val
    have hqi : (sourceFrequencyRepresentativeNorm F S₀ i.val.val : ℝ) ≤ 2*U := by
      have h : (sourceFrequencyRepresentativeNorm F S₀ i.val.val : ℝ) < (2 : ℝ)^(j+1) := by
        exact_mod_cast i.property.2
      simpa only [U, pow_succ, mul_comm] using h.le
    exact Real.rpow_le_rpow_of_nonpos hq hqi (by linarith)
  have hsum : (Fintype.card D : ℝ)*(2*U)^(-σ) ≤ sourceFrequencyRepresentativeNormMass F S₀ σ := by
    calc
      _ = ∑ _ : D, (2*U)^(-σ) := by simp [nsmul_eq_mul]
      _ ≤ ∑ i : D, f (e i) := Finset.sum_le_sum (fun i _ => hp i)
      _ = ∑ i ∈ Finset.univ.map e, f i := (Finset.sum_map _ _ _).symm
      _ ≤ _ := hs.sum_le_tsum _ (fun i _ => hfn i)
  have h := mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg h2U.le σ)
  rw [mul_assoc, ← Real.rpow_add h2U, neg_add_cancel, Real.rpow_zero, mul_one,
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hU.le] at h
  exact h.trans_eq (by dsimp only [U]; ring)

end
end ArtinMatthews.SourceEulerAssembly
