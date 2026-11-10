module

public import ArtinMatthews.SpectralJOddSynthesis
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

/-! A summable odd-order majorant retains the extra small-argument factor.
It will give absolute weight-and-modulus convergence at the infinity cusp. -/
noncomputable section
open Set

namespace ArtinMatthews

theorem spectralJOddSynthesisTerm_small_argument (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ (j : ℕ) (c : ℝ), 1 ≤ c →
      ‖spectralJOddSynthesisTerm f j (Q/c)‖ ≤
        (C*(A^(2*j+1)/((2*j+1).factorial : ℝ)))/c := by
  obtain ⟨C₀,A₀,hC₀,hA₀,hcoeff⟩ := spectralJDiscreteCoefficient_factorial_bound f hf hc hp
  refine ⟨2*C₀*Real.exp (Q^2/4),A₀*Q/2,by positivity,by positivity,?_⟩
  intro j c hc
  let u : ℝ := 1/c
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; exact (div_le_one hcp).mpr hc
  have hQu : 0 ≤ Q*u := mul_nonneg hQ hu
  have hQuQ : Q*u ≤ Q := mul_le_of_le_one_right hQ hu1
  have hsq : (Q*u)^2 ≤ Q^2 := (sq_le_sq₀ hQu hQ).mpr hQuQ
  have hpow : u^(2*j+1) ≤ u := by
    simpa using pow_le_pow_of_le_one hu hu1 (show 1 ≤ 2*j+1 by omega)
  have hx : Q/c = Q*u := by dsimp [u]; ring
  rw [hx]
  calc
    _ ≤ 2*C₀*Real.exp ((Q*u)^2/4)*
        ((A₀*(|Q*u|/2))^(2*j+1)/((2*j+1).factorial : ℝ)) :=
      spectralJOddSynthesisTerm_norm_le f hC₀ hA₀ hcoeff j (Q*u)
    _ = (2*C₀)*Real.exp ((Q*u)^2/4)*
        ((A₀*Q/2)^(2*j+1)/((2*j+1).factorial : ℝ))*u^(2*j+1) := by
      rw [abs_of_nonneg hQu,show A₀*(Q*u/2) = (A₀*Q/2)*u by ring,mul_pow]
      ring
    _ ≤ (2*C₀)*Real.exp (Q^2/4)*
        ((A₀*Q/2)^(2*j+1)/((2*j+1).factorial : ℝ))*u := by gcongr
    _ = _ := by dsimp [u]; ring

theorem spectralJOddMajorant_summable (C A : ℝ) :
    Summable (fun j : ℕ => C*(A^(2*j+1)/((2*j+1).factorial : ℝ))) := by
  exact ((NormedSpace.expSeries_div_hasSum_exp A).summable.comp_injective
    (show Function.Injective (fun j : ℕ => 2*j+1) from fun a b h => by dsimp only at h; omega)).mul_left C

end ArtinMatthews
