module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralCuspPrincipalMoment
public import ArtinMatthews.SpectralFiniteDyadicCutoff
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralMixedCuspPrincipalDyadic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Finite native principal moments assemble over dyadic bands. -/

noncomputable section
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

theorem gamma0CuspPrincipalMoment_cutoff_le (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) {R B C : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hCut : ∀ i ∈ u, 1+|gamma0CuspPrincipalParameter N i| ≤ R)
    (hBand : ∀ k : ℕ, gamma0CuspPrincipalMoment N
      (u.filter (fun i => (2 : ℝ)^k ≤ 1+|gamma0CuspPrincipalParameter N i| ∧
        1+|gamma0CuspPrincipalParameter N i| ≤ 2*(2 : ℝ)^k)) b Y hY n hn ≤
          C*(((2 : ℝ)^k)^2+B*(2 : ℝ)^k)) :
    gamma0CuspPrincipalMoment N u b Y hY n hn ≤ 2*C*(R^2+B*R) := by
  let τ (i : Gamma0AllHeightSpectralIndex N) := 1+|gamma0CuspPrincipalParameter N i|
  let f (i : Gamma0AllHeightSpectralIndex N) :=
    ‖gamma0CuspUnitAmplitude N i b Y hY n hn‖^2/Real.cosh (Real.pi*gamma0CuspPrincipalParameter N i)
  have hτ (i : Gamma0AllHeightSpectralIndex N) (hi : i ∈ u) : 1 ≤ τ i ∧ τ i ≤ R :=
    ⟨le_add_of_nonneg_right (abs_nonneg _),hCut i hi⟩
  have hf (i : Gamma0AllHeightSpectralIndex N) (_ : i ∈ u) : 0 ≤ f i :=
    div_nonneg (sq_nonneg _) (Real.cosh_pos _).le
  have hW (k : ℕ) : (∑ i ∈ u.filter (fun i => (2 : ℝ)^k ≤ τ i ∧ τ i ≤ 2*(2 : ℝ)^k), f i) ≤
      C*(((2 : ℝ)^k)^2+B*(2 : ℝ)^k)*1 := by
    rw [mul_one]
    exact hBand k
  have h := spectral_nonneg_dyadic_cutoff_sum_le u τ f hR hB hC
    (zero_le_one : (0 : ℝ) ≤ 1) hτ hf hW
  simpa only [gamma0CuspPrincipalMoment,f,mul_one] using h

theorem gamma0MixedCusp_principal_cutoff_orbit_bessel :
    ∃ C : ℝ, 0 < C ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (u : Finset (Gamma0AllHeightSpectralIndex (r*s))) (n : ℤ) (hn : n ≠ 0)
        {R Y : ℝ}, 1 ≤ R → ∀ hY : 0 < Y,
      Y < (1/16)/(|cuspFourierFrequency 1 n| /
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      (∀ i ∈ u, 1/4 ≤ gamma0AllHeightGradientSpectralValue (r*s) i) →
      (∀ i ∈ u, 1+|gamma0CuspPrincipalParameter (r*s) i| ≤ R) →
      gamma0CuspPrincipalMoment (r*s) u (gamma0CuspOneOver s) Y hY n hn ≤
        C*(R^2+|cuspFourierFrequency 1 n| * R/((r*s : ℕ) : ℝ)) := by
  classical
  obtain ⟨C,hC,hDyad⟩ := gamma0MixedCusp_principal_dyadic_orbit_bessel
  refine ⟨2*C,by positivity,?_⟩
  intro r s ir is hcop u n hn R Y hR hY hYB hPrincipal hCut
  let q := |cuspFourierFrequency 1 n|
  let w := (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)
  let B := q/(((r*s : ℕ) : ℝ))
  have hp : 0 < q/w := div_pos (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn))
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos (r*s) (gamma0CuspOneOver s)))
  have hB : 0 ≤ B := by dsimp only [B,q]; positivity
  have h := gamma0CuspPrincipalMoment_cutoff_le (r*s) u (gamma0CuspOneOver s) Y hY n hn
    hR hB hC.le hCut (fun k => by
      let T : ℝ := 2^k
      have hT : 1 ≤ T := one_le_pow₀ (by norm_num)
      have hY' : Y < (T/16)/(q/w) := hYB.trans_le
        (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hT (by norm_num)) hp.le)
      have hK := hDyad r s hcop _ n hn (by linarith only [hT]) hY hY'
        (fun i hi => hPrincipal i (Finset.mem_filter.mp hi).1)
        (fun i hi => (Finset.mem_filter.mp hi).2)
      exact hK.trans_eq (by dsimp only [B,T,q]; ring))
  exact h.trans_eq (by dsimp only [B,q]; ring)

end ArtinMatthews
