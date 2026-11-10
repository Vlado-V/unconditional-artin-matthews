module

public import ArtinMatthews.SpectralGamma0EigenPlaneBound
public import ArtinMatthews.SpectralGamma0GreenSpectralBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Absolute convergence of the genuine Green-squared point series. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0GreenPointCoefficient (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N)
    (p : ℝ × ℝ) : ℂ :=
  (i.1.re : ℂ) * gamma0FullCuspidalPlaneRepresentative N r Y hY i p

theorem gamma0GreenPointCoefficient_norm_sq (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N)
    (p : ℝ × ℝ) :
    ‖gamma0GreenPointCoefficient N r Y hY i p‖^2 =
      i.1.re^2 * ‖gamma0FullCuspidalPlaneRepresentative N r Y hY i p‖^2 := by
  simp only [gamma0GreenPointCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    mul_pow,sq_abs]

theorem gamma0GreenPointCoefficient_square_compact_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K,
      Summable (fun i => ‖gamma0GreenPointCoefficient N r Y hY i p‖^2) ∧
      (∑' i, ‖gamma0GreenPointCoefficient N r Y hY i p‖^2) ≤ C^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalPlaneRepresentative_green_weighted_sum_bound N r Y hY hK hKΩ
  refine ⟨C,hC,?_⟩
  intro p hp
  have hs (s : Finset (Gamma0AllHeightSpectralIndex N)) :
      (∑ i ∈ s, ‖gamma0GreenPointCoefficient N r Y hY i p‖^2) ≤ C^2 := by
    simpa only [gamma0GreenPointCoefficient_norm_sq] using hb s p hp
  exact ⟨summable_of_sum_le (fun _ => sq_nonneg _) hs,
    Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hs⟩

theorem gamma0GreenPointCoefficient_square_summable
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    (p : ℝ × ℝ) (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) :
    Summable (fun i => ‖gamma0GreenPointCoefficient N r Y hY i p‖^2) := by
  obtain ⟨_,_,hb⟩ := gamma0GreenPointCoefficient_square_compact_bound N r Y hY
    (isCompact_singleton (x := p)) (by simpa only [singleton_subset_iff])
  exact (hb p (mem_singleton p)).1

theorem finite_complex_kernel_norm_sum_le {ι : Type*} (s : Finset ι)
    (f g : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : (∑ i ∈ s, ‖f i‖^2) ≤ C^2) (hg : (∑ i ∈ s, ‖g i‖^2) ≤ C^2) :
    (∑ i ∈ s, ‖f i * star (g i)‖) ≤ C^2 := by
  simp only [norm_mul,norm_star]
  have hsf : Real.sqrt (∑ i ∈ s, ‖f i‖^2) ≤ C := by
    simpa only [Real.sqrt_sq hC] using Real.sqrt_le_sqrt hf
  have hsg : Real.sqrt (∑ i ∈ s, ‖g i‖^2) ≤ C := by
    simpa only [Real.sqrt_sq hC] using Real.sqrt_le_sqrt hg
  exact (Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖f i‖) (fun i => ‖g i‖)).trans
    ((mul_le_mul hsf hsg (Real.sqrt_nonneg _) hC).trans_eq (pow_two C).symm)

def gamma0GreenSquaredPointKernel (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p q : ℝ × ℝ) : ℂ :=
  ∑' i, gamma0GreenPointCoefficient N r Y hY i p *
    star (gamma0GreenPointCoefficient N r Y hY i q)

theorem gamma0GreenSquaredPointKernel_compact_absolute_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ q ∈ K,
      Summable (fun i => ‖gamma0GreenPointCoefficient N r Y hY i p *
        star (gamma0GreenPointCoefficient N r Y hY i q)‖) ∧
      (∑' i, ‖gamma0GreenPointCoefficient N r Y hY i p *
        star (gamma0GreenPointCoefficient N r Y hY i q)‖) ≤ C^2 ∧
      ‖gamma0GreenSquaredPointKernel N r Y hY p q‖ ≤ C^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalPlaneRepresentative_green_weighted_sum_bound N r Y hY hK hKΩ
  refine ⟨C,hC,?_⟩
  intro p hp q hq
  have hs (s : Finset (Gamma0AllHeightSpectralIndex N)) :
      (∑ i ∈ s, ‖gamma0GreenPointCoefficient N r Y hY i p *
        star (gamma0GreenPointCoefficient N r Y hY i q)‖) ≤ C^2 := by
    apply finite_complex_kernel_norm_sum_le s _ _ C hC.le
    · simpa only [gamma0GreenPointCoefficient_norm_sq] using hb s p hp
    · simpa only [gamma0GreenPointCoefficient_norm_sq] using hb s q hq
  have hsum := summable_of_sum_le (fun i => norm_nonneg
    (gamma0GreenPointCoefficient N r Y hY i p * star (gamma0GreenPointCoefficient N r Y hY i q))) hs
  have hbound := hsum.tsum_le_of_sum_le hs
  exact ⟨hsum,hbound,(norm_tsum_le_tsum_norm hsum).trans hbound⟩

end ArtinMatthews
