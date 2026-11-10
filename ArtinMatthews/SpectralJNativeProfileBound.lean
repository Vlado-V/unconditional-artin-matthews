module

public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralBesselJAllX
public import ArtinMatthews.SpectralSquareProfile
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

/-! The literal native J integral is continuous in the reciprocal-root profile norm. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

theorem spectralWeylJMultiplier_coordinate_bound (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(x : ℂ) * spectralWeylJMultiplier r x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := spectral_besselJ_vertical_allX 0 le_rfl
  let a : ℂ := (2 * (Real.pi : ℂ) * Complex.I) / (Real.sinh (Real.pi * r) : ℂ)
  let B := C * Real.exp (Real.pi * |r|)
  have hB : 0 ≤ B := mul_nonneg hC.le (Real.exp_pos _).le
  refine ⟨‖a‖ * (B + B), mul_nonneg (norm_nonneg _) (add_nonneg hB hB), ?_⟩
  intro x hx
  let Jp := Complex.besselJ (((2 * r : ℝ) : ℂ) * Complex.I) (x : ℂ)
  let Jm := Complex.besselJ (((-2 * r : ℝ) : ℂ) * Complex.I) (x : ℂ)
  have hp : ‖Jp‖ ≤ B := by
    have he := hb r x hx
    simp only [Complex.ofReal_zero, zero_add, Real.rpow_zero, mul_one] at he
    simpa only [Jp, B, Complex.ofReal_mul, Complex.ofReal_ofNat] using he
  have hm : ‖Jm‖ ≤ B := by
    have he := hb (-r) x hx
    simp only [Complex.ofReal_zero, zero_add, Real.rpow_zero, mul_one, abs_neg] at he
    have heq : (((-2 * r : ℝ) : ℂ) * Complex.I) = 2 * ((-r : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    simpa only [Jm, B, heq] using he
  have he : (x : ℂ) * spectralWeylJMultiplier r x = a * (Jp - Jm) := by
    rw [spectralWeylJMultiplier, ite_eq_left hx]
    change (x : ℂ) * (a * (Jp - Jm) / (x : ℂ)) = _
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hx.ne')
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hp hm)) (norm_nonneg _)

theorem spectralWeylJMultiplier_profile_integral (r : ℝ) (d : ℝ → ℂ) :
    (∫ x : ℝ in Ioi 0, ((x : ℂ) * d (x ^ 2)) * spectralWeylJMultiplier r x) =
      (1 / 2 : ℂ) * ∫ s : ℝ in Ioi 0, d s * spectralWeylJMultiplier r (Real.sqrt s) := by
  let v (s : ℝ) := d s * spectralWeylJMultiplier r (Real.sqrt s)
  calc
    _ = ∫ x : ℝ in Ioi 0, (x : ℂ) * v (x ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only [v]
      rw [Real.sqrt_sq (mem_Ioi.mp hx).le, mul_assoc]
    _ = _ := spectralSquare_integral v

theorem spectralWeylJMultiplier_profile_bound (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ → ℂ), Measurable d →
      IntegrableOn (fun s : ℝ => ‖d s‖ / Real.sqrt s) (Ioi 0) →
      IntegrableOn (fun x : ℝ => ((x : ℂ) * d (x ^ 2)) * spectralWeylJMultiplier r x) (Ioi 0) ∧
      ‖∫ x : ℝ in Ioi 0, ((x : ℂ) * d (x ^ 2)) * spectralWeylJMultiplier r x‖ ≤
        C * (∫ s : ℝ in Ioi 0, ‖d s‖ / Real.sqrt s) := by
  obtain ⟨C, hC, hb⟩ := spectralWeylJMultiplier_coordinate_bound r
  refine ⟨C / 2, by positivity, ?_⟩
  intro d hd hInt
  let v (s : ℝ) := d s * spectralWeylJMultiplier r (Real.sqrt s)
  have hM : Measurable (spectralWeylJMultiplier r) :=
    spectralWeylJMultiplier_measurable.comp (measurable_const.prodMk measurable_id)
  have hv : Measurable v := hd.mul (hM.comp Real.continuous_sqrt.measurable)
  have hbound (s : ℝ) (hs : 0 < s) : ‖v s‖ ≤ C * (‖d s‖ / Real.sqrt s) := by
    have hx : 0 < Real.sqrt s := Real.sqrt_pos_of_pos hs
    have he := hb (Real.sqrt s) hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at he
    have hn : ‖spectralWeylJMultiplier r (Real.sqrt s)‖ ≤ C / Real.sqrt s :=
      (le_div_iff₀ hx).mpr (by simpa only [mul_comm] using he)
    change ‖d s * spectralWeylJMultiplier r (Real.sqrt s)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ ‖d s‖ * (C / Real.sqrt s) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = _ := by ring
  have hvI : IntegrableOn v (Ioi 0) := by
    apply (hInt.const_mul C).mono' hv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
    exact hbound s (mem_Ioi.mp hs)
  refine ⟨?_, ?_⟩
  · apply ((spectralSquare_integrable v).mpr hvI).congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp only [v]
    rw [Real.sqrt_sq (mem_Ioi.mp hx).le, mul_assoc]
  · rw [spectralWeylJMultiplier_profile_integral, norm_mul]
    change ‖(1 / 2 : ℂ)‖ * ‖∫ s in Ioi (0 : ℝ), v s‖ ≤ _
    have hN : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hN]
    have hi : ‖∫ s in Ioi (0 : ℝ), v s‖ ≤
        ∫ s in Ioi (0 : ℝ), C * (‖d s‖ / Real.sqrt s) := by
      apply norm_integral_le_of_norm_le (hInt.const_mul C)
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
      exact hbound s (mem_Ioi.mp hs)
    rw [integral_const_mul] at hi
    exact (mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by ring)

theorem spectralJCompactProfile_norm_div_sqrt_integrable {g : ℝ → ℂ}
    (hg : Continuous g) (hc : HasCompactSupport g) (hpos : tsupport g ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (fun s : ℝ => ‖g s‖ / Real.sqrt s) (Ioi 0) := by
  let a (s : ℝ) := ‖g s‖ / Real.sqrt s
  have ha : Continuous a := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : 0 < s
    · exact hg.norm.continuousAt.div Real.continuous_sqrt.continuousAt (Real.sqrt_pos_of_pos hs).ne'
    · have hnot : s ∉ tsupport g := fun h => hs (mem_Ioi.mp (hpos h))
      have hn := notMem_tsupport_iff_eventuallyEq.mp hnot
      apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) s).congr_of_eventuallyEq
      filter_upwards [hn] with t ht
      change ‖g t‖ / Real.sqrt t = 0
      have ht' : g t = 0 := ht
      rw [ht', norm_zero, zero_div]
  have haC : HasCompactSupport a := hc.mono (by
    intro s hs
    intro hz
    apply hs
    simp only [a, hz, norm_zero, zero_div])
  exact (ha.integrable_of_hasCompactSupport haC).integrableOn

end
end ArtinMatthews
