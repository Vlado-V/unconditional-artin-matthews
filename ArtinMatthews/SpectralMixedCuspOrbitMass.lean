module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralGamma0Core
public import ArtinMatthews.SpectralInfinityPoincareOrbitBound
public import ArtinMatthews.SpectralCuspOrbitSupportCount
public import ArtinMatthews.SpectralGamma0EnergyGraph
public import ArtinMatthews.SpectralModularDensityPeriodization
public import ArtinMatthews.SpectralPoincareUnfolding
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

/-! Orbit and completed mass bounds at the actual source cusp 1/s,
keeping its width and the overlap at normalized height. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups CompactlySupported BigOperators
namespace ArtinMatthews

private theorem gamma0PoincareSeed_normsq_le_of_orbit_card
    (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane, ℂ)) (z : UpperHalfPlane) (C : ℝ)
    (hcard : ∀ t : Finset (CongruenceSubgroup.Gamma0 N),
      (∀ γ ∈ t, ψ (γ.val • z) ≠ 0) → (t.card : ℝ) ≤ C) :
    ‖gamma0PoincareSeed N ψ z‖^2 ≤ C*(gamma0PoincareSeed N (spectralCompactSeedNormSq ψ) z).re := by
  classical
  let f (γ : CongruenceSubgroup.Gamma0 N) := ψ (γ.val • z)
  let g (γ : CongruenceSubgroup.Gamma0 N) := spectralCompactSeedNormSq ψ (γ.val • z)
  have hf : Function.HasFiniteSupport f := gamma0PoincareSeed_integral_point_finite N ψ z
  let t := hf.toFinset
  have hg : Function.support g ⊆ t := by
    intro γ hγ
    apply hf.mem_toFinset.mpr
    intro hz
    exact hγ (by
      change spectralCompactSeedNormSq ψ (γ.val • z) = 0
      change ψ (γ.val • z) = 0 at hz
      rw [spectralCompactSeedNormSq_apply,hz,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),
        Complex.ofReal_zero])
  have hEq : gamma0PoincareSeed N ψ z = ∑ γ ∈ t, f γ := by
    rw [gamma0PoincareSeed_eq_finsum]
    exact finsum_eq_sum_of_support_subset f (fun _ h => hf.mem_toFinset.mpr h)
  have hEq₂ : (gamma0PoincareSeed N (spectralCompactSeedNormSq ψ) z).re =
      ∑ γ ∈ t, ‖f γ‖^2 := by
    rw [gamma0PoincareSeed_eq_finsum]
    change (∑ᶠ γ, g γ).re = _
    rw [finsum_eq_sum_of_support_subset g hg]
    simp only [g,spectralCompactSeedNormSq_apply,← Complex.ofReal_sum,Complex.ofReal_re,f]
  have hc := hcard t (fun γ hγ => hf.mem_toFinset.mp hγ)
  rw [hEq,hEq₂]
  calc
    _ ≤ (∑ γ ∈ t, ‖f γ‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (t.card : ℝ)*(∑ γ ∈ t, ‖f γ‖^2) := by
      simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
        Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) (fun γ => ‖f γ‖)
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem gamma0MixedCusp_poincare_orbit_normsq_le (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (ψ : C_c(UpperHalfPlane, ℂ)) {A : ℝ} (hA : 0 < A)
    (hSupp : ∀ z : UpperHalfPlane, ψ z ≠ 0 →
      ((gamma0CuspOneOver s) • z).re ∈ Icc 0 (2*((r*s : ℕ) : ℝ)) ∧
      (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)*A ≤ ((gamma0CuspOneOver s) • z).im)
    (z : UpperHalfPlane) :
    ‖gamma0PoincareSeed (r*s) ψ z‖^2 ≤
      ((2*(gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) : ℝ)+1)*
        (4*(1+2/(((r*s : ℕ) : ℝ)*A))))*
      (gamma0PoincareSeed (r*s) (spectralCompactSeedNormSq ψ) z).re := by
  apply gamma0PoincareSeed_normsq_le_of_orbit_card
  intro t ht
  let a := gamma0CuspOneOver s
  have hw : 0 < (gamma0CuspTrueWidth (r*s) a : ℝ) :=
    Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos (r*s) a)
  have h := gamma0_cusp_orbit_support_card_le (r*s) a z (mul_pos hw hA) t
    (fun γ hγ => by
      rw [mul_smul]
      exact hSupp (γ.val • z) (ht γ hγ))
  exact h.trans (mul_le_mul_of_nonneg_left (gamma0MixedCusp_heightRows_card_le r s hcop z hA)
    (by positivity))

theorem gamma0MixedCusp_compact_seed_orbit_mass_bound (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (ψ : h2SmoothCompactSeeds) {A : ℝ} (hA : 0 < A)
    (hSupp : ∀ z : UpperHalfPlane, ψ.val z ≠ 0 →
      ((gamma0CuspOneOver s) • z).re ∈ Icc 0 (2*((r*s : ℕ) : ℝ)) ∧
      (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)*A ≤ ((gamma0CuspOneOver s) • z).im) :
    ‖gamma0SmoothSeedMass (r*s) ψ‖^2 ≤
      2*((2*(gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) : ℝ)+1)*
        (4*(1+2/(((r*s : ℕ) : ℝ)*A))))*(∫ z : UpperHalfPlane, ‖ψ.val z‖^2) := by
  let N := r*s
  let a := gamma0CuspOneOver s
  let C := (2*(gamma0CuspFrequencyStep N a : ℝ)+1)*(4*(1+2/((N : ℝ)*A)))
  let φ := spectralCompactSeedNormSq ψ.val
  let Q := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N
  let H (f : C_c(UpperHalfPlane, ℂ)) (q : Q) (z : UpperHalfPlane) :=
    gamma0PoincareSeed N f (q.out⁻¹ • z)
  have hLp (f : C_c(UpperHalfPlane, ℂ)) (q : Q) :
      MemLp (H f q) 2 (volume.restrict ModularGroup.fd) :=
    arithmeticPoincareSeed_memLp_modularRegion
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) f
      (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹)
  have hI (q : Q) : IntegrableOn (H φ q) ModularGroup.fd :=
    memLp_one_iff_integrable.mp ((hLp φ q).mono_exponent (by norm_num))
  have hI₁ (q : Q) : IntegrableOn (fun z => ‖H ψ.val q z‖^2) ModularGroup.fd :=
    (memLp_two_iff_integrable_sq_norm (hLp ψ.val q).aestronglyMeasurable).mp (hLp ψ.val q)
  have hbound (q : Q) :
      (∫ z in ModularGroup.fd, ‖H ψ.val q z‖^2) ≤
        C*(∫ z in ModularGroup.fd, (H φ q z).re) := by
    rw [← integral_const_mul]
    exact integral_mono (hI₁ q) ((hI q).re.const_mul C)
      (fun z => gamma0MixedCusp_poincare_orbit_normsq_le r s hcop ψ.val hA hSupp (q.out⁻¹ • z))
  have hU :
      (∑ q : Q, ∫ z in ModularGroup.fd, H φ q z) =
        2*∫ z : UpperHalfPlane, φ z := by
    have h := gamma0_periodization_unfold_integral N (fun _ => (1 : ℂ))
      continuous_const (fun _ _ => rfl) φ
    simpa only [one_mul] using h
  have hUre :
      (∑ q : Q, ∫ z in ModularGroup.fd, (H φ q z).re) =
        2*(∫ z : UpperHalfPlane, ‖ψ.val z‖^2) := by
    calc
      _ = (∑ q : Q, ∫ z in ModularGroup.fd, H φ q z).re := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro q _
        exact integral_re (hI q)
      _ = _ := by
        rw [hU]
        simp only [φ,spectralCompactSeedNormSq_apply,integral_complex_ofReal,
          Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,Complex.ofReal_re,zero_mul,sub_zero]
  rw [gamma0SmoothSeedMass_norm_sq]
  change (∑ q : Q, ∫ z in ModularGroup.fd, ‖H ψ.val q z‖^2) ≤
    2*C*(∫ z : UpperHalfPlane, ‖ψ.val z‖^2)
  calc
    _ ≤ ∑ q : Q, C*(∫ z in ModularGroup.fd, (H φ q z).re) :=
      Finset.sum_le_sum (fun q _ => hbound q)
    _ = _ := by rw [← Finset.mul_sum,hUre]; ring

end ArtinMatthews
