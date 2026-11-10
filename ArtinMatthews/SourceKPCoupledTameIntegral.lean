module

public import ArtinMatthews.SourceJacquetBallShells
public import ArtinMatthews.SourceKPCoupledTameRest
public import ArtinMatthews.SourceKPExteriorScattering
public import ArtinMatthews.StandardLocalFourier
public import ArtinMatthews.ProbeIdealSourceRegions
public import ArtinMatthews.SourceKPCoupledTameAbsolute
public import ArtinMatthews.SourceKPCoupledTameShellAverage
public import ArtinMatthews.SourceKPCoupledTameShellMeasure
public import ArtinMatthews.SourceKPIntertwiningSeries
public import ArtinMatthews.SourceLocalHaarGeneralDilation
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
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact all-tame scattering in the actual coupled kernel. The
self-dual integral retains its local integer-ball normalization. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical
open scoped NumberField AdeleRing BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ)

local notation "L" => P.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P
local notation "μ₀" => sourceJacquetHaar K P
local notation "B₀" => sourceLocalBall K P
local notation "shell₀" => sourceJacquetValuationShell K P
local notation "Q₀" => (Ideal.absNorm P.asIdeal : ℝ)

theorem sourceKPCoupledScattering_exp : sourceKPUnramifiedScatteringFactor P s =
    (1-(Q₀ : ℂ)⁻¹ * Complex.exp (-6*s*(Real.log Q₀ : ℂ))) /
      (1-Complex.exp (-6*s*(Real.log Q₀ : ℂ))) := by
  have hQ : 0 < Q₀ := sourceLocalNorm_pos K P
  have hQ₀ : (Q₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have h₁ : (Q₀ : ℂ)^(-(6*s)) = Complex.exp (-6*s*(Real.log Q₀ : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hQ₀, ← Complex.ofReal_log hQ.le]
    congr 1
    ring
  have h₂ : (Q₀ : ℂ)^(-(6*s+1)) = (Q₀ : ℂ)⁻¹ * (Q₀ : ℂ)^(-(6*s)) := by
    rw [show -(6*s+1) = -(1 : ℂ) + -(6*s) by ring, Complex.cpow_add _ _ hQ₀, Complex.cpow_neg_one]
  unfold sourceKPUnramifiedScatteringFactor
  rw [← Complex.ofReal_natCast, h₂, h₁]

theorem sourceKPCoupledTameKernel_unit_ball (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1) :
    (∫ x in B₀ 0, sourceKPCoupledTameRestKernel K hζ P s r x ∂μ₀) = sourceKPAdelicCompactScalar K hζ s r := by
  have he : ∀ x ∈ B₀ 0, sourceKPCoupledTameRestKernel K hζ P s r x = sourceKPAdelicCompactScalar K hζ s r := by
    intro x hx
    have hx' : ν₀ x ≤ 1 := by simpa only [sourceLocalBall, Set.mem_setOf_eq, WithZero.exp_zero] using hx
    exact congrArg (fun v : SourceKPAdelicTorusInducedSpace K hζ s => v.val 1)
      (sourceKPCoupledTameRest_value_integral_input K hζ P s h6 r hr x hx')
  rw [setIntegral_congr_fun (sourceLocalBall_isCompact K P 0).measurableSet he, integral_const,
    Measure.real, Measure.restrict_apply_univ,
    ← Measure.real, sourceKPCoupledJacquetBall_mass K P, one_smul]

theorem sourceKPCoupledTameKernel_shell_model (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1) (l : ℕ) :
    (∫ x in shell₀ (l : ℤ), sourceKPCoupledTameRestKernel K hζ P s r x ∂μ₀) =
      if 3 ∣ l then (1-(Q₀ : ℂ)⁻¹) * Complex.exp (-2*s*(l : ℂ)*(Real.log Q₀ : ℂ)) *
        sourceKPAdelicCompactScalar K hζ s r else 0 := by
  rw [sourceKPCoupledTameKernel_shell_integral K hζ P s h6 r hr l, sourceKPCoupledJacquetShell_mass K P l]
  by_cases h : 3 ∣ l
  · rw [ite_eq_left h, ite_eq_left h]
    have hp : ((Q₀^l : ℝ) : ℂ) = Complex.exp ((Real.log Q₀*(l : ℝ) : ℝ) : ℂ) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (sourceLocalNorm_pos K P), Complex.ofReal_exp]
    rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv, hp]
    calc
      _ = (1-(Q₀ : ℂ)⁻¹) *
          (Complex.exp ((Real.log Q₀*(l : ℝ) : ℝ) : ℂ) *
            Complex.exp (-(s+1/2)*((2*(l : ℤ) : ℤ) : ℂ)*(Real.log Q₀ : ℂ))) *
          sourceKPAdelicCompactScalar K hζ s r := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        push_cast
        congr 2
        ring
  · simp only [ite_eq_right h]

theorem sourceKPCoupledTameKernel_truncation_three (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1) (N : ℕ) :
    (∫ x in B₀ ((3*N : ℕ) : ℤ), sourceKPCoupledTameRestKernel K hζ P s r x ∂μ₀) =
      (1+(1-(Q₀ : ℂ)⁻¹)*∑ k ∈ Finset.range N, (Complex.exp (-6*s*(Real.log Q₀ : ℂ)))^(k+1)) *
        sourceKPAdelicCompactScalar K hζ s r := by
  let f := sourceKPCoupledTameRestKernel K hζ P s r
  let v := sourceKPAdelicCompactScalar K hζ s r
  let b := Complex.exp (-6*s*(Real.log Q₀ : ℂ))
  let : (μ₀).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  have hc : Continuous f := sourceKPCoupledTameRestKernel_continuous K hζ P s r
  have hball := (sourceJacquetBall_integral_shells K P f
    (hc.continuousOn.integrableOn_compact (μ := μ₀) (sourceLocalBall_isCompact K P 0))
    (fun l _ => hc.continuousOn.integrableOn_compact (μ := μ₀)
      (sourceJacquetValuationShell_isCompact K P (l : ℤ))) (3*N)).2
  change (∫ x in B₀ ((3*N : ℕ) : ℤ), f x ∂μ₀) = (1+(1-(Q₀ : ℂ)⁻¹)*∑ k ∈ Finset.range N, b^(k+1))*v
  rw [hball]
  simp_rw [f, sourceKPCoupledTameKernel_unit_ball K hζ P s h6 r hr,
    sourceKPCoupledTameKernel_shell_model K hζ P s h6 r hr]
  rw [add_mul, one_mul]
  congr 1
  rw [← sourceKPDivisibleThreeSum b N, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : 3 ∣ l
  · rw [ite_eq_left hl, ite_eq_left hl]
    obtain ⟨k, hk⟩ := hl
    rw [hk, show 3*k/3 = k by omega]
    dsimp only [b]
    rw [← Complex.exp_nat_mul]
    push_cast
    congr 2
    ring
  · simp only [ite_eq_right hl, mul_zero, zero_mul]

theorem sourceKPCoupledTameKernel_integral (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1) (hs : 0 < s.re) :
    (∫ x, sourceKPCoupledTameRestKernel K hζ P s r x ∂μ₀) =
      sourceKPUnramifiedScatteringFactor P s * sourceKPAdelicCompactScalar K hζ s r := by
  let f := sourceKPCoupledTameRestKernel K hζ P s r
  let a := fun N : ℕ => B₀ ((3*N : ℕ) : ℤ)
  have hcover : (⋃ N : ℕ, a N) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : ν₀ x = 0
    · exact Set.mem_iUnion.mpr ⟨0, by change ν₀ x ≤ _; rw [hx]; exact zero_le⟩
    · let m := WithZero.log (ν₀ x)
      have hm : ν₀ x = WithZero.exp m := (WithZero.exp_log hx).symm
      refine Set.mem_iUnion.mpr ⟨m.toNat, ?_⟩
      change ν₀ x ≤ WithZero.exp ((3*m.toNat : ℕ) : ℤ)
      rw [hm, WithZero.exp_le_exp]
      have hle := Int.self_le_toNat m
      omega
  have hm : Monotone a := by
    intro i j hij x hx
    exact (show ν₀ x ≤ WithZero.exp ((3*i : ℕ) : ℤ) from hx).trans
      (WithZero.exp_le_exp.mpr (by exact_mod_cast Nat.mul_le_mul_left 3 hij))
  have hi : IntegrableOn f (⋃ N : ℕ, a N) μ₀ := by
    rw [hcover, integrableOn_univ]
    exact sourceKPCoupledTameKernel_integrable K hζ P s h6 r hr hs
  have h := tendsto_setIntegral_of_monotone
    (fun N => (sourceLocalBall_isCompact K P ((3*N : ℕ) : ℤ)).measurableSet) hm hi
  rw [hcover, setIntegral_univ] at h
  change Filter.Tendsto (fun N => ∫ x in B₀ ((3*N : ℕ) : ℤ), f x ∂μ₀) Filter.atTop _ at h
  simp_rw [f, sourceKPCoupledTameKernel_truncation_three K hζ P s h6 r hr] at h
  rw [sourceKPCoupledScattering_exp K P s]
  exact tendsto_nhds_unique h ((sourceKPIntertwiningGeometric_limit
    (VaryingKummerAnalytic.probeIdealPrime_norm_gt_one K P) hs).mul_const _)

theorem sourceKPCoupledTameKernel_full_eq_factor_unit (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1) (hs : 0 < s.re) :
    (∫ x, sourceKPCoupledTameRestKernel K hζ P s r x ∂μ₀) =
      sourceKPUnramifiedScatteringFactor P s * ∫ x in B₀ 0, sourceKPCoupledTameRestKernel K hζ P s r x ∂μ₀ := by
  rw [sourceKPCoupledTameKernel_integral K hζ P s h6 r hr hs, sourceKPCoupledTameKernel_unit_ball K hζ P s h6 r hr]

theorem sourceKPCoupledTameKernel_selfDual_integral (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1) (hs : 0 < s.re) :
    (∫ x, sourceKPCoupledTameRestKernel K hζ P s r x ∂sourceLocalSelfDual K P) =
      ((sourceLocalSelfDual K P).real (B₀ 0) : ℂ) *
        (sourceKPUnramifiedScatteringFactor P s * sourceKPAdelicCompactScalar K hζ s r) := by
  let f := sourceKPCoupledTameRestKernel K hζ P s r
  calc
    _ = ∫ x, f x ∂((sourceLocalSelfDual K P) (B₀ 0) • μ₀) :=
      congrArg (fun μ => ∫ x, f x ∂μ) (sourceLocalSelfDual_eq_integer_mass_smul_jacquet K P)
    _ = _ := by rw [integral_smul_measure, sourceKPCoupledTameKernel_integral K hζ P s h6 r hr hs]; rfl

end
end ArtinMatthews
