module

public import ArtinMatthews.SourceJacquetBallShells
public import ArtinMatthews.SourceKPCoupledTameRest
public import ArtinMatthews.SourceKPLocalUniformizerAction
public import ArtinMatthews.StandardLocalHaarScaling
public import ArtinMatthews.ProbeIdealSourceRegions
public import ArtinMatthews.SourceKPCoupledTameShellMeasure
public import ArtinMatthews.SourceKPCoupledTameShellValue
public import ArtinMatthews.SourceKPCoupledUniformizerPhase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute local convergence of the actual coupled tame kernel in
Re(s)>0. The remaining global vector is controlled on its true cubic orbit. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical
open scoped NumberField AdeleRing BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ)

local notation "L" => P.adicCompletion K
local notation "π₀" => sourceLocalPrimeUnit K P
local notation "ν₀" => sourceKPFiniteVal K P
local notation "χ₀" => sourceKPTameUniformizerCharacter K hζ P π₀
local notation "A₀" => sourceKPLocalUniformizerCycle K hζ P π₀ s
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ s
local notation "F₀" => sourceKPAdelicCompactSection K hζ s
local notation "μ₀" => sourceJacquetHaar K P
local notation "B₀" => sourceLocalBall K P
local notation "shell₀" => sourceJacquetValuationShell K P
local notation "Q₀" => (Ideal.absNorm P.asIdeal : ℝ)

theorem sourceKPCoupledTameCharacter_norm (u : Lˣ) : ‖(χ₀ u : ℂ)‖ = 1 := by
  have h := congrArg (fun z : ℂˣ => (z : ℂ)) (sourceKPTameUniformizerCharacter_cube K hζ P π₀ u)
  have hp : (χ₀ u : ℂ)^3 = 1 := by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  exact Complex.norm_eq_one_of_pow_eq_one hp (by decide)

def sourceKPCoupledTameOrbitNorm (r : SourceKPAdelicProjective K hζ) : ℝ :=
  ∑ i : ZMod 3, ‖((sourceKPCubicPower A₀ i).val ((F₀).val r)).val 1‖

theorem sourceKPCoupledTameOrbitNorm_nonneg (r : SourceKPAdelicProjective K hζ) :
    0 ≤ sourceKPCoupledTameOrbitNorm K hζ P s r := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem sourceKPCoupledTameKernel_shell_norm_le (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1)
    (l : ℕ) (x : L) (hx : x ∈ shell₀ (l : ℤ)) :
    ‖sourceKPCoupledTameRestKernel K hζ P s r x‖ ≤
      Real.exp (-(2*s.re+1)*(l : ℝ)*Real.log Q₀) * sourceKPCoupledTameOrbitNorm K hζ P s r := by
  obtain ⟨u, hu, rfl⟩ := sourceKPCoupledTameShell_unit_coordinates K P l x hx
  let j : ℤ := 2*(l : ℤ)
  have hA := sourceKPLocalUniformizerCycle_cube K hζ P π₀ (sourceKPCoupledUniformizer_valuation K P) s
  have hterm : ‖((A₀^j).val ((F₀).val r)).val 1‖ ≤ sourceKPCoupledTameOrbitNorm K hζ P s r := by
    rw [← sourceKPCubicPower_int A₀ hA j]
    let f : ZMod 3 → ℝ := fun i => ‖((sourceKPCubicPower A₀ i).val ((F₀).val r)).val 1‖
    change f (j : ZMod 3) ≤ ∑ i : ZMod 3, f i
    exact Finset.single_le_sum (f := f) (fun i _ => norm_nonneg _) (Finset.mem_univ (j : ZMod 3))
  have he : -(s+1/2)*(j : ℂ)*(Real.log Q₀ : ℂ) = -(2*s+1)*(l : ℂ)*(Real.log Q₀ : ℂ) := by
    dsimp only [j]
    push_cast
    ring
  have hRe : (-(2*s+1)*(l : ℂ)*(Real.log Q₀ : ℂ)).re = -(2*s.re+1)*(l : ℝ)*Real.log Q₀ := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.one_re, mul_zero, zero_mul, sub_zero]
  unfold sourceKPCoupledTameRestKernel
  rw [sourceKPCoupledTameShell_value K hζ P s h6 r hr l u hu]
  change ‖((((χ₀ u)^(4*(l : ℤ)) : ℂˣ) : ℂ) * Complex.exp (-(s+1/2)*(j : ℂ)*
      (Real.log Q₀ : ℂ))) * ((A₀^j).val ((F₀).val r)).val 1‖ ≤ _
  rw [norm_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow, sourceKPCoupledTameCharacter_norm,
    one_zpow, one_mul, he, Complex.norm_exp, hRe]
  exact mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le

theorem sourceKPCoupledTameKernel_shell_norm_integral_le (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1) (l : ℕ) :
    (∫ x in shell₀ (l : ℤ), ‖sourceKPCoupledTameRestKernel K hζ P s r x‖ ∂μ₀) ≤
      sourceKPCoupledTameOrbitNorm K hζ P s r * (Real.exp (-2*s.re*Real.log Q₀))^l := by
  let f := sourceKPCoupledTameRestKernel K hζ P s r
  let M := sourceKPCoupledTameOrbitNorm K hζ P s r
  let : (μ₀).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  have hnorm := norm_setIntegral_le_of_norm_le_const (μ := μ₀) (f := fun x => ‖f x‖)
    (sourceJacquetValuationShell_isCompact K P (l : ℤ)).measure_lt_top (fun x hx => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact sourceKPCoupledTameKernel_shell_norm_le K hζ P s h6 r hr l x hx)
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hnorm
  have hvol : (μ₀).real (shell₀ (l : ℤ)) ≤ Q₀^l := by
    calc
      _ ≤ (μ₀).real (B₀ (l : ℤ)) := measureReal_mono (fun _ hx => hx.1)
        (sourceLocalBall_isCompact K P _).measure_ne_top
      _ = _ := by rw [sourceLocalBall_volume_scaling K P μ₀, sourceKPCoupledJacquetBall_mass K P,
        mul_one, zpow_natCast]
  calc
    _ ≤ Real.exp (-(2*s.re+1)*(l : ℝ)*Real.log Q₀) * M * (μ₀).real (shell₀ (l : ℤ)) := hnorm
    _ ≤ Real.exp (-(2*s.re+1)*(l : ℝ)*Real.log Q₀) * M * Q₀^l :=
      mul_le_mul_of_nonneg_left hvol (mul_nonneg (Real.exp_pos _).le
        (sourceKPCoupledTameOrbitNorm_nonneg K hζ P s r))
    _ = M * (Real.exp (-(2*s.re+1)*(l : ℝ)*Real.log Q₀) * Real.exp (Real.log Q₀*(l : ℝ))) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (sourceLocalNorm_pos K P)]
      ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 2
      ring

theorem sourceKPCoupledTameShells_cover : B₀ 0 ∪ (⋃ l : ℕ, shell₀ (l : ℤ)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : ν₀ x = 0
  · left
    change ν₀ x ≤ WithZero.exp (0 : ℤ)
    rw [hx]
    exact zero_le
  · let m := WithZero.log (ν₀ x)
    have he : ν₀ x = WithZero.exp m := (WithZero.exp_log hx).symm
    by_cases hm : m ≤ 0
    · left
      change ν₀ x ≤ WithZero.exp (0 : ℤ)
      rw [he]
      exact WithZero.exp_le_exp.mpr hm
    · right
      apply Set.mem_iUnion.mpr
      refine ⟨m.toNat, ?_⟩
      rw [sourceJacquetValuationShell_mem, Int.toNat_of_nonneg (by omega : 0 ≤ m)]
      exact he

theorem sourceKPCoupledTameKernel_integrable (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P r = 1) (hs : 0 < s.re) :
    Integrable (sourceKPCoupledTameRestKernel K hζ P s r) μ₀ := by
  let f := sourceKPCoupledTameRestKernel K hζ P s r
  let : (μ₀).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  have hcont : Continuous f := sourceKPCoupledTameRestKernel_continuous K hζ P s r
  have hlog : 0 < Real.log Q₀ := Real.log_pos (VaryingKummerAnalytic.probeIdealPrime_norm_gt_one K P)
  have hq : Real.exp (-2*s.re*Real.log Q₀) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos hs hlog]
  have hsummable : Summable (fun l : ℕ => ∫ x in shell₀ (l : ℤ), ‖f x‖ ∂μ₀) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
      ((summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left (sourceKPCoupledTameOrbitNorm K hζ P s r))
    exact sourceKPCoupledTameKernel_shell_norm_integral_le K hζ P s h6 r hr
  have hzero := hcont.continuousOn.integrableOn_compact (μ := μ₀) (sourceLocalBall_isCompact K P 0)
  have hshell : IntegrableOn f (⋃ l : ℕ, shell₀ (l : ℤ)) μ₀ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun l => hcont.continuousOn.integrableOn_compact (μ := μ₀)
        (sourceJacquetValuationShell_isCompact K P (l : ℤ))) hsummable
  have h := hzero.union hshell
  rwa [sourceKPCoupledTameShells_cover K P, integrableOn_univ] at h

end
end ArtinMatthews
