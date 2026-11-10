module

public import ArtinMatthews.SourceKPTameIntertwiningShell
public import ArtinMatthews.SourceJacquetHaarDilation
public import ArtinMatthews.SourceKPCommRingDiagonal
public import ArtinMatthews.SourceKPProjectiveBruhatCells
public import ArtinMatthews.SourceKPTameJacquetShellPoint
public import ArtinMatthews.StandardLocalBall
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact zero-frequency shell integrals of the cubic spherical induced
vector, including the parameter twist and the normalized Haar factor. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical StandardAdelic
open QuadraticWeil VaryingKummerAnalytic
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceLocalValuation K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "shell₀" => sourceJacquetValuationShell K P.val
local notation "μ₀" => sourceJacquetHaar K P.val

theorem sourceKPTameIntertwiningIntegrand_on_zero (s : ℂ) (x : L)
    (hx : x ∈ sourceLocalBall K P.val 0) :
    sourceKPTameIntertwiningIntegrand K hζ S₀ P s x = sourceJacquetBasis 0 := by
  rw [sourceKPTameIntertwiningIntegrand, sourceKPTameIntertwiningWeight_integral K S₀ P s x hx, one_smul]
  have hv : ν₀ x ≤ 1 := by
    change ν₀ x ≤ WithZero.exp (0 : ℤ) at hx
    rwa [WithZero.exp_zero] at hx
  have hd : sourceGL2Diagonal (1 : Lˣ) = 1 := by
    rw [← sourceKPDiagonalHom_field]
    exact map_one _
  simpa only [sourceKPTameJacquetPoint, zpow_zero, hd,
    sourceFiniteKP2ProjectiveLift_one, mul_one] using
    sourceKPTameExteriorSpherical_weyl_upper_integral K hζ S₀ P x hv

theorem sourceKPTameIntertwiningIntegrand_on_shell_image (s : ℂ) (l : ℕ) (u : L)
    (hu : u ∈ shell₀ 0) :
    sourceKPTameIntertwiningIntegrand K hζ S₀ P s
      (((π₀ ^ (-(l : ℤ)) : Lˣ) : L) * u) =
      (Complex.exp (-(2*s+1) * (l : ℂ) * (Real.log Q₀ : ℂ)) *
        sourceJacquetWeight K P.val (sourceJacquetShellCharacter K P.val χ₀ l) u) •
        sourceJacquetBasis ((2 * (l : ℤ) : ℤ) : ZMod 3) := by
  let t := π₀ ^ (-(l : ℤ))
  have hν : ν₀ u = 1 := by
    simpa only [WithZero.exp_zero] using (sourceJacquetValuationShell_mem K P.val 0 u).mp hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hν
    exact zero_ne_one hν
  let v := Units.mk0 u hu0
  have ht : ν₀ (t : L) = WithZero.exp (l : ℤ) := by
    dsimp only [t]
    rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀, neg_neg]
  have hx : (t : L) * u ∈ shell₀ l := by
    have hImage := sourceJacquetValuationShell_mul_image K P.val 0 (l : ℤ) t ht
    rw [zero_add] at hImage
    rw [← hImage]
    exact ⟨u, hu, rfl⟩
  have hp := sourceKPTameJacquetPoint_scaled_shell K hζ S₀ P 0 l v hν
  simp only [Int.cast_zero, zpow_zero, one_mul, zero_sub, sub_zero] at hp
  change sourceKPTameJacquetPoint K hζ S₀ P 0 ((π₀ : L) ^ (-(l : ℤ)) * u) = _ at hp
  rw [sourceKPTameIntertwiningIntegrand, sourceKPTameIntertwiningWeight_shell K S₀ P s l _ hx,
    Units.val_zpow_eq_zpow_val, hp, smul_smul]
  congr 1
  rw [sourceJacquetScale, Real.rpow_def_of_pos (sourceJacquetPrimeNorm_pos K S₀ P),
    Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  push_cast
  congr 2
  ring

theorem sourceKPTameIntertwiningIntegral_shell (hP : P.val ∉ traceBadPlaces K) (s : ℂ) (l : ℕ) :
    IntegrableOn (sourceKPTameIntertwiningIntegrand K hζ S₀ P s) (shell₀ l) μ₀ ∧
      (∫ x in shell₀ l, sourceKPTameIntertwiningIntegrand K hζ S₀ P s x ∂μ₀) =
        if 3 ∣ l then
          ((1-(Q₀ : ℂ)⁻¹) * Complex.exp (-2*s*(l : ℂ)*(Real.log Q₀ : ℂ))) • sourceJacquetBasis 0
        else 0 := by
  let t := π₀ ^ (-(l : ℤ))
  let f := sourceKPTameIntertwiningIntegrand K hζ S₀ P s
  let A := sourceJacquetWeight K P.val (sourceJacquetShellCharacter K P.val χ₀ l)
  let z := Complex.exp (-(2*s+1) * (l : ℂ) * (Real.log Q₀ : ℂ))
  let b := sourceJacquetBasis ((2 * (l : ℤ) : ℤ) : ZMod 3)
  let : Measure.IsAddHaarMeasure μ₀ := sourceJacquetHaar_isAddHaar K P.val
  have ht : ν₀ (t : L) = WithZero.exp (l : ℤ) := by
    dsimp only [t]
    rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀, neg_neg]
  have hImage := sourceJacquetValuationShell_mul_image K P.val 0 (l : ℤ) t ht
  rw [zero_add] at hImage
  have hpt : Set.EqOn (fun u => f ((t : L) * u)) (fun u => (z * A u) • b) (shell₀ 0) :=
    fun u hu => sourceKPTameIntertwiningIntegrand_on_shell_image K hζ S₀ P s l u hu
  let g : L → ZMod 3 → ℂ := fun x => (z * A ((t : L)⁻¹ * x)) • b
  have hg : Continuous g := (continuous_const.mul
    ((sourceJacquetWeight_locallyConstant K P.val _).continuous.comp
      (continuous_const.mul continuous_id))).smul continuous_const
  have he : Set.EqOn g f (shell₀ (l : ℤ)) := by
    intro x hx
    rw [← hImage] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    change (z * A ((t : L)⁻¹ * ((t : L) * u))) • b = f ((t : L) * u)
    rw [← mul_assoc, inv_mul_cancel₀ t.ne_zero, one_mul]
    exact (hpt hu).symm
  have hShell := sourceJacquetValuationShell_isCompact K P.val (l : ℤ)
  refine ⟨(hg.continuousOn.integrableOn_compact (μ := μ₀) hShell).congr_fun he hShell.measurableSet, ?_⟩
  change (∫ x in shell₀ (l : ℤ), f x ∂μ₀) = _
  rw [← hImage, sourceJacquetSetIntegral_dilation K P.val hP t _ f,
    setIntegral_congr_fun (sourceJacquetValuationShell_isCompact K P.val 0).measurableSet hpt,
    integral_smul_const, integral_const_mul, sourceKPTameUnitShell_zero_frequency K hζ S₀ P l]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change (‖(t : L)‖ : ℂ) • ((z * (if 3 ∣ l then 1-(Q₀ : ℂ)⁻¹ else 0)) • b) = _
  rw [sourceJacquetDilation_norm K P.val (l : ℤ) t ht, smul_smul]
  by_cases hl : 3 ∣ l
  · simp only [ite_eq_left hl]
    have hb : b = sourceJacquetBasis 0 := by
      dsimp only [b]
      congr 1
      rw [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, (ZMod.natCast_eq_zero_iff _ _).mpr hl, mul_zero]
    rw [hb]
    congr 1
    dsimp only [z]
    rw [sourceJacquetScale, Real.rpow_def_of_pos (sourceJacquetPrimeNorm_pos K S₀ P), Complex.ofReal_exp]
    simp only [Int.cast_natCast]
    calc
      _ = (1-(Q₀ : ℂ)⁻¹) *
          (Complex.exp ((Real.log Q₀ * (l : ℝ) : ℝ) : ℂ) *
            Complex.exp (-(2*s+1) * (l : ℂ) * (Real.log Q₀ : ℂ))) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        push_cast
        congr 2
        ring
  · simp only [ite_eq_right hl, mul_zero, zero_smul]

def sourceKPTameIntertwiningTruncation (s : ℂ) (N : ℕ) : ZMod 3 → ℂ :=
  ∫ x in sourceLocalBall K P.val (N : ℤ), sourceKPTameIntertwiningIntegrand K hζ S₀ P s x ∂μ₀

theorem sourceKPTameIntertwiningTruncation_formula (hP : P.val ∉ traceBadPlaces K) (s : ℂ) (N : ℕ) :
    sourceKPTameIntertwiningTruncation K hζ S₀ P s N =
      sourceJacquetBasis 0 +
        ∑ l ∈ Finset.Icc 1 N, if 3 ∣ l then
          ((1-(Q₀ : ℂ)⁻¹) * Complex.exp (-2*s*(l : ℂ)*(Real.log Q₀ : ℂ))) • sourceJacquetBasis 0
        else 0 := by
  let f := sourceKPTameIntertwiningIntegrand K hζ S₀ P s
  have hzero : IntegrableOn f (sourceLocalBall K P.val 0) μ₀ := by
    let : Measure.IsAddHaarMeasure μ₀ := sourceJacquetHaar_isAddHaar K P.val
    exact ((continuous_const : Continuous (fun _ : L => sourceJacquetBasis (0 : ZMod 3))).continuousOn.integrableOn_compact
      (μ := μ₀) (sourceLocalBall_isCompact K P.val 0)).congr_fun
        (fun x hx => (sourceKPTameIntertwiningIntegrand_on_zero K hζ S₀ P s x hx).symm)
        (sourceLocalBall_isCompact K P.val 0).measurableSet
  have hball := sourceJacquetBall_integral_shells K P.val f hzero
    (fun l _ => (sourceKPTameIntertwiningIntegral_shell K hζ S₀ P hP s l).1) N
  change (∫ x in sourceLocalBall K P.val (N : ℤ), f x ∂μ₀) = _
  rw [hball.2]
  have hinit : (∫ x in sourceLocalBall K P.val 0, f x ∂μ₀) = sourceJacquetBasis 0 := by
    rw [setIntegral_congr_fun (sourceLocalBall_isCompact K P.val 0).measurableSet
      (sourceKPTameIntertwiningIntegrand_on_zero K hζ S₀ P s), integral_const,
      sourceLocalBall_zero_eq_integerOpen, Measure.real, Measure.restrict_apply_univ, sourceJacquetHaar_integers,
      ENNReal.toReal_one, one_smul]
  rw [hinit]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact (sourceKPTameIntertwiningIntegral_shell K hζ S₀ P hP s l).2

end
end ArtinMatthews
