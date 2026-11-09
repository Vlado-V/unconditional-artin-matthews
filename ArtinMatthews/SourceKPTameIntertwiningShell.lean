module

public import ArtinMatthews.SourceKPTameJacquetShellIntegral
public import ArtinMatthews.SourceKPTameJacquetSignedIntegrability
public import ArtinMatthews.SourceKPExteriorScattering


set_option backward.privateInPublic true
@[expose] public section

/-! The zero-frequency intertwining integral uses the literal spherical
induced vector on the cubic local cover. The variable parameter is
introduced by the positive Iwasawa-height twist of its open-cell value. -/

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

def sourceKPTameIntertwiningWeight (s : ℂ) (x : L) : ℂ :=
  Complex.exp (-(2*s+1/3) * (Real.log (max 1 ‖x‖) : ℂ))

def sourceKPTameIntertwiningIntegrand (s : ℂ) (x : L) : ZMod 3 → ℂ :=
  sourceKPTameIntertwiningWeight K S₀ P s x • sourceKPTameJacquetPoint K hζ S₀ P 0 x

theorem sourceKPTameIntertwiningWeight_continuous (s : ℂ) :
    Continuous (sourceKPTameIntertwiningWeight K S₀ P s) := by
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Complex.continuous_ofReal.comp
  exact (continuous_const.max continuous_norm).log
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)))

theorem sourceKPTameUnitShell_zero_frequency (l : ℕ) :
    (∫ x in shell₀ 0, sourceJacquetWeight K P.val (sourceJacquetShellCharacter K P.val χ₀ l) x ∂μ₀) =
      if 3 ∣ l then 1 - (Q₀ : ℂ)⁻¹ else 0 := by
  have h := sourceJacquetShellIntegral_eq_unit_shell K P.val
    (sourceJacquetShellCharacter K P.val χ₀ l) 0
  simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one] at h
  rw [h, sourceJacquetShellIntegral_of_integral_frequency K P.val _ 0
    ((P.val.adicCompletionIntegers K).zero_mem),
    sourceJacquetShellCharacter_sum K P.val χ₀ (sourceJacquetActualCharacter_order K hζ S₀ P)]
  split_ifs
  · simp only [Complex.ofReal_natCast]
    rw [sub_div, div_self (Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr P.val.ne_bot)), one_div]
  · simp

theorem sourceKPTameIntertwiningWeight_integral (s : ℂ) (x : L) (hx : x ∈ sourceLocalBall K P.val 0) :
    sourceKPTameIntertwiningWeight K S₀ P s x = 1 := by
  have hnorm : ‖x‖ ≤ 1 := by
    change ν₀ x ≤ WithZero.exp (0 : ℤ) at hx
    rw [WithZero.exp_zero] at hx
    exact Valued.toNormedField.norm_le_one_iff.mpr hx
  rw [sourceKPTameIntertwiningWeight, max_eq_left hnorm, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero]

theorem sourceKPTameIntertwiningWeight_shell (s : ℂ) (l : ℕ) (x : L) (hx : x ∈ shell₀ l) :
    sourceKPTameIntertwiningWeight K S₀ P s x =
      Complex.exp (-(2*s+1/3) * (l : ℂ) * (Real.log Q₀ : ℂ)) := by
  have hv := (sourceJacquetValuationShell_mem K P.val (l : ℤ) x).mp hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hQ : 1 < Q₀ := probeIdealPrime_norm_gt_one K P.val
  have hn : ‖x‖ = Q₀ ^ (l : ℤ) := by
    rw [sourceLocalNorm_eq_zpow K P.val x hx0, hv, WithZero.log_exp]
  have hn' : ‖x‖ = Q₀ ^ l := by simpa using hn
  have hge : 1 ≤ ‖x‖ := by rw [hn']; exact one_le_pow₀ hQ.le
  rw [sourceKPTameIntertwiningWeight, max_eq_right hge, hn', Real.log_pow, Complex.ofReal_mul]
  push_cast
  congr 1
  ring

end
end ArtinMatthews
