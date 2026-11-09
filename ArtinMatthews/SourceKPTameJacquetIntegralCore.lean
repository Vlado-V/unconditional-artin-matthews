module

public import ArtinMatthews.SourceJacquetShellAmplitude
public import ArtinMatthews.SourceKPTameJacquetPoint


set_option backward.privateInPublic true
@[expose] public section

/-! The literal vector Jacquet integrand on the actual spherical
section. On the integral H-ball its transformed value is constant
with the exact modular exponent and the negative valuation index. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceLocalValuation K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "B" => sourceLocalBall K P.val
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)

def sourceKPTameJacquetIntegrand (e : ℤ) (x : L) : ZMod 3 → ℂ :=
  localFiniteCharacter K P.val (-x) • sourceKPTameJacquetPoint K hζ S₀ P e x

def sourceKPTameJacquetScaledIntegrand (e : ℤ) (H : L) : ZMod 3 → ℂ :=
  sourceKPTameJacquetIntegrand K hζ S₀ P e ((π₀ : L) ^ e * H)

theorem sourceKPTameJacquetScaledIntegrand_on_zero_ball (e : ℕ) (H : L) (hH : H ∈ B 0) :
    sourceKPTameJacquetScaledIntegrand K hζ S₀ P e H =
      sourceJacquetScale Q₀ ((e : ℝ) / 3) • sourceJacquetBasis (-(e : ZMod 3)) := by
  have hH₀ : ν₀ H ≤ 1 := by
    change ν₀ H ≤ WithZero.exp (0 : ℤ) at hH
    rwa [WithZero.exp_zero] at hH
  have hπe : ν₀ ((π₀ : L) ^ (e : ℤ)) = WithZero.exp (-(e : ℤ)) :=
    sourceJacquetFrequency_valuation K P.val (π₀ : L) hπ₀ (e : ℤ)
  have hx : -((π₀ : L) ^ (e : ℤ) * H) ∈ P.val.adicCompletionIntegers K := by
    apply (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P.val).mpr
    change ν₀ (-((π₀ : L) ^ (e : ℤ) * H)) ≤ 1
    rw [Valuation.map_neg, map_mul, hπe]
    exact (mul_le_mul' (WithZero.exp_le_one_iff.mpr (by omega)) hH₀).trans_eq (one_mul _)
  rw [sourceKPTameJacquetScaledIntegrand, sourceKPTameJacquetIntegrand, localFiniteCharacter_integral _ _ _ hx,
    one_smul, sourceKPTameJacquetPoint_scaled_integral K hζ S₀ P (e : ℤ) H hH₀]
  have hr : ((e : ℤ) : ℝ) = (e : ℝ) := Int.cast_natCast e
  have hi : ((-(e : ℤ) : ℤ) : ZMod 3) = -(e : ZMod 3) :=
    (Int.cast_neg (R := ZMod 3) (e : ℤ)).trans (congrArg Neg.neg (Int.cast_natCast e))
  rw [hr, hi]

theorem sourceKPTameJacquetScaledIntegral_ball_zero (e : ℕ) :
    IntegrableOn (sourceKPTameJacquetScaledIntegrand K hζ S₀ P e) (B 0) μ₀ ∧
      (∫ H in B 0, sourceKPTameJacquetScaledIntegrand K hζ S₀ P e H ∂μ₀) =
        sourceJacquetScale Q₀ ((e : ℝ) / 3) • sourceJacquetBasis (-(e : ZMod 3)) := by
  let v := sourceJacquetScale Q₀ ((e : ℝ) / 3) • sourceJacquetBasis (-(e : ZMod 3))
  let : Measure.IsAddHaarMeasure μ₀ := sourceJacquetHaar_isAddHaar K P.val
  have hB := sourceLocalBall_isCompact K P.val 0
  have hI : IntegrableOn (fun _ => v) (B 0) μ₀ := continuousOn_const.integrableOn_compact hB
  have he : Set.EqOn (sourceKPTameJacquetScaledIntegrand K hζ S₀ P e) (fun _ => v) (B 0) :=
    fun H hH => sourceKPTameJacquetScaledIntegrand_on_zero_ball K hζ S₀ P e H hH
  refine ⟨hI.congr_fun (fun H hH => (he hH).symm) hB.measurableSet, ?_⟩
  have hμ : Measure.real μ₀ (B 0) = 1 := by
    rw [Measure.real, sourceLocalBall_zero_eq_integerOpen, sourceJacquetHaar_integers, ENNReal.toReal_one]
  rw [setIntegral_congr_fun hB.measurableSet he, setIntegral_const, hμ, one_smul]

end
end ArtinMatthews
