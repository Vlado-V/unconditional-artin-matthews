module

public import ArtinMatthews.SpectralPrincipalDecayWeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric


set_option backward.privateInPublic true
@[expose] public section

/-! A true polynomial cutoff-mass bound gives a quantitative integrable
principal spectral weight, with its linear parameter retained. -/
namespace ArtinMatthews
open Set MeasureTheory Filter
noncomputable section

def spectralPrincipalCutoff {α : Type*} (τ : α → ℝ) (R : ℝ) : Set α :=
  {x | 1+|τ x| ≤ R}

theorem spectralPrincipalCutoff_measurable {α : Type*} [MeasurableSpace α]
    {τ : α → ℝ} (hτ : Measurable τ) (R : ℝ) :
    MeasurableSet (spectralPrincipalCutoff τ R) :=
  by
  have ha : Measurable (fun x => |τ x|) := by
    simpa only [Real.norm_eq_abs] using hτ.norm
  exact measurableSet_le (measurable_const.add ha) measurable_const

theorem spectralPrincipalDecayWeight_measurable {α : Type*} [MeasurableSpace α]
    {τ : α → ℝ} (hτ : Measurable τ) (Z : ℝ) :
    Measurable (fun x => spectralPrincipalDecayWeight Z (τ x)) := by
  unfold spectralPrincipalDecayWeight
  have ha : Measurable (fun x => |τ x|) := by
    simpa only [Real.norm_eq_abs] using hτ.norm
  exact measurable_const.div ((measurable_const.add (ha.div_const Z)).pow_const 4)

theorem spectralPrincipalDecayWeight_lintegral_bound
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (τ : α → ℝ)
    (hτ : Measurable τ) {B C Z : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hZ : 1 ≤ Z)
    (hcut : ∀ R : ℝ, 1 ≤ R →
      ν (spectralPrincipalCutoff τ R) ≤ ENNReal.ofReal (C*(R^2+B*R))) :
    (∫⁻ x, ENNReal.ofReal (spectralPrincipalDecayWeight Z (τ x)) ∂ν) ≤
      ENNReal.ofReal (8*C*(Z^2+B*Z)) := by
  let S (k : ℕ) := spectralPrincipalCutoff τ (spectralPrincipalDyadicRadius Z k)
  let G (k : ℕ) := (S k).indicator (fun _ => ENNReal.ofReal ((1/16 : ℝ)^k))
  let D := 4*C*(Z^2+B*Z)
  have hZ₀ : 0 ≤ Z := zero_le_one.trans hZ
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hS (k : ℕ) : MeasurableSet (S k) := spectralPrincipalCutoff_measurable hτ _
  have hG (k : ℕ) : Measurable (G k) := measurable_const.indicator (hS k)
  have hpoint (x : α) :
      ENNReal.ofReal (spectralPrincipalDecayWeight Z (τ x)) ≤ ∑' k, G k x := by
    obtain ⟨k,hk,hw⟩ := spectralPrincipalDecayWeight_dyadic hZ (τ x)
    calc
      _ ≤ ENNReal.ofReal ((1/16 : ℝ)^k) := ENNReal.ofReal_le_ofReal hw
      _ = G k x := by
        change ENNReal.ofReal ((1/16 : ℝ)^k) =
          (S k).indicator (fun _ : α => ENNReal.ofReal ((1/16 : ℝ)^k)) x
        rw [Set.indicator_of_mem (show x ∈ S k from hk)]
      _ ≤ _ := ENNReal.le_tsum (f := fun j => G j x) k
  have hcost (k : ℕ) : (∫⁻ x, G k x ∂ν) ≤ ENNReal.ofReal (D*(1/4 : ℝ)^k) := by
    change (∫⁻ x, (S k).indicator (fun _ => ENNReal.ofReal ((1/16 : ℝ)^k)) x ∂ν) ≤ _
    rw [lintegral_indicator (hS k), lintegral_const, Measure.restrict_apply_univ]
    calc
      _ ≤ ENNReal.ofReal ((1/16 : ℝ)^k) *
          ENNReal.ofReal (C*((spectralPrincipalDyadicRadius Z k)^2+B*spectralPrincipalDyadicRadius Z k)) :=
        mul_le_mul_right (hcut _ (spectralPrincipalDyadicRadius_ge_one hZ k)) _
      _ = ENNReal.ofReal ((1/16 : ℝ)^k *
          (C*((spectralPrincipalDyadicRadius Z k)^2+B*spectralPrincipalDyadicRadius Z k))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (spectralPrincipalDyadic_cost hB hC hZ₀ k)
  have hsum : Summable (fun k : ℕ => D*(1/4 : ℝ)^k) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num)).mul_left D
  have hsumle : (∑' k : ℕ, D*(1/4 : ℝ)^k) ≤ 8*C*(Z^2+B*Z) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num)]
    dsimp [D]
    have hbase : 0 ≤ C*(Z^2+B*Z) := by positivity
    nlinarith
  calc
    _ ≤ ∫⁻ x, ∑' k, G k x ∂ν := lintegral_mono hpoint
    _ = ∑' k, ∫⁻ x, G k x ∂ν := lintegral_tsum (fun k => (hG k).aemeasurable)
    _ ≤ ∑' k, ENNReal.ofReal (D*(1/4 : ℝ)^k) := ENNReal.tsum_le_tsum hcost
    _ = ENNReal.ofReal (∑' k : ℕ, D*(1/4 : ℝ)^k) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsumle

theorem spectralPrincipalDecayWeight_integrable_bound
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (τ : α → ℝ)
    (hτ : Measurable τ) {B C Z : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hZ : 1 ≤ Z)
    (hcut : ∀ R : ℝ, 1 ≤ R →
      ν (spectralPrincipalCutoff τ R) ≤ ENNReal.ofReal (C*(R^2+B*R))) :
    Integrable (fun x => spectralPrincipalDecayWeight Z (τ x)) ν ∧
      (∫ x, spectralPrincipalDecayWeight Z (τ x) ∂ν) ≤ 8*C*(Z^2+B*Z) := by
  have hlin := spectralPrincipalDecayWeight_lintegral_bound ν τ hτ hB hC hZ hcut
  have hpos : ∀ᵐ x ∂ν, 0 ≤ spectralPrincipalDecayWeight Z (τ x) :=
    Eventually.of_forall fun x => spectralPrincipalDecayWeight_nonneg Z (τ x)
  have hi : Integrable (fun x => spectralPrincipalDecayWeight Z (τ x)) ν :=
    ⟨(spectralPrincipalDecayWeight_measurable hτ Z).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hpos).mpr (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 8*C*(Z^2+B*Z))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi hpos]
  exact hlin

end
end ArtinMatthews
