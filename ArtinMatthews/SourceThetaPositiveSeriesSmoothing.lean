module

public import ArtinMatthews.SourceThetaPositiveCoefficientSeries
public import ArtinMatthews.SourceThetaSmoothingSum


set_option backward.privateInPublic true
@[expose] public section

/-! Forward Gaussian smoothing of the actual positive sheet expansion.
The Fubini bound uses the proved weighted sheet at exponent two and the
exterior ideal norm majorant. -/

namespace ArtinMatthews.SourceReflection

open NumberField IsDedekindDomain MeasureTheory AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "E" => SourcePrimeExponents K S₀
local notation "C" => ReflectionSquarefreeExponents K S₀

private theorem sourceExponent_countable : Countable E := by
  let f (e : E) := (sourcePrimeExponentNorm K S₀ e : ℝ) ^ (-2 : ℝ)
  have hs : Summable f := sourcePrimeExponentNorm_summable K S₀ (σ := 2) (by norm_num)
  have hall : Function.support f = Set.univ := Set.eq_univ_of_forall fun e =>
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos K S₀ e)) _).ne'
  exact Set.countable_univ_iff.mp (hall ▸ hs.countable_support)

variable [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : QuadraticWeil.standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
variable {M : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K M)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
variable (U : ∀ p : S, SourceThetaFiniteCutoff K p.val) (v : InfinitePlace K)

local notation "H" => sourceThetaPositiveSheet K S c U hζ v
local notation "C₀" => sourceThetaMellinConstant K S c U
local notation "A₀" => sourceThetaMellinScale K c
local notation "r" => Fintype.card (InfinitePlace K)

include hc in
theorem sourceThetaPositiveCoefficientSeries_smoothing (row : sourceRing K S₀)
    {Z : ℝ} (hZ : 0 < Z) :
    sourceThetaGaussianSmoothing C₀ A₀ r
      (sourceThetaPositiveCoefficientSeries K hζ S₀ hS η S c U v row) (1 / Z) =
      reflectionCoefficientRow K hζ S₀ hS η row Z := by
  let _ : Countable E := sourceExponent_countable K S₀
  let _ : Countable C := by
    unfold ReflectionSquarefreeExponents
    infer_instance
  let J := C × E
  let _ : Countable J := inferInstanceAs (Countable (C × E))
  let u : ℝ := 1 / Z
  let x := Real.log u
  let N (p : J) : ℝ := sourcePrimeExponentNorm K S₀ (p.1.val + 3 • p.2)
  let b (p : J) := Real.log (N p)
  let a (p : J) := reflectionCoefficientBeforeGaussian K hζ S₀ hS η p.1 p.2 row
  let W (t : ℝ) := H (Real.exp t)
  have hN (p : J) : 0 < N p := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos K S₀ _)
  have hu : 0 < u := one_div_pos.mpr hZ
  have hW : Measurable W := sourceThetaPositiveSheet_log_measurable K S c hc U hζ v
  obtain ⟨B, hB, hb⟩ := sourceThetaPositiveSheet_log_norm_bound K S c hc U hζ v 2 (by norm_num)
  let A (_ : J) (t : ℝ) := B * Real.exp (-(2 : ℝ) * t)
  have hA (p : J) : Measurable (A p) := by unfold A; fun_prop
  have hA₀ (p : J) (t : ℝ) : 0 ≤ A p t := mul_nonneg hB (Real.exp_pos _).le
  have hD : Summable (fun p : J => ‖a p‖ * Real.exp (-(2 : ℝ) * b p)) := by
    refine (reflectionCoefficientBeforeGaussian_dirichlet_summable K hζ S₀ hS η row
      (σ := 2) (by norm_num)).congr ?_
    intro p
    change ‖a p‖ * (N p) ^ (-2 : ℝ) = ‖a p‖ * Real.exp (-(2 : ℝ) * Real.log (N p))
    rw [Real.rpow_def_of_pos (hN p), mul_comm (Real.log (N p))]
  have hsum := sourceThetaGaussianLogSmooth_sum_integral C₀ A₀ r 1 2 B x a b A
    hA hA₀ (fun _ _ => le_rfl) hD (fun _ => W) (fun _ => hW) (fun _ t => hb t)
  have hlog (V : ℝ → ℂ) (t : ℝ) :
      sourceThetaGaussianSmoothing C₀ A₀ r V (Real.exp t) =
        sourceThetaGaussianLogSmooth C₀ A₀ r 1 (fun y => V (Real.exp y)) t := by
    have h := sourceThetaGaussianProfile_exp C₀ A₀ r 1 V t
    rw [sourceThetaGaussianProfile_forward] at h
    exact h
  calc
    _ = sourceThetaGaussianLogSmooth C₀ A₀ r 1
        (fun y => sourceThetaPositiveCoefficientSeries K hζ S₀ hS η S c U v row (Real.exp y)) x := by
      have h := hlog (sourceThetaPositiveCoefficientSeries K hζ S₀ hS η S c U v row) x
      rwa [show Real.exp x = u from Real.exp_log hu] at h
    _ = ∫ y : ℝ, sourceThetaGaussianLogKernel C₀ A₀ r y *
        (∑' p : J, a p * W (x + b p + 1 * y)) := by
      unfold sourceThetaGaussianLogSmooth
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        apply congrArg (fun z : ℂ => sourceThetaGaussianLogKernel C₀ A₀ r y * z)
        change sourceThetaPositiveCoefficientSeries K hζ S₀ hS η S c U v row
          (Real.exp (x + 1 * y)) = _
        rw [sourceThetaPositiveCoefficientSeries_eq_product_tsum K hζ S₀ hS η S c U v hc row
          (Real.exp_pos _)]
        apply tsum_congr
        intro p
        change a p * H (N p * Real.exp (x + 1 * y)) = a p * H (Real.exp (x + b p + 1 * y))
        rw [show x + b p + 1 * y = b p + (x + 1 * y) by ring,
          Real.exp_add (b p) (x + 1 * y), show Real.exp (b p) = N p from Real.exp_log (hN p)]
    _ = ∑' p : J, a p * sourceThetaGaussianLogSmooth C₀ A₀ r 1 W (x + b p) := hsum
    _ = ∑' p : J, reflectionCoefficientTerm K hζ S₀ hS η p.1 p.2 row Z := by
      apply tsum_congr
      intro p
      have harg : Real.exp (x + b p) = N p / Z := by
        rw [Real.exp_add, show Real.exp x = u from Real.exp_log hu,
          show Real.exp (b p) = N p from Real.exp_log (hN p)]
        change (1 / Z) * N p = N p / Z
        ring
      change a p * sourceThetaGaussianLogSmooth C₀ A₀ r 1 (fun y => H (Real.exp y)) (x + b p) = _
      rw [← hlog H (x + b p), harg, sourceThetaPositiveSheet_smoothing K S c U hζ v hc
        (div_pos (hN p) hZ), reflectionCoefficientTerm_eq_beforeGaussian_mul]
    _ = _ := (reflectionCoefficientRow_eq_product_tsum K hζ S₀ hS η row hZ).symm

end
end ArtinMatthews.SourceReflection
