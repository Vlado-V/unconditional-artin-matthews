module

public import ArtinMatthews.SourceKPRetainedThetaTensor
public import ArtinMatthews.SourceThetaPositiveSheet
public import ArtinMatthews.SourceThetaRotatedSmoothing
public import ArtinMatthews.SourceThetaWeightedSheet


set_option backward.privateInPublic true
@[expose] public section

/-! The reflected Gaussian profiles of the finite retained family use
the literal normalized sheet and the original positive theta constants. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain ClassFieldTheory QuadraticWeil
open MeasureTheory SourcePhysical SourceReflection VaryingKummerAnalytic
open scoped NumberField Classical ContDiff BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {I : Type*}
variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
variable {J : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
variable (rowU : I → exteriorUnitSubgroup (sourceHilbertSet K S₀))
variable (a : I → ∀ P : ↥(sourceHilbertSet K S₀), SourceFiniteKP2Projective K hζ P.val)
variable (v : InfinitePlace K)

local notation "S" => sourceHilbertSet K S₀
local notation "Label" => SourceKPRetainedThetaLabel K hζ S₀ I
local notation "F" => sourceKPRetainedThetaFiniteFactor K hζ S₀ hS η hJ rowU a
local notation "D" => sourceKPRetainedThetaTensor K hζ S₀ hS η hJ rowU a v
local notation "c" => (fun _ : InfinitePlace K => (4 : ℝ) * Real.pi)
local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v

theorem sourceKPRetainedThetaTensor_sheet_eq (d : Label) :
    (D d).sheet 0 = sourceSLocalSheetProfile S ν hζ
      (fun x => (∏ w : InfinitePlace K, sourceThetaBesselProfile (4 * Real.pi) (sourceSheetArchNorm w (x.1 w))) *
        ∏ P : S, F d P (x.2 P)) := by
  unfold SourceThetaRotatedTensor.sheet sourceThetaSLocalSheet
  congr 1
  funext x
  exact sourceKPRetainedThetaTensor_literal K hζ S₀ hS η hJ rowU a v d x

variable (U : ∀ P : ↥(sourceHilbertSet K S₀), SourceThetaFiniteCutoff K P.val)

local notation "C₀" => sourceThetaMellinConstant K S c U
local notation "A₀" => sourceThetaMellinScale K c
local notation "r" => Fintype.card (InfinitePlace K)

def sourceKPRetainedThetaProfile (d : Label) : ℝ → ℂ :=
  (D d).smoothed C₀ A₀ r (-1) 0

local notation "P" => sourceKPRetainedThetaProfile K hζ S₀ hS η hJ rowU a v U

theorem sourceKPRetainedThetaProfile_eq_weightedSheet (d : Label) :
    P d = sourceThetaGaussianProfile C₀ A₀ r (-1) ((D d).weightedSheet 0 (fun _ => 1)) := by
  unfold sourceKPRetainedThetaProfile SourceThetaRotatedTensor.smoothed
    SourceThetaRotatedTensor.sheet sourceThetaSLocalSheet SourceThetaRotatedTensor.weightedSheet
  simp only [one_mul]

theorem sourceKPRetainedThetaProfile_eq_literal (d : Label) :
    P d = sourceThetaGaussianProfile C₀ A₀ r (-1)
      (sourceSLocalSheetProfile S ν hζ
        (fun x => (∏ w : InfinitePlace K, sourceThetaBesselProfile (4 * Real.pi) (sourceSheetArchNorm w (x.1 w))) *
          ∏ p : S, F d p (x.2 p))) := by
  unfold sourceKPRetainedThetaProfile SourceThetaRotatedTensor.smoothed
  rw [sourceKPRetainedThetaTensor_sheet_eq K hζ S₀ hS η hJ rowU a v d]

theorem sourceKPRetainedThetaProfile_logSmooth (d : Label) :
    ContDiff ℝ ∞ (fun t : ℝ => P d (Real.exp t)) :=
  (D d).smoothed_logSmooth C₀ A₀ r (-1) (by norm_num)

theorem sourceKPRetainedThetaProfile_logDeriv_twoEnded (d : Label)
    {α A : ℝ} (hα : α < 1 / 3) (hA : -(1 / 3 : ℝ) < A) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (fun x => P d (Real.exp x)) t‖ ≤
        C * min (Real.exp (α * t)) (Real.exp (-A * t)) := by
  obtain ⟨C,hC,h⟩ := (D d).smoothed_logDeriv_twoEnded C₀ A₀ r (-1) (by norm_num) hα hA j
  exact ⟨C,hC,fun t => (le_add_of_nonneg_right ((D d).smoothedAbs_nonneg C₀ A₀ r (-1) j t)).trans (h t)⟩

theorem sourceKPRetainedThetaProfile_abs_integrable (d : Label) (j : ℕ) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (sourceThetaGaussianProfileAbsIntegrand C₀ A₀ r (-1)
      (sourceThetaSLocalSheetAbs K S hζ v ((D d).localDeriv j) (D d).retained) T) (Set.Ioi 0) :=
  (D d).smoothedAbs_integrable C₀ A₀ r (-1) j 0 (by norm_num) hT

theorem sourceKPRetainedThetaProfile_logDeriv_uniform [Finite I]
    {α A : ℝ} (hα : α < 1 / 3) (hA : -(1 / 3 : ℝ) < A) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : Label) (j : ℕ), j ≤ m → ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (fun x => P d (Real.exp x)) t‖ ≤
        C * min (Real.exp (α * t)) (Real.exp (-A * t)) := by
  let : Fintype I := Fintype.ofFinite I
  let : Fintype Label := sourceKPRetainedThetaLabel_fintype K hζ S₀ I
  let B := Label × Fin (m + 1)
  have hB (p : B) := sourceKPRetainedThetaProfile_logDeriv_twoEnded K hζ S₀ hS η hJ rowU a v U
    p.1 hα hA p.2.val
  choose M hM hbound using hB
  refine ⟨∑ p : B, M p, Finset.sum_nonneg (fun p _ => hM p), fun d j hj t => ?_⟩
  let p : B := (d, ⟨j, Nat.lt_succ_of_le hj⟩)
  exact (hbound p t).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun q _ => hM q) (Finset.mem_univ p))
    (le_min (Real.exp_pos _).le (Real.exp_pos _).le))

theorem sourceKPRetainedThetaProfile_finiteProfiles [Finite I] :
    (∀ d : Label, ContDiff ℝ ∞ (fun x : ℝ => P d (Real.exp x))) ∧
    ∀ d : Label, ∃ α : ℝ, 0 ≤ α ∧ ∀ A : ℝ, 0 < A →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 2, ∀ x : ℝ,
        ‖iteratedFDeriv ℝ k (fun y => P d (Real.exp y)) x‖ ≤
          M * min (Real.exp (α * x)) (Real.exp (-A * x)) := by
  refine ⟨sourceKPRetainedThetaProfile_logSmooth K hζ S₀ hS η hJ rowU a v U, fun d => ?_⟩
  refine ⟨1 / 6, by norm_num, fun A hA => ?_⟩
  have hA' : -(1 / 3 : ℝ) < A := by linarith
  obtain ⟨M,hM,h⟩ := sourceKPRetainedThetaProfile_logDeriv_uniform K hζ S₀ hS η hJ rowU a v U
    (show (1 / 6 : ℝ) < 1 / 3 by norm_num) hA' 2
  exact ⟨M,hM,h d⟩

end
end ArtinMatthews
