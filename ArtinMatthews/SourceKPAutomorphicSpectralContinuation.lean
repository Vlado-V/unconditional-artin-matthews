module

public import ArtinMatthews.SourceKPAutomorphicSpectralFamily
public import ArtinMatthews.SourceKPCompactGarding


set_option backward.privateInPublic true
@[expose] public section

/-! Fredholm continuation on the genuine closed form of the actual automorphic quotient. -/
namespace ArtinMatthews
open NumberField Filter HilbertResolvent
open scoped NumberField AdeleRing MatrixGroups Topology InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "rK" => (InfinitePlace.nrComplexPlaces K : ℝ)
local notation "j" => sourceKPCompactGenuineH1Mass K hζ
local notation "V" => SourceKPCompactGenuineH1 K hζ

theorem sourceKPAutomorphicSpectralPencil_fredholm (t : ℝ) (ht : t < rK) :
    (pencil ((j).adjoint.comp j) (t : ℂ)).IsFredholm := by
  obtain ⟨R,C,hC,h⟩ := sourceKPCompactH1_garding K hζ
  apply pencil_adjoint_comp_fredholm_of_form_estimate j
    (sourceKPCompactGenuineH1LocalizedMass K hζ R)
    (sourceKPCompactGenuineH1LocalizedMass_isCompactOperator K hζ R)
    (sourceKPAutomorphicSpectralRank_pos K hζ).le ht hC
  intro u
  have he := h u.val
  change rK * ‖sourceKPCompactH1Mass K hζ u.val‖^2 ≤
    ‖u.val‖^2-‖sourceKPCompactH1Mass K hζ u.val‖^2 +
      C*‖sourceKPCompactH1LocalizedMass K hζ R u.val‖^2 at he
  exact he

theorem sourceKPAutomorphicTruncatedContinuation_meromorphic {T : ℝ} (hT : 1 ≤ T) :
    MeromorphicOn (sourceKPAutomorphicTruncatedContinuation K hζ hT) {s | 0 < s.re} :=
  spectralCorrection_meromorphicOn j (sourceKPAutomorphicSpectralRank_pos K hζ)
    (sourceKPAutomorphicSpectralPencil_fredholm K hζ) _
    (sourceKPAutomorphicGenuineDefectL2_analyticAt K hζ hT)

theorem sourceKPAutomorphicExceptionalRegularized_analyticAt {T : ℝ} (hT : 1 ≤ T) :
    AnalyticAt ℂ (sourceKPAutomorphicExceptionalRegularized K hζ hT) (1/6) :=
  exceptionalDesingularizedCorrection_analyticAt j (sourceKPAutomorphicSpectralRank_pos K hζ)
    (sourceKPAutomorphicSpectralPencil_fredholm K hζ)
    (sourceKPAutomorphicGenuineDefectL2_analyticAt K hζ hT (1/6))

theorem sourceKPAutomorphicExceptionalRegularized_eventually_eq {T : ℝ} (hT : 1 ≤ T) :
    sourceKPAutomorphicExceptionalRegularized K hζ hT =ᶠ[𝓝[≠] (1/6 : ℂ)]
      fun s => (s-1/6) • sourceKPAutomorphicTruncatedContinuation K hζ hT s :=
  eventually_exceptionalDesingularizedCorrection_eq j (sourceKPAutomorphicSpectralRank_pos K hζ)
    (sourceKPAutomorphicSpectralPencil_fredholm K hζ) _

theorem sourceKPAutomorphicExceptionalResidue_tendsto {T : ℝ} (hT : 1 ≤ T) :
    Tendsto (fun s => (s-1/6) • sourceKPAutomorphicTruncatedContinuation K hζ hT s)
      (𝓝[≠] (1/6 : ℂ)) (𝓝 (sourceKPAutomorphicExceptionalResidue K hζ hT)) :=
  spectralCorrection_residue_tendsto j (sourceKPAutomorphicSpectralRank_pos K hζ)
    (sourceKPAutomorphicSpectralPencil_fredholm K hζ)
    (sourceKPAutomorphicGenuineDefectL2_analyticAt K hζ hT (1/6))

def sourceKPAutomorphicExceptionalFormResidue {T : ℝ} (hT : 1 ≤ T) : V :=
  (-3 * ((exceptionalCenter rK : ℂ)+1) / (4*(rK : ℂ))) •
    (nullSpace ((j).adjoint.comp j) (exceptionalCenter rK)).starProjection
      ((j).adjoint (sourceKPAutomorphicGenuineDefectL2 K hζ hT (1/6)))

theorem sourceKPAutomorphicExceptionalFormResidue_mem_null {T : ℝ} (hT : 1 ≤ T) :
    sourceKPAutomorphicExceptionalFormResidue K hζ hT ∈
      nullSpace ((j).adjoint.comp j) (exceptionalCenter rK) :=
  (nullSpace ((j).adjoint.comp j) (exceptionalCenter rK)).smul_mem _
    ((nullSpace ((j).adjoint.comp j) (exceptionalCenter rK)).starProjection_apply_mem _)

theorem sourceKPAutomorphicExceptionalFormResidue_mass {T : ℝ} (hT : 1 ≤ T) :
    j (sourceKPAutomorphicExceptionalFormResidue K hζ hT) =
      sourceKPAutomorphicExceptionalResidue K hζ hT := by
  unfold sourceKPAutomorphicExceptionalFormResidue sourceKPAutomorphicExceptionalResidue exceptionalResidue
  rw [map_smul]

theorem sourceKPAutomorphicExceptionalFormResidue_weak_eigen {T : ℝ} (hT : 1 ≤ T) (v : V) :
    sourceKPCompactH1Dirichlet K hζ v.val (sourceKPAutomorphicExceptionalFormResidue K hζ hT).val =
      (exceptionalCenter rK : ℂ) * inner ℂ (j v) (sourceKPAutomorphicExceptionalResidue K hζ hT) := by
  let u := sourceKPAutomorphicExceptionalFormResidue K hζ hT
  have h : pencil ((j).adjoint.comp j) (exceptionalCenter rK : ℂ) u = 0 :=
    sourceKPAutomorphicExceptionalFormResidue_mem_null K hζ hT
  have he := congrArg (fun w : V => inner ℂ v w) h
  change inner ℂ v (pencil ((j).adjoint.comp j) (exceptionalCenter rK : ℂ) u) = inner ℂ v 0 at he
  rw [pencil_adjoint_comp_inner_right,inner_zero_right] at he
  rw [← sourceKPAutomorphicExceptionalFormResidue_mass K hζ hT]
  change inner ℂ v u-inner ℂ (j v) (j u) =
    (exceptionalCenter rK : ℂ)*inner ℂ (j v) (j u)
  linear_combination he

end
end ArtinMatthews
