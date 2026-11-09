module

public import ArtinMatthews.SourceKPAutomorphicSpectralContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual genuine form residue satisfies the weak eigenvalue
equation against the full scalar form. The cubic projector is the
contractive projection in the actual mass-and-energy Hilbert norm. -/

namespace ArtinMatthews
open NumberField MeasureTheory HilbertResolvent
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "V" => SourceKPCompactH1 K hζ
local notation "Vχ" => SourceKPCompactGenuineH1 K hζ
local notation "P" => sourceKPCompactH1Projector K hζ
local notation "J" => sourceKPCompactH1Mass K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "Q" => sourceKPCompactGenuineL2Projector K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCompactH1Projector_opNorm_le : ‖P‖ ≤ 1 := by
  apply (P).opNorm_le_bound zero_le_one
  intro u
  rw [one_mul]
  refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
    (p := fun w => ‖P w‖ ≤ ‖w‖) u
    (isClosed_le (P).continuous.norm continuous_norm) ?_
  intro f
  rw [sourceKPCompactH1Projector_core, LinearIsometry.norm_map, LinearIsometry.norm_map]
  have hc : ‖sourceKPCompactFormCoreProjector K hζ‖ ≤ 1 := by
    unfold sourceKPCompactFormCoreProjector
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  simpa only [one_mul] using (sourceKPCompactFormCoreProjector K hζ).le_of_opNorm_le hc f

private theorem genuine_mass_projector_fixed (u : Vχ) : Q (J u.val) = J u.val :=
  (sourceKPCompactGenuineL2Projector_fixed_iff K hζ (sourceKPArchHaar K hζ) _).mpr u.prop

theorem sourceKPCompactH1Projector_fixed_genuine (u : Vχ) : P u.val = u.val := by
  apply sourceKPCompactH1Mass_injective K hζ
  rw [sourceKPCompactH1Projector_mass]
  exact genuine_mass_projector_fixed K hζ u

theorem sourceKPCompactH1Projector_inner_genuine (v : V) (u : Vχ) :
    inner ℂ (P v) u.val = inner ℂ v u.val := by
  let a := (P).adjoint u.val
  have hnorm : ‖a‖ ≤ ‖u.val‖ := by
    have hp : ‖(P).adjoint‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]
      exact sourceKPCompactH1Projector_opNorm_le K hζ
    simpa only [one_mul] using ((P).adjoint).le_of_opNorm_le hp u.val
  have hinner : inner ℂ a u.val = inner ℂ u.val u.val := by
    rw [show a = (P).adjoint u.val from rfl, ContinuousLinearMap.adjoint_inner_left,
      sourceKPCompactH1Projector_fixed_genuine K hζ u]
  have hn : ‖a - u.val‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hinner, inner_self_eq_norm_sq_to_K]
    have hsq := pow_le_pow_left₀ (norm_nonneg a) hnorm 2
    change ‖a‖ ^ 2 - 2 * ((‖u.val‖ : ℂ) ^ 2).re + ‖u.val‖ ^ 2 ≤ 0
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    linarith
  have hzero : ‖a - u.val‖ = 0 := by nlinarith [norm_nonneg (a-u.val)]
  have ha : a = u.val := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  rw [← ContinuousLinearMap.adjoint_inner_right]
  exact congrArg (inner ℂ v) ha

theorem sourceKPCompactH1Projector_mass_inner_genuine (v : V) (u : Vχ) :
    inner ℂ (J (P v)) (J u.val) = inner ℂ (J v) (J u.val) := by
  rw [sourceKPCompactH1Projector_mass]
  have h := sourceKPCompactGenuineL2Projector_isSymmetric K hζ (sourceKPArchHaar K hζ)
    (J v) (J u.val)
  change inner ℂ (Q (J v)) (J u.val) = inner ℂ (J v) (Q (J u.val)) at h
  rw [genuine_mass_projector_fixed K hζ u] at h
  exact h

theorem sourceKPCompactH1Projector_dirichlet_genuine (v : V) (u : Vχ) :
    sourceKPCompactH1Dirichlet K hζ (P v) u.val = sourceKPCompactH1Dirichlet K hζ v u.val := by
  unfold sourceKPCompactH1Dirichlet
  rw [sourceKPCompactH1Projector_inner_genuine, sourceKPCompactH1Projector_mass_inner_genuine]

theorem sourceKPAutomorphicExceptionalFormResidue_weak_eigen_scalar {T : ℝ} (hT : 1 ≤ T) (v : V) :
    sourceKPCompactH1Dirichlet K hζ v (sourceKPAutomorphicExceptionalFormResidue K hζ hT).val =
      (exceptionalCenter (InfinitePlace.nrComplexPlaces K : ℝ) : ℂ) *
        inner ℂ (J v) (sourceKPAutomorphicExceptionalResidue K hζ hT).val := by
  let u := sourceKPAutomorphicExceptionalFormResidue K hζ hT
  let r := sourceKPAutomorphicExceptionalResidue K hζ hT
  have hm : J u.val = r.val := congrArg Subtype.val
    (sourceKPAutomorphicExceptionalFormResidue_mass K hζ hT)
  have h := sourceKPAutomorphicExceptionalFormResidue_weak_eigen K hζ hT
    (sourceKPCompactH1ProjectToGenuine K hζ v)
  change sourceKPCompactH1Dirichlet K hζ (P v) u.val =
    (exceptionalCenter (InfinitePlace.nrComplexPlaces K : ℝ) : ℂ) * inner ℂ (J (P v)) r.val at h
  rw [sourceKPCompactH1Projector_dirichlet_genuine K hζ v u, ← hm,
    sourceKPCompactH1Projector_mass_inner_genuine K hζ v u, hm] at h
  exact h

end
end ArtinMatthews
