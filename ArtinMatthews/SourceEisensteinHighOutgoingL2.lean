module

public import ArtinMatthews.SourceEisensteinHighOutgoingMass
public import Mathlib.Analysis.SpecificLimits.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine outgoing term is square-integrable in the initial right half-plane,
by its exact geometric mass on the literal dyadic high-cusp shells. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "X" => SourceKPAutomorphicLevel K hζ
local instance sourceHighOutgoingL2Measurable : MeasurableSpace X := borel X
local instance sourceHighOutgoingL2Borel : BorelSpace X := ⟨rfl⟩
local notation "μ" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)

def sourceKPDyadicRadialTime (n : ℕ) : ℝ :=
  n * Real.log 2 / (2 * Fintype.card (InfinitePlace K))

theorem sourceKPDyadicRadialTime_nonneg (n : ℕ) : 0 ≤ sourceKPDyadicRadialTime K n := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog.le) (by positivity)

theorem sourceKPDyadicRadialTime_scale (n : ℕ) :
    sourceKPRadialHeightScale K (sourceKPDyadicRadialTime K n) = (2 : ℝ) ^ n := by
  have hcard : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : 2 * (Fintype.card (InfinitePlace K) : ℝ) *
      (n * Real.log 2 / (2 * Fintype.card (InfinitePlace K))) = n * Real.log 2 := by
    field_simp [hcard]
  rw [sourceKPRadialHeightScale,sourceKPDyadicRadialTime,he,Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem sourceKPHighOutgoingExtension_dyadic_mass {s : ℂ} (hs : 0 < s.re)
    (T : ℝ) (hT : 1 < T) (n : ℕ) :
    (∫ x in dyadicL2OpenShell (sourceKPAutomorphicOrbitHeight K hζ) T n,
      ‖sourceKPHighOutgoingExtension K hζ s T hT x‖ ^ 2 ∂μ) =
      ((2 : ℝ) ^ (-2*s.re)) ^ n *
        (∫ x in dyadicL2OpenShell (sourceKPAutomorphicOrbitHeight K hζ) T 0,
          ‖sourceKPHighOutgoingExtension K hζ s T hT x‖ ^ 2 ∂μ) := by
  have h := sourceKPHighOutgoingExtension_shell_mass_scale K hζ hs
    (sourceKPDyadicRadialTime K n) (sourceKPDyadicRadialTime_nonneg K n) T (T*2) hT
  rw [sourceKPDyadicRadialTime_scale] at h
  have hlo : (2 : ℝ)^n*T = T*2^n := mul_comm _ _
  have hhi : (2 : ℝ)^n*(T*2) = T*2^(n+1) := by rw [pow_succ]; ring
  have hp : ((2 : ℝ)^n)^(-2*s.re) = ((2 : ℝ)^(-2*s.re))^n := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_comm (n : ℝ),Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hlo,hhi,hp] at h
  simpa only [dyadicL2OpenShell,Nat.zero_add,pow_zero,pow_one,mul_one,Nat.cast_zero] using h

theorem sourceKPHighOutgoingExtension_dyadic_memLp {s : ℂ} (hs : 0 < s.re)
    (T : ℝ) (hT : 1 < T) (n : ℕ) :
    MemLp (sourceKPHighOutgoingExtension K hζ s T hT) 2
      ((μ).restrict (dyadicL2OpenShell (sourceKPAutomorphicOrbitHeight K hζ) T n)) := by
  apply (sourceKPHighOutgoingExtension_shell_memLp K hζ hs T (T*2^(n+1)) hT).mono_measure
  apply Measure.restrict_mono_set
  intro x hx
  refine ⟨?_,hx.2⟩
  have hp : T ≤ T*(2 : ℝ)^n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)) (zero_lt_one.trans hT).le
  exact hp.trans_lt hx.1

theorem sourceKPHighOutgoingExtension_memLp {s : ℂ} (hs : 0 < s.re)
    (T : ℝ) (hT : 1 < T) :
    MemLp (sourceKPHighOutgoingExtension K hζ s T hT) 2
      ((μ).restrict {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) := by
  apply memLp_high_of_summable_dyadicOpenShells μ (sourceKPAutomorphicOrbitHeight K hζ)
    (zero_lt_one.trans hT) _ (sourceKPHighOutgoingExtension_dyadic_memLp K hζ hs T hT)
  have hr : (2 : ℝ)^(-2*s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg := (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) hr).mul_right
    (∫ x in dyadicL2OpenShell (sourceKPAutomorphicOrbitHeight K hζ) T 0,
      ‖sourceKPHighOutgoingExtension K hζ s T hT x‖ ^ 2 ∂μ)
  exact hg.congr (fun n => (sourceKPHighOutgoingExtension_dyadic_mass K hζ hs T hT n).symm)

end
end ArtinMatthews
