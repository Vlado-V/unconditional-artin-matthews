module

public import ArtinMatthews.SourceHilbertSpectralCorrection


set_option backward.privateInPublic true
@[expose] public section

/-! The exact pullback of the finite-rank singular term at s = 1/6. -/

namespace ArtinMatthews.HilbertResolvent

open Filter
open scoped InnerProductSpace Topology
noncomputable section

def exceptionalCenter (r : ℝ) : ℝ := 8 * r / 9

def exceptionalFactor (r : ℝ) (s : ℂ) : ℂ := -4 * (r : ℂ) * (s + 1 / 6)

theorem exceptionalCenter_lt {r : ℝ} (hr : 0 < r) : exceptionalCenter r < r := by
  unfold exceptionalCenter
  linarith

theorem exceptionalCenter_add_one_ne_zero {r : ℝ} (hr : 0 < r) :
    exceptionalCenter r + 1 ≠ 0 := by
  unfold exceptionalCenter
  linarith

theorem spectralParameter_exceptional (r : ℝ) :
    spectralParameter r (1 / 6) = (exceptionalCenter r : ℂ) := by
  simp only [spectralParameter, exceptionalCenter, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem spectralParameter_sub_exceptional (r : ℝ) (s : ℂ) :
    spectralParameter r s - (exceptionalCenter r : ℂ) = (s - 1 / 6) * exceptionalFactor r s := by
  rw [← spectralParameter_exceptional r]
  unfold spectralParameter exceptionalFactor
  ring

theorem exceptionalFactor_value (r : ℝ) :
    exceptionalFactor r (1 / 6) = -4 * (r : ℂ) / 3 := by
  unfold exceptionalFactor
  ring

theorem exceptionalFactor_analyticAt (r : ℝ) (s : ℂ) : AnalyticAt ℂ (exceptionalFactor r) s := by
  unfold exceptionalFactor
  fun_prop

theorem exceptionalFactor_ne_zero {r : ℝ} (hr : 0 < r) : exceptionalFactor r (1 / 6) ≠ 0 := by
  rw [exceptionalFactor_value]
  exact div_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hr.ne')) (by norm_num)

theorem exceptionalFactor_eventually_ne_zero {r : ℝ} (hr : 0 < r) :
    ∀ᶠ s : ℂ in 𝓝 (1 / 6 : ℂ), exceptionalFactor r s ≠ 0 :=
  (exceptionalFactor_analyticAt r (1 / 6)).continuousAt.eventually
    (isOpen_ne.mem_nhds (exceptionalFactor_ne_zero hr))

theorem spectralParameter_tendsto_exceptional_punctured {r : ℝ} (hr : 0 < r) :
    Tendsto (spectralParameter r) (𝓝[≠] (1 / 6 : ℂ)) (𝓝[≠] (exceptionalCenter r : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : Tendsto (spectralParameter r) (𝓝 (1 / 6 : ℂ))
        (𝓝 (spectralParameter r (1 / 6))) :=
      (spectralParameter_analyticAt r (1 / 6)).continuousAt
    rw [spectralParameter_exceptional] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [(exceptionalFactor_eventually_ne_zero hr).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with s hf hs
    show spectralParameter r s ≠ (exceptionalCenter r : ℂ)
    intro he
    have hz : (s - (1 / 6 : ℂ)) * exceptionalFactor r s = 0 := by
      rw [← spectralParameter_sub_exceptional, he, sub_self]
    exact (mul_ne_zero (sub_ne_zero.mpr (show s ≠ (1 / 6 : ℂ) from hs)) hf) hz

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def exceptionalDesingularizedInverse (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (s : ℂ) : V →L[ℂ] V :=
  (exceptionalFactor r s)⁻¹ • desingularizedInverse (j.adjoint.comp j)
    (adjoint_comp_selfAdjoint j) (exceptionalCenter r)
    (exceptionalCenter_add_one_ne_zero hr) (spectralParameter r s)

theorem exceptionalDesingularizedInverse_analyticAt (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (hF : ∀ t : ℝ, t < r → (pencil (j.adjoint.comp j) (t : ℂ)).IsFredholm) :
    AnalyticAt ℂ (exceptionalDesingularizedInverse j hr) (1 / 6 : ℂ) := by
  have ha := (exceptionalFactor_analyticAt r (1 / 6)).inv (exceptionalFactor_ne_zero hr)
  have hb := (desingularizedInverse_analyticAt (j.adjoint.comp j) (adjoint_comp_selfAdjoint j)
    (exceptionalCenter r) (exceptionalCenter_add_one_ne_zero hr)
    (hF _ (exceptionalCenter_lt hr))).comp_of_eq
      (spectralParameter_analyticAt r (1 / 6)) (spectralParameter_exceptional r)
  exact ha.smul hb

theorem eventually_exceptionalDesingularizedInverse_eq (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (hF : ∀ t : ℝ, t < r → (pencil (j.adjoint.comp j) (t : ℂ)).IsFredholm) :
    exceptionalDesingularizedInverse j hr =ᶠ[𝓝[≠] (1 / 6 : ℂ)]
      (fun s => (s - 1 / 6) • spectralInverse j r s) := by
  have h := (eventually_desingularizedInverse_eq (j.adjoint.comp j) (adjoint_comp_selfAdjoint j)
    (exceptionalCenter r) (exceptionalCenter_add_one_ne_zero hr)
    (hF _ (exceptionalCenter_lt hr))).comp_tendsto
      (spectralParameter_tendsto_exceptional_punctured hr)
  filter_upwards [h, (exceptionalFactor_eventually_ne_zero hr).filter_mono nhdsWithin_le_nhds] with s hs hf
  change desingularizedInverse (j.adjoint.comp j) (adjoint_comp_selfAdjoint j) (exceptionalCenter r)
    (exceptionalCenter_add_one_ne_zero hr) (spectralParameter r s) =
    (spectralParameter r s - (exceptionalCenter r : ℂ)) • spectralInverse j r s at hs
  change (exceptionalFactor r s)⁻¹ • _ = (s - 1 / 6) • spectralInverse j r s
  rw [hs, spectralParameter_sub_exceptional, smul_smul]
  have hc : (exceptionalFactor r s)⁻¹ * ((s - 1 / 6) * exceptionalFactor r s) = s - 1 / 6 := by
    calc
      _ = (s - 1 / 6) * ((exceptionalFactor r s)⁻¹ * exceptionalFactor r s) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hf, mul_one]
  rw [hc]

theorem eventually_spectralPencil_isUnit_exceptional (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (hF : ∀ t : ℝ, t < r → (pencil (j.adjoint.comp j) (t : ℂ)).IsFredholm) :
    ∀ᶠ s : ℂ in 𝓝[≠] (1 / 6 : ℂ),
      IsUnit (pencil (j.adjoint.comp j) (spectralParameter r s)) :=
  (spectralParameter_tendsto_exceptional_punctured hr).eventually
    ((eventually_isUnit_and_inverse_eq (j.adjoint.comp j) (adjoint_comp_selfAdjoint j)
      (exceptionalCenter r) (exceptionalCenter_add_one_ne_zero hr)
      (hF _ (exceptionalCenter_lt hr))).mono (fun _ h => h.1))

def exceptionalDesingularizedCorrection (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (D : ℂ → H) (s : ℂ) : H :=
  -j (exceptionalDesingularizedInverse j hr s (j.adjoint (D s)))

def exceptionalResidue (j : V →L[ℂ] H) (r : ℝ) (D : ℂ → H) : H :=
  (-3 * ((exceptionalCenter r : ℂ) + 1) / (4 * (r : ℂ))) •
    j ((nullSpace (j.adjoint.comp j) (exceptionalCenter r)).starProjection (j.adjoint (D (1 / 6))))

theorem exceptionalDesingularizedCorrection_value (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (D : ℂ → H) : exceptionalDesingularizedCorrection j hr D (1 / 6) = exceptionalResidue j r D := by
  unfold exceptionalDesingularizedCorrection exceptionalDesingularizedInverse
  rw [spectralParameter_exceptional, desingularizedInverse_center, exceptionalFactor_value]
  unfold poleResidue exceptionalResidue
  rw [smul_smul, smul_apply, map_smul, ← neg_smul]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr hr.ne']

theorem exceptionalDesingularizedCorrection_analyticAt (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (hF : ∀ t : ℝ, t < r → (pencil (j.adjoint.comp j) (t : ℂ)).IsFredholm)
    {D : ℂ → H} (hD : AnalyticAt ℂ D (1 / 6 : ℂ)) :
    AnalyticAt ℂ (exceptionalDesingularizedCorrection j hr D) (1 / 6 : ℂ) :=
  forcedCorrection_analyticAt j (exceptionalDesingularizedInverse_analyticAt j hr hF) hD

theorem eventually_exceptionalDesingularizedCorrection_eq (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (hF : ∀ t : ℝ, t < r → (pencil (j.adjoint.comp j) (t : ℂ)).IsFredholm) (D : ℂ → H) :
    exceptionalDesingularizedCorrection j hr D =ᶠ[𝓝[≠] (1 / 6 : ℂ)]
      (fun s => (s - 1 / 6) • spectralCorrection j r D s) := by
  filter_upwards [eventually_exceptionalDesingularizedInverse_eq j hr hF] with s hs
  change -j (exceptionalDesingularizedInverse j hr s (j.adjoint (D s))) =
    (s - 1 / 6) • (-j (spectralInverse j r s (j.adjoint (D s))))
  rw [hs, smul_apply, map_smul, smul_neg]

theorem spectralCorrection_residue_tendsto (j : V →L[ℂ] H) {r : ℝ} (hr : 0 < r)
    (hF : ∀ t : ℝ, t < r → (pencil (j.adjoint.comp j) (t : ℂ)).IsFredholm)
    {D : ℂ → H} (hD : AnalyticAt ℂ D (1 / 6 : ℂ)) :
    Tendsto (fun s => (s - 1 / 6) • spectralCorrection j r D s)
      (𝓝[≠] (1 / 6 : ℂ)) (𝓝 (exceptionalResidue j r D)) := by
  have hc : Tendsto (exceptionalDesingularizedCorrection j hr D) (𝓝 (1 / 6 : ℂ))
      (𝓝 (exceptionalDesingularizedCorrection j hr D (1 / 6))) :=
    (exceptionalDesingularizedCorrection_analyticAt j hr hF hD).continuousAt
  rw [exceptionalDesingularizedCorrection_value] at hc
  exact (hc.mono_left nhdsWithin_le_nhds).congr'
    (eventually_exceptionalDesingularizedCorrection_eq j hr hF D)

end
end ArtinMatthews.HilbertResolvent
