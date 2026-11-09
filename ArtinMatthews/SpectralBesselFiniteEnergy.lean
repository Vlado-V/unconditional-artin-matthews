module

public import ArtinMatthews.SpectralBesselODEUniqueness
public import ArtinMatthews.SpectralBesselKWhittakerDecay


set_option backward.privateInPublic true
@[expose] public section

/-! Wronskian uniqueness using the actual weighted mass and unweighted
vertical energy on a cusp ray. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralWronskian (f g : ℝ → ℂ) (y : ℝ) : ℂ :=
  deriv f y * g y - f y * deriv g y

theorem spectralWronskian_hasDerivAt (a : ℂ) (f g : ℝ → ℂ) (y : ℝ)
    (hf : HasDerivAt f (deriv f y) y)
    (hf' : HasDerivAt (deriv f) (a * f y) y)
    (hg : HasDerivAt g (deriv g y) y)
    (hg' : HasDerivAt (deriv g) (a * g y) y) :
    HasDerivAt (spectralWronskian f g) 0 y := by
  have hd := (hf'.mul hg).sub (hf.mul hg')
  convert hd using 1
  · rfl
  · ring

theorem spectralWronskian_eq (a : ℝ → ℂ) (f g : ℝ → ℂ) (Y x y : ℝ)
    (hx : Y < x) (hy : Y < y)
    (hf : ∀ t, Y < t → HasDerivAt f (deriv f t) t)
    (hf' : ∀ t, Y < t → HasDerivAt (deriv f) (a t * f t) t)
    (hg : ∀ t, Y < t → HasDerivAt g (deriv g t) t)
    (hg' : ∀ t, Y < t → HasDerivAt (deriv g) (a t * g t) t) :
    spectralWronskian f g x = spectralWronskian f g y := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi Y).isPreconnected
  · intro t ht
    exact (spectralWronskian_hasDerivAt (a t) f g t (hf t ht) (hf' t ht)
      (hg t ht) (hg' t ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact (spectralWronskian_hasDerivAt (a t) f g t (hf t ht) (hf' t ht)
      (hg t ht) (hg' t ht)).deriv
  · exact hx
  · exact hy

theorem spectralWronskian_zero_of_finite_energy (a : ℝ → ℂ) (f g : ℝ → ℂ) (Y : ℝ)
    (hf : ∀ t, Y < t → HasDerivAt f (deriv f t) t)
    (hf' : ∀ t, Y < t → HasDerivAt (deriv f) (a t * f t) t)
    (hg : ∀ t, Y < t → HasDerivAt g (deriv g t) t)
    (hg' : ∀ t, Y < t → HasDerivAt (deriv g) (a t * g t) t)
    (henergy : IntegrableOn (fun t : ℝ => ‖deriv f t‖ ^ 2) (Ioi Y))
    (hmass : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2 / t ^ 2) (Ioi Y))
    (hbound : ∀ᶠ t in atTop, ‖g t‖ ≤ 1 ∧ t * ‖deriv g t‖ ≤ 1) :
    ∀ x : ℝ, Y < x → spectralWronskian f g x = 0 := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp hbound
  let U := max B (max Y 1)
  have hUY : Y ≤ U := le_trans (le_max_left Y 1) (le_max_right B (max Y 1))
  have hU1 : 1 ≤ U := le_trans (le_max_right Y 1) (le_max_right B (max Y 1))
  have hUB : B ≤ U := le_max_left B (max Y 1)
  let c := spectralWronskian f g (U + 1)
  have hUc : Y < U + 1 := by linarith
  have hconst (t : ℝ) (ht : Y < t) : spectralWronskian f g t = c :=
    spectralWronskian_eq a f g Y t (U + 1) ht hUc hf hf' hg hg'
  have hsub : Ioi U ⊆ Ioi Y := fun _ ht => hUY.trans_lt ht
  have hi := ((henergy.mono_set hsub).add (hmass.mono_set hsub)).const_mul (2 : ℝ)
  have hc : IntegrableOn (fun _ : ℝ => ‖c‖ ^ 2) (Ioi U) := by
    apply hi.mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one (hU1.trans_lt ht)
      have hb := hB t (hUB.trans ht.le)
      have hd : ‖deriv g t‖ ≤ 1 / t := by
        apply (le_div_iff₀ ht0).mpr
        simpa only [mul_comm] using hb.2
      have hw : ‖spectralWronskian f g t‖ ≤ ‖deriv f t‖ + ‖f t‖ / t := by
        calc
          _ ≤ ‖deriv f t * g t‖ + ‖f t * deriv g t‖ := norm_sub_le _ _
          _ = ‖deriv f t‖ * ‖g t‖ + ‖f t‖ * ‖deriv g t‖ := by rw [norm_mul, norm_mul]
          _ ≤ ‖deriv f t‖ * 1 + ‖f t‖ * (1 / t) :=
            add_le_add (mul_le_mul_of_nonneg_left hb.1 (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
          _ = _ := by ring
      have hs := (sq_le_sq₀ (norm_nonneg (spectralWronskian f g t))
        (add_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) ht0.le))).mpr hw
      have hsq : ‖spectralWronskian f g t‖ ^ 2 ≤
          2 * (‖deriv f t‖ ^ 2 + ‖f t‖ ^ 2 / t ^ 2) := by
        rw [← div_pow]
        nlinarith [sq_nonneg (‖deriv f t‖ - ‖f t‖ / t)]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← hconst t (hUY.trans_lt ht)]
      exact hsq
  have hcz : ‖c‖ ^ 2 = 0 := by
    have hh := (integrableOn_const_iff (by finiteness)).mp hc
    simpa only [Real.volume_Ioi, lt_self_iff_false, or_false, enorm_eq_zero] using hh
  have hc0 : c = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hcz)
  intro x hx
  exact (hconst x hx).trans hc0

theorem spectralNormalODE_eq_mul_of_wronskian_zero (eig : ℂ) (q Y t₀ : ℝ)
    (hY : 0 ≤ Y) (ht₀ : Y < t₀) (f g : ℝ → ℂ)
    (hf : ∀ t, Y < t → HasDerivAt f (deriv f t) t)
    (hf' : ∀ t, Y < t → HasDerivAt (deriv f)
      (((q : ℂ) ^ 2 - eig / (t : ℂ) ^ 2) * f t) t)
    (hg : ∀ t, Y < t → HasDerivAt g (deriv g t) t)
    (hg' : ∀ t, Y < t → HasDerivAt (deriv g)
      (((q : ℂ) ^ 2 - eig / (t : ℂ) ^ 2) * g t) t)
    (hg₀ : g t₀ ≠ 0) (hW : spectralWronskian f g t₀ = 0) :
    ∀ y, Y < y → f y = (f t₀ / g t₀) * g y := by
  let c := f t₀ / g t₀
  have hgfirst : ∀ t, Y < t → HasDerivAt (fun y => c * g y)
      (deriv (fun y => c * g y) t) t := by
    intro t ht
    rw [deriv_const_mul_field]
    exact (hg t ht).const_mul c
  have hgsecond : ∀ t, Y < t → HasDerivAt (deriv (fun y => c * g y))
      (((q : ℂ) ^ 2 - eig / (t : ℂ) ^ 2) * (c * g t)) t := by
    intro t ht
    rw [deriv_const_mul_field']
    convert (hg' t ht).const_mul c using 1
    ring
  have hvalue : f t₀ = c * g t₀ := by dsimp [c]; field_simp
  have hderiv : deriv f t₀ = deriv (fun y => c * g y) t₀ := by
    rw [deriv_const_mul_field]
    have hh : deriv f t₀ * g t₀ = f t₀ * deriv g t₀ := sub_eq_zero.mp hW
    dsimp [c]
    calc
      _ = (deriv f t₀ * g t₀) / g t₀ := by field_simp
      _ = (f t₀ * deriv g t₀) / g t₀ := by rw [hh]
      _ = _ := by ring
  exact fun y hy => spectralNormalODE_unique eig q Y t₀ hY ht₀ f
    (fun y => c * g y) hf hf' hgfirst hgsecond hvalue hderiv hy

theorem spectralNormalODE_finite_energy_classification (ν : ℂ) (hν : ν.re = 0)
    (q Y : ℝ) (hq : 0 < q) (hY : 0 ≤ Y) (f : ℝ → ℂ)
    (hf : ∀ t, Y < t → HasDerivAt f (deriv f t) t)
    (hf' : ∀ t, Y < t → HasDerivAt (deriv f)
      (((q : ℂ) ^ 2 - (1 / 4 - ν ^ 2) / (t : ℂ) ^ 2) * f t) t)
    (henergy : IntegrableOn (fun t : ℝ => ‖deriv f t‖ ^ 2) (Ioi Y))
    (hmass : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2 / t ^ 2) (Ioi Y)) :
    ∃ c : ℂ, ∀ y, Y < y →
      f y = c * ((Real.sqrt y : ℂ) * OAI.CubicEisenstein.schlafliBesselK ν (q * y)) := by
  let g := spectralKBesselWhittaker ν q
  have hg : ∀ t, Y < t → HasDerivAt g (deriv g t) t := by
    intro t ht
    have ht0 := hY.trans_lt ht
    have hd := spectralKBesselWhittaker_hasDerivAt ν q t hq ht0
    rw [← spectralKBesselWhittaker_deriv ν q t hq ht0] at hd
    exact hd
  have hg' : ∀ t, Y < t → HasDerivAt (deriv g)
      (((q : ℂ) ^ 2 - (1 / 4 - ν ^ 2) / (t : ℂ) ^ 2) * g t) t := by
    intro t ht
    exact spectralKBesselWhittaker_deriv_normal_hasDerivAt ν q t hq (hY.trans_lt ht)
  have hbound : ∀ᶠ t in atTop, ‖g t‖ ≤ 1 ∧ t * ‖deriv g t‖ ≤ 1 := by
    have hglim := (spectralKBesselWhittaker_imaginary_tendsto_atTop ν hν q hq).norm
    simp only [norm_zero] at hglim
    have hgdlim := spectralKBesselWhittaker_imaginary_weighted_deriv_tendsto ν hν q hq
    filter_upwards [hglim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hgdlim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht hd
    exact ⟨ht.le, hd.le⟩
  have hW := spectralWronskian_zero_of_finite_energy
    (fun t => (q : ℂ) ^ 2 - (1 / 4 - ν ^ 2) / (t : ℂ) ^ 2) f g Y
    hf hf' hg hg' henergy hmass hbound
  obtain ⟨t₀, _, ht₀, hne⟩ := spectralKBesselWhittaker_exists_ne_zero_above ν
    (by rw [hν]; norm_num) q Y hq
  refine ⟨f t₀ / g t₀, ?_⟩
  intro y hy
  have he := spectralNormalODE_eq_mul_of_wronskian_zero (1 / 4 - ν ^ 2) q Y t₀
    hY ht₀ f g hf hf' hg hg' hne (hW t₀ ht₀) y hy
  simpa only [g, spectralKBesselWhittaker_eq_sqrt ν q y (hY.trans_lt hy).le] using he

end ArtinMatthews
