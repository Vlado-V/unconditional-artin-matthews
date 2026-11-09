module

public import ArtinMatthews.SpectralJLogProfile
public import ArtinMatthews.SpectralJLogSturm


set_option backward.privateInPublic true
@[expose] public section

/-! Exact conjugation of the physical Bessel Sturm operator by the
positive logarithmic coordinate, with support preserved through every
iterate. -/
namespace ArtinMatthews
open Set Filter
open SourceSturm
open scoped Topology ContDiff
noncomputable section

theorem spectralJLogSturm_tsupport (a : ℝ) (g : ℝ → ℂ) :
    tsupport (spectralJLogSturm a g) ⊆ tsupport g := by
  apply closure_minimal _ isClosed_closure
  intro v hv
  by_contra hn
  have h₀ : g v = 0 := image_eq_zero_of_notMem_tsupport hn
  have h₁ : deriv g v = 0 := deriv_of_notMem_tsupport hn
  have h₂ : deriv (deriv g) v = 0 :=
    deriv_of_notMem_tsupport (fun h => hn (tsupport_deriv_subset h))
  exact hv (by simp only [spectralJLogSturm, h₀, h₂, mul_zero, add_zero])

theorem spectralJLogSturm_iterate_tsupport (a : ℝ) (n : ℕ) (g : ℝ → ℂ) :
    tsupport (((spectralJLogSturm a)^[n]) g) ⊆ tsupport g := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (spectralJLogSturm_tsupport a _).trans ih

theorem spectralJLogProfile_sturm_pos {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    sturmD (spectralJLogProfile g a) x =
      spectralJLogProfile (spectralJLogSturm a g) a x := by
  have hDx := sturmD_div_eq
    ((spectralJLogProfile_contDiffAt_pos hg ha hx).of_le (by simp)) hx
  rw [spectralJLogProfile_flux_deriv hg ha hx, spectralJLogProfile, if_pos hx] at hDx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have heq := (div_eq_iff hxC).mp hDx
  have hpot : (a : ℂ)^2*(Real.exp (2*Real.log (x/a)) : ℂ) = (x : ℂ)^2 := by
    have hr : a^2*Real.exp (2*Real.log (x/a)) = x^2 := by
      rw [show 2*Real.log (x/a) = Real.log (x/a)+Real.log (x/a) by ring,
        Real.exp_add, Real.exp_log (div_pos hx ha)]
      field_simp [ha.ne'] <;> ring
    exact_mod_cast hr
  rw [heq, spectralJLogProfile, if_pos hx, spectralJLogSturm, spectralJLogPotential]
  calc
    _ = deriv (deriv g) (Real.log (x/a)) + (x : ℂ)^2*g (Real.log (x/a)) := by
      field_simp [hxC] <;> ring
    _ = _ := by rw [← hpot]; ring

theorem spectralJLogProfile_sturm {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    {a α β : ℝ} (ha : 0 < a) (hs : tsupport g ⊆ Icc α β) :
    sturmD (spectralJLogProfile g a) = spectralJLogProfile (spectralJLogSturm a g) a := by
  funext x
  by_cases hx : 0 < x
  · exact spectralJLogProfile_sturm_pos hg ha hx
  · have hn : x ∉ tsupport (spectralJLogProfile g a) :=
      fun h => hx (spectralJLogProfile_positive_tsupport ha hs h)
    have hz : sturmD (spectralJLogProfile g a) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hn (sturmD_tsupport _ h))
    simp only [hz, spectralJLogProfile, if_neg hx]

theorem spectralJLogProfile_sturm_iterate (n : ℕ) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) {a α β : ℝ} (ha : 0 < a) (hs : tsupport g ⊆ Icc α β) :
    ((sturmD^[n]) (spectralJLogProfile g a)) =
      spectralJLogProfile (((spectralJLogSturm a)^[n]) g) a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    exact spectralJLogProfile_sturm (spectralJLogSturm_iterate_smooth a n hg) ha
      ((spectralJLogSturm_iterate_tsupport a n g).trans hs)

end
end ArtinMatthews
