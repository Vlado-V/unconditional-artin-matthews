module

public import ArtinMatthews.SpectralEisensteinRegularMatching


set_option backward.privateInPublic true
@[expose] public section

/-! The actual regular matching parameters fill a punctured neighborhood
of each point. This follows from finite truncated spectral windows and
the actual nonzero matching determinant. -/
noncomputable section
open Set Filter Topology
namespace ArtinMatthews

theorem eisensteinSpectralParameter_eq_iff (u v : ℂ) :
    u*(1-u)=v*(1-v) ↔ u=v ∨ u=1-v := by
  constructor
  · intro h
    have h0 : (u-v)*(u-(1-v))=0 := by linear_combination -h
    exact (mul_eq_zero.mp h0).imp sub_eq_zero.mp sub_eq_zero.mp
  · rintro (rfl | rfl)
    · rfl
    · ring

theorem gamma0EisensteinMatchingRegular_eventually (N : ℕ) [NeZero N] (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s, gamma0EisensteinMatchingRegular N w := by
  let ζ (w : ℂ) := w*(1-w)
  let E : Set ℂ := {z | z∈(gamma0EisensteinMatchingForm N).exceptional ∧ ‖z‖≤‖ζ s‖+1}
  have hfinite : E.Finite :=
    (gamma0EisensteinMatchingForm N).exceptional_finite_norm_le (‖ζ s‖+1) (by positivity)
  have hc : Continuous ζ := by unfold ζ;fun_prop
  have hnζ : Tendsto ζ (𝓝 s) (𝓝 (ζ s)) := hc.continuousAt
  have hnn : Tendsto (fun w => ‖ζ w‖) (𝓝 s) (𝓝 ‖ζ s‖) := hnζ.norm
  have hcut : (E\{ζ s})ᶜ∈𝓝 (ζ s) :=
    (hfinite.sdiff.isClosed.isOpen_compl).mem_nhds (by simp)
  have hcut' : ∀ᶠ w in 𝓝 s, ζ w∉E\{ζ s} := hnζ.eventually hcut
  have hnorm : ∀ᶠ w in 𝓝 s, ‖ζ w‖<‖ζ s‖+1 :=
    hnn.eventually (eventually_lt_nhds (by linarith : ‖ζ s‖<‖ζ s‖+1))
  have hreflect : ∀ᶠ w in 𝓝[≠] s,w≠1-s := by
    by_cases he : s=1-s
    · filter_upwards [(self_mem_nhdsWithin : ({s}:Set ℂ)ᶜ∈𝓝[≠] s)] with w hw
      intro h
      exact hw (mem_singleton_iff.mpr (h.trans he.symm))
    · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (by simpa only [mem_compl_iff,mem_singleton_iff] using he))
  filter_upwards [nhdsWithin_le_nhds hcut',nhdsWithin_le_nhds hnorm,
    (self_mem_nhdsWithin : ({s}:Set ℂ)ᶜ∈𝓝[≠] s),hreflect,
    gamma0EisensteinMatchingMatrix_det_eventually_ne_zero N s] with w hw hn hws hwr hd
  refine ⟨?_,hd⟩
  intro he
  have hmem : ζ w∈E := ⟨he,hn.le⟩
  have heq : ζ w=ζ s := by
    by_contra h
    exact hw ⟨hmem,by simpa only [mem_singleton_iff] using h⟩
  exact (eisensteinSpectralParameter_eq_iff w s).mp heq |>.elim
    (fun h => hws (mem_singleton_iff.mpr h)) hwr

end ArtinMatthews
