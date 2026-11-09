module

public import ArtinMatthews.SpectralPositiveSmoothDensity


set_option backward.privateInPublic true
@[expose] public section

/-! The compact interval quotient used by the exponential-polynomial
approximation. Endpoint continuity follows from actual compact positive
support, via the compact image under x |-> exp(-x). -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralKLExponentialQuotient (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  if 0 < t ∧ t < 1 then f (-Real.log t)/((t*(1-t) : ℝ) : ℂ) else 0

theorem spectralKLExponentialQuotient_tsupport (f : ℝ → ℂ) (hfc : HasCompactSupport f) :
    tsupport (spectralKLExponentialQuotient f) ⊆
      (fun x : ℝ => Real.exp (-x)) '' tsupport f := by
  have hK : IsCompact ((fun x : ℝ => Real.exp (-x)) '' tsupport f) :=
    hfc.isCompact.image (by fun_prop)
  unfold tsupport
  apply closure_minimal _ hK.isClosed
  intro t ht
  have hp : 0 < t ∧ t < 1 := by
    by_contra hn
    exact (Function.mem_support.mp ht) (by simp [spectralKLExponentialQuotient,hn])
  have hft : f (-Real.log t) ≠ 0 := by
    intro h
    apply Function.mem_support.mp ht
    simp [spectralKLExponentialQuotient,hp,h]
  refine ⟨-Real.log t,subset_tsupport f hft,?_⟩
  dsimp only
  rw [neg_neg,Real.exp_log hp.1]

theorem spectralKLExponentialQuotient_support_interval (f : ℝ → ℂ)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    tsupport (spectralKLExponentialQuotient f) ⊆ Ioo (0 : ℝ) 1 := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := spectralKLExponentialQuotient_tsupport f hfc ht
  exact ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos (hfp hx))⟩

theorem spectralKLExponentialQuotient_continuous (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Continuous (spectralKLExponentialQuotient f) := by
  have hOn : ContinuousOn (spectralKLExponentialQuotient f) (Ioo (0 : ℝ) 1) := by
    intro t ht
    have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht.1.ne'
    have hn : ContinuousAt (fun s : ℝ => f (-Real.log s)) t :=
      (hf.continuousAt (x := -Real.log t)).comp_of_eq
        (show ContinuousAt (fun s : ℝ => -Real.log s) t from hlog.neg) rfl
    have hden : ((t*(1-t) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (mul_ne_zero ht.1.ne' (sub_pos.mpr ht.2).ne')
    have hRat : ContinuousAt (fun s : ℝ => f (-Real.log s)/((s*(1-s) : ℝ) : ℂ)) t :=
      hn.div (by fun_prop) hden
    have heq : spectralKLExponentialQuotient f =ᶠ[𝓝 t]
        (fun s : ℝ => f (-Real.log s)/((s*(1-s) : ℝ) : ℂ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact ite_eq_left hs
    exact (hRat.congr heq.symm).continuousWithinAt
  exact hOn.continuous_of_tsupport_subset isOpen_Ioo
    (spectralKLExponentialQuotient_support_interval f hfc hfp)

theorem spectralKLExponentialQuotient_hasCompactSupport (f : ℝ → ℂ) (hfc : HasCompactSupport f) :
    HasCompactSupport (spectralKLExponentialQuotient f) := by
  have hK : IsCompact ((fun x : ℝ => Real.exp (-x)) '' tsupport f) :=
    hfc.isCompact.image (by fun_prop)
  exact hK.of_isClosed_subset (isClosed_tsupport _) (spectralKLExponentialQuotient_tsupport f hfc)

theorem spectralKLExponentialAnchor_factor (x : ℝ) :
    spectralKLExponentialAnchor x = Real.exp (-x)*(1-Real.exp (-x)) := by
  unfold spectralKLExponentialAnchor
  rw [show -2*x = -x+-x by ring,Real.exp_add]
  ring

theorem spectralKLExponentialQuotient_recover (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    (spectralKLExponentialAnchor x : ℂ)*spectralKLExponentialQuotient f (Real.exp (-x)) = f x := by
  have hr : 0 < Real.exp (-x) ∧ Real.exp (-x) < 1 :=
    ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)⟩
  have hq : (spectralKLExponentialAnchor x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (spectralKLExponentialAnchor_pos hx).ne'
  unfold spectralKLExponentialQuotient
  rw [ite_eq_left hr,Real.log_exp,neg_neg,← spectralKLExponentialAnchor_factor]
  field_simp

end ArtinMatthews
