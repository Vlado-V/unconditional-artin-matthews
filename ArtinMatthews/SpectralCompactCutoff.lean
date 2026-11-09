module

public import ArtinMatthews.SpectralCoreLocalizationChartCompact
public import Mathlib.Geometry.Manifold.PartitionOfUnity


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine compact smooth cutoffs for arbitrary compact hyperbolic cores. -/

noncomputable section
open Set
open scoped ContDiff

namespace ArtinMatthews

theorem compact_hyperbolic_open_rectangle {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ A a b : ℝ, 0 < a ∧ a ≤ b ∧
      (fun z : UpperHalfPlane => (z.re,z.im)) '' K ⊆ (Ioo (-A) A) ×ˢ (Ioo a b) := by
  have hc : Continuous (fun z : UpperHalfPlane => |z.re|+z.im+1/z.im) :=
    (UpperHalfPlane.continuous_re.abs.add UpperHalfPlane.continuous_im).add
      (continuous_const.div UpperHalfPlane.continuous_im (fun z => z.im_pos.ne'))
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  let L := max C 1
  have hL : 1 ≤ L := le_max_right _ _
  have hpos : 0 < L+1 := by linarith
  have ha : 0 < 1/(L+1) := one_div_pos.mpr hpos
  refine ⟨L+1,1/(L+1),L+1,ha,?_,?_⟩
  · have hh : 1/(L+1) ≤ 1 := (div_le_one hpos).mpr (by linarith)
    linarith
  · rintro _ ⟨z,hz,rfl⟩
    have hn := (le_abs_self (|z.re|+z.im+1/z.im)).trans ((hC z hz).trans (le_max_left C 1))
    change |z.re|+z.im+1/z.im ≤ L at hn
    have hinv : 0 < 1/z.im := one_div_pos.mpr z.im_pos
    have hx : |z.re| < L+1 := by linarith [z.im_pos]
    have hy : z.im < L+1 := by linarith [abs_nonneg z.re]
    have hi : 1/z.im < L+1 := by linarith [abs_nonneg z.re,z.im_pos]
    have hlo : 1/(L+1) < z.im := by
      apply (div_lt_iff₀ hpos).mpr
      have hh := (div_lt_iff₀ z.im_pos).mp hi
      nlinarith
    exact ⟨abs_lt.mp hx,⟨hlo,hy⟩⟩

/-- Mathlib's smooth Urysohn theorem produces the actual cutoff. Its support
lies in a fixed positive-height rectangle and its residual has norm at most one. -/
theorem exists_compact_hyperbolic_cutoff {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ (A a b : ℝ) (φ : SchwartzMap (ℝ × ℝ) ℂ),
      0 < a ∧ a ≤ b ∧ tsupport φ ⊆ spectralPlaneRectangle A a b ∧
      (∀ z ∈ K, φ (z.re,z.im) = 1) ∧
      (∀ p, ‖φ p‖ ≤ 1) ∧ (∀ p, ‖1-φ p‖ ≤ 1) := by
  obtain ⟨A,a,b,ha,hab,hrect⟩ := compact_hyperbolic_open_rectangle hK
  let T := (fun z : UpperHalfPlane => (z.re,z.im)) '' K
  have hT : IsCompact T := hK.image (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)
  obtain ⟨f,hf,hfr,hfs,hfone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_Ioo.prod isOpen_Ioo) hT.isClosed hrect
  have hs : tsupport f ⊆ spectralPlaneRectangle A a b := by
    rw [tsupport,hfs]
    apply closure_minimal (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
    exact (spectralPlaneRectangle_compact A a b).isClosed
  let g : ℝ × ℝ → ℂ := fun p => (f p : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hf
  have hgs : tsupport g ⊆ spectralPlaneRectangle A a b := by
    exact (tsupport_comp_subset (g := Complex.ofReal) (by simp) f).trans hs
  have hgc : HasCompactSupport g :=
    (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) hgs
  let φ : SchwartzMap (ℝ × ℝ) ℂ := hgc.toSchwartzMap hg
  refine ⟨A,a,b,φ,ha,hab,hgs,?_,?_,?_⟩
  · intro z hz
    change (f (z.re,z.im) : ℂ) = 1
    rw [(hfone (z.re,z.im)).mp ⟨z,hz,rfl⟩,Complex.ofReal_one]
  · intro p
    have hp := hfr ⟨p,rfl⟩
    change ‖(f p : ℂ)‖ ≤ 1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp.1]
    exact hp.2
  · intro p
    have hp := hfr ⟨p,rfl⟩
    change ‖1-(f p : ℂ)‖ ≤ 1
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hp.2)]
    linarith [hp.1]

end ArtinMatthews
