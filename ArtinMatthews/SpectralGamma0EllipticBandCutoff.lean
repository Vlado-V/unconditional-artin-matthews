module

public import ArtinMatthews.SpectralGamma0EllipticBand
public import ArtinMatthews.SpectralCompactCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Actual compact smooth cutoffs with a full two-cell band plateau. -/
noncomputable section
open Set
open scoped ContDiff
namespace ArtinMatthews

theorem exists_spectralEllipticBand_cutoff {w c d : ℝ}
    (hw : 0 ≤ w) (hc : 0 < c) (hcd : c ≤ d) :
    ∃ (A a b : ℝ) (φ : SchwartzMap (ℝ × ℝ) ℂ),
      0 < a ∧ a ≤ b ∧ tsupport φ ⊆ spectralPlaneRectangle A a b ∧
      (∀ p ∈ spectralEllipticBand w c d, φ p = 1) ∧ a ≤ c := by
  let A := w+1
  let a := c/2
  let b := d+1
  let K : Set (ℝ × ℝ) := Icc 0 w ×ˢ Icc c d
  have hK : IsClosed K := isClosed_Icc.prod isClosed_Icc
  have hKU : K ⊆ Ioo (-A) A ×ˢ Ioo a b := by
    intro p hp
    change (-A < p.1 ∧ p.1 < A) ∧ (a < p.2 ∧ p.2 < b)
    dsimp [K, A, a, b] at *
    constructor
    · constructor
      · linarith [hp.1.1]
      · linarith [hp.1.2]
    · constructor
      · linarith [hp.2.1]
      · linarith [hp.2.2]
  obtain ⟨f,hf,_,hfs,hfone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_Ioo.prod isOpen_Ioo) hK hKU
  have hs : tsupport f ⊆ spectralPlaneRectangle A a b := by
    rw [tsupport,hfs]
    apply closure_minimal (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
    exact (spectralPlaneRectangle_compact A a b).isClosed
  let g : ℝ × ℝ → ℂ := fun p => (f p : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hf
  have hgs : tsupport g ⊆ spectralPlaneRectangle A a b :=
    (tsupport_comp_subset (g := Complex.ofReal) (by simp) f).trans hs
  have hgc : HasCompactSupport g :=
    (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) hgs
  let φ : SchwartzMap (ℝ × ℝ) ℂ := hgc.toSchwartzMap hg
  refine ⟨A,a,b,φ,by dsimp [a]; linarith,by dsimp [a,b]; linarith,hgs,?_,?_⟩
  · intro p hp
    change (f p : ℂ) = 1
    rw [(hfone p).mp ⟨⟨hp.1.1.le,hp.1.2⟩,hp.2⟩,Complex.ofReal_one]
  · dsimp [a]
    linarith

end ArtinMatthews
