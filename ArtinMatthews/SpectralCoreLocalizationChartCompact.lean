module

public import ArtinMatthews.SpectralCoreLocalizationCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! A compact positive coordinate set is an actual compact hyperbolic chart. -/

namespace ArtinMatthews
noncomputable section

open Set

theorem spectralCoreChart_compact_of_positive {S : Set (ℝ × ℝ)}
    (hS : IsCompact S) (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    IsCompact {z : UpperHalfPlane | (z.re,z.im) ∈ S} := by
  let lift : ℝ × ℝ → UpperHalfPlane := fun p =>
    UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p)
  have hpos (p : ℝ × ℝ) (hp : p ∈ S) : 0 < (Complex.equivRealProdCLM.symm p).im := by
    simpa [Complex.equivRealProdCLM_symm_apply] using hpositive hp
  have hc : ContinuousOn lift S := by
    intro p hp
    exact (ContinuousAt.comp (f := fun q : ℝ × ℝ => Complex.equivRealProdCLM.symm q)
      (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) (hpos p hp)).continuousAt
      Complex.equivRealProdCLM.symm.continuous.continuousAt).continuousWithinAt
  have he : lift '' S = {z : UpperHalfPlane | (z.re,z.im) ∈ S} := by
    ext z
    constructor
    · rintro ⟨p,hp,rfl⟩
      have hpair : ((lift p).re,(lift p).im) = p := by
        change Complex.equivRealProdCLM ((lift p : UpperHalfPlane) : ℂ) = p
        simp only [lift, UpperHalfPlane.ofComplex_apply_of_im_pos (hpos p hp)]
        exact Complex.equivRealProdCLM.apply_symm_apply p
      change ((lift p).re,(lift p).im) ∈ S
      rwa [hpair]
    · intro hz
      refine ⟨(z.re,z.im),hz,?_⟩
      have hz' : Complex.equivRealProdCLM.symm (z.re,z.im) = (z : ℂ) :=
        Complex.equivRealProdCLM.symm_apply_apply (z : ℂ)
      simp only [lift,hz',UpperHalfPlane.ofComplex_apply]
  rw [← he]
  exact hS.image_of_continuousOn hc

theorem spectralCoreChart_compact (A a b : ℝ) (ha : 0 < a) :
    IsCompact {z : UpperHalfPlane | (z.re,z.im) ∈ spectralPlaneRectangle A a b} :=
  spectralCoreChart_compact_of_positive (spectralPlaneRectangle_compact A a b)
    (fun _ hp => ha.trans_le hp.2.1)

end
end ArtinMatthews
