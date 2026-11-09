module

public import ArtinMatthews.SpectralPeterssonPhysicalCauchy


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute integrability and finite linearity of the original
Petersson pairing follow from the actual physical L2 profiles. -/
noncomputable section
open MeasureTheory UpperHalfPlane
open scoped InnerProductSpace ComplexConjugate BigOperators

namespace ArtinMatthews

theorem spectralPeterssonHilbertProfile_inner (k : ℕ) (F G : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) :
    ⟪spectralPeterssonHilbertProfile k F z, spectralPeterssonHilbertProfile k G z⟫_ℂ =
      UpperHalfPlane.petersson (k : ℤ) F G z := by
  let p := z.im^((k : ℝ)/2)
  have hp : p*p = z.im^k := by
    dsimp only [p]
    rw [← Real.rpow_add z.im_pos,show (k : ℝ)/2+(k : ℝ)/2=k by ring,Real.rpow_natCast]
  rw [RCLike.inner_apply]
  unfold spectralPeterssonHilbertProfile UpperHalfPlane.petersson
  simp only [map_mul,Complex.conj_ofReal,zpow_natCast]
  calc
    _ = conj (F z)*G z*((p : ℂ)*(p : ℂ)) := by dsimp only [p]; ring
    _ = _ := by rw [← Complex.ofReal_mul,hp,Complex.ofReal_pow]

theorem gamma0PeterssonPhysical_pair_integrable (N k : ℕ) (F G : UpperHalfPlane → ℂ)
    (hF : MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N)))
    (hG : MemLp (spectralPeterssonHilbertProfile k G) 2 (volume.restrict (gamma0InteriorRegion N))) :
    IntegrableOn (fun z => UpperHalfPlane.petersson (k : ℤ) F G z) (gamma0InteriorRegion N) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
    (hF.toLp (spectralPeterssonHilbertProfile k F)) (hG.toLp (spectralPeterssonHilbertProfile k G))
  apply h.congr
  filter_upwards [hF.coeFn_toLp,hG.coeFn_toLp] with z hf hg
  rw [hf,hg,spectralPeterssonHilbertProfile_inner]

theorem gamma0PeterssonInner_finset_left {ι : Type*} (N k : ℕ) (t : Finset ι)
    (α : ι → ℂ) (F : ι → UpperHalfPlane → ℂ) (G : UpperHalfPlane → ℂ)
    (hF : ∀ i ∈ t, IntegrableOn (fun z => UpperHalfPlane.petersson (k : ℤ) (F i) G z)
      (gamma0InteriorRegion N)) :
    gamma0PeterssonInner N k (fun z => ∑ i ∈ t, α i*F i z) G =
      ∑ i ∈ t, conj (α i)*gamma0PeterssonInner N k (F i) G := by
  classical
  have he (z : UpperHalfPlane) :
      UpperHalfPlane.petersson (k : ℤ) (fun z => ∑ i ∈ t, α i*F i z) G z =
        ∑ i ∈ t, conj (α i)*UpperHalfPlane.petersson (k : ℤ) (F i) G z := by
    simp only [UpperHalfPlane.petersson,map_sum,map_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold gamma0PeterssonInner
  simp_rw [he]
  rw [integral_finsetSum t (fun i hi => (hF i hi).const_mul _)]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_const_mul _ _

end ArtinMatthews
