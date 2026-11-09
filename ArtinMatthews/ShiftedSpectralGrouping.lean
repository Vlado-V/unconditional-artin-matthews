module

public import ArtinMatthews.ShiftedConvolutionCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Exact frequency grouping of the finite dual sum, using the same
coefficient sequence as the proved convolution norm estimate. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

def shiftedSpectralFrequencies (S T : Finset ℕ) (m3 m4 : ℕ) : Finset ℤ :=
  (S ×ˢ T).image (fun k => (m4 : ℤ)*k.2-(m3 : ℤ)*k.1)

theorem shiftedSpectral_grouped (S T : Finset ℕ) (m3 m4 D : ℕ)
    (a b : ℕ → ℂ) (F : ℤ → ℂ) :
    (∑ k1∈S, ∑ k2∈T,
      if (m3^2*k1 : ZMod D)=(m4^2*k2 : ZMod D) then
        a k1*b k2*F ((m4 : ℤ)*k2-(m3 : ℤ)*k1) else 0) =
      ∑ r∈shiftedSpectralFrequencies S T m3 m4,
        shiftedConvolutionCoeff S T m3 m4 D a b r*F r := by
  classical
  symm
  unfold shiftedConvolutionCoeff
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k1 hk1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k2 hk2
  let r0 : ℤ := (m4 : ℤ)*k2-(m3 : ℤ)*k1
  have hr : r0∈shiftedSpectralFrequencies S T m3 m4 :=
    Finset.mem_image.mpr ⟨(k1,k2),Finset.mem_product.mpr ⟨hk1,hk2⟩,rfl⟩
  rw [Finset.sum_eq_single r0]
  · by_cases h : (m3^2*k1 : ZMod D)=(m4^2*k2 : ZMod D) <;> simp [r0,h]
  · intro r _hr hne
    have hne' : (m4 : ℤ)*k2-(m3 : ℤ)*k1≠r := Ne.symm hne
    simp only [hne',false_and,ite_false,zero_mul]
  · exact fun h => (h hr).elim

end ArtinMatthews
