module

public import ArtinMatthews.SpectralGamma0CompactMass
public import ArtinMatthews.SpectralFiniteCoverIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The two literal cusp strips covering a modular tail. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem modular_tail_two_strip_cover (N : ℕ) [NeZero N] (Y : ℝ) :
    {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ Y < z.im} ⊆
      hyperbolicCuspStrip (N : ℝ) Y ∪
        (fun z : UpperHalfPlane => ModularGroup.T • z) ⁻¹' hyperbolicCuspStrip (N : ℝ) Y := by
  intro z hz
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (NeZero.one_le : 1 ≤ N)
  have hx := abs_le.mp hz.1.2
  by_cases hp : 0 < z.re
  · exact Or.inl ⟨⟨hp,by linarith [hx.2]⟩,hz.2⟩
  · right
    change (ModularGroup.T • z).re ∈ Ioc 0 (N : ℝ) ∧ Y < (ModularGroup.T • z).im
    rw [ModularGroup.re_T_smul,ModularGroup.im_T_smul]
    exact ⟨⟨by linarith [hx.1],by linarith [le_of_not_gt hp]⟩,hz.2⟩

end ArtinMatthews
