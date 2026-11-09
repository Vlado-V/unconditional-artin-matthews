module

public import ArtinMatthews.SpectralGamma0CuspPeriod
public import ArtinMatthews.SpectralCuspMass


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete finite modular cover of an unbounded cusp period strip. -/

noncomputable section
open Set
open scoped MatrixGroups

namespace ArtinMatthews

/-- Above height one, translating the real part into [-1/2,1/2] puts the point
in the actual standard modular region. -/
theorem cusp_strip_modular_translation (N : ℕ) {z : UpperHalfPlane}
    (hz : z ∈ hyperbolicCuspStrip (N : ℝ) 1) :
    ∃ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), ModularGroup.T ^ (-k) • z ∈ ModularGroup.fd := by
  classical
  let k : ℤ := ⌊z.re + 1 / 2⌋
  have hkle : (k : ℝ) ≤ z.re + 1 / 2 := Int.floor_le _
  have hklt : z.re + 1 / 2 < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hk0 : 0 ≤ k := Int.floor_nonneg.mpr (by linarith [hz.1.1])
  have hkN : k ≤ (N : ℤ) := by
    have h : (k : ℝ) < (N : ℝ) + 1 := by linarith [hz.1.2]
    have hi : k < (N : ℤ) + 1 := by exact_mod_cast h
    omega
  refine ⟨k, Finset.mem_Icc.mpr ⟨hk0, hkN⟩, ?_⟩
  constructor
  · simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      ModularGroup.im_T_zpow_smul]
    nlinarith [hz.2, sq_nonneg (ModularGroup.T ^ (-k) • z).re]
  · rw [ModularGroup.re_T_zpow_smul, Int.cast_neg, abs_le]
    constructor <;> linarith

/-- The unbounded width-N strip is covered by at most N+1 integer translates
of the actual modular region. -/
theorem cusp_strip_modular_cover (N : ℕ) :
    hyperbolicCuspStrip (N : ℝ) 1 ⊆
      ⋃ k ∈ Finset.Icc (0 : ℤ) (N : ℤ),
        (fun z : UpperHalfPlane => ModularGroup.T ^ (-k) • z) ⁻¹' ModularGroup.fd := by
  intro z hz
  obtain ⟨k, hk, h⟩ := cusp_strip_modular_translation N hz
  exact mem_iUnion₂.mpr ⟨k, hk, h⟩

end ArtinMatthews
