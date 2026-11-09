module

public import ArtinMatthews.SpectralEisensteinProfileGradientSum
public import ArtinMatthews.SpectralEisensteinCutoffRegularity


set_option backward.privateInPublic true
@[expose] public section

/-! Positive row profiles bound the mass and hyperbolic gradient of actual
height profiles. The proof keeps the common half factor and local finiteness. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0CuspHeightProfile_continuous_of_zero_low (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (f : ℝ → ℂ) (hf : Continuous f) {ε : ℝ} (hε : 0<ε)
    (hlow : ∀ t≤ε, f t=0) : Continuous (gamma0CuspHeightProfile N a f) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨T,hT⟩ := gamma0CuspHeightProfile_locally_finite_sum N a f hε hlow z
  have hc : Continuous (fun w : UpperHalfPlane => (1/2:ℂ)*
      ∑ v ∈ T, f (cuspEisensteinNormalizedHeight N 1 a v w)) :=
    continuous_const.mul (continuous_finsetSum T
      (fun v _ => hf.comp (cuspEisensteinNormalizedHeight_continuous N 1 a v)))
  exact hc.continuousAt.congr_of_eventuallyEq hT

theorem gamma0CuspHeightProfile_norm_of_nonneg (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (b : ℝ → ℝ) (hb : ∀ t, 0≤b t) {ε : ℝ} (hε : 0<ε)
    (hlow : ∀ t≤ε, b t=0) (z : UpperHalfPlane) :
    ‖gamma0CuspHeightProfile N a (fun t => (b t:ℂ)) z‖ =
      (1/2:ℝ)*∑' v : Gamma0CuspEisensteinRows N 1 a, b (cuspEisensteinNormalizedHeight N 1 a v z) := by
  rw [gamma0CuspHeightProfile_eq_tsum N a _ hε
    (fun t ht => by simp only [hlow t ht,Complex.ofReal_zero]),norm_mul]
  rw [← Complex.ofReal_tsum,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (fun _ => hb _))]
  norm_num

theorem gamma0CuspHeightProfile_nonneg_summable (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (b : ℝ → ℝ) {ε : ℝ} (hε : 0<ε)
    (hlow : ∀ t≤ε, b t=0) (z : UpperHalfPlane) :
    Summable (fun v : Gamma0CuspEisensteinRows N 1 a => b (cuspEisensteinNormalizedHeight N 1 a v z)) := by
  apply summable_of_hasFiniteSupport
  apply (cuspEisensteinHeight_compact_finite N 1 a hε isCompact_singleton).subset
  intro v hv
  refine ⟨z,mem_singleton z,?_⟩
  by_contra hn
  exact hv (hlow _ (le_of_lt (lt_of_not_ge hn)))

theorem gamma0CuspHeightProfile_norm_le_of_majorant (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (f : ℝ → ℂ) (b : ℝ → ℝ) (hb : ∀ t, 0≤b t)
    {ε : ℝ} (hε : 0<ε) (hflow : ∀ t≤ε, f t=0) (hblow : ∀ t≤ε, b t=0)
    (hle : ∀ t>0, ‖f t‖≤b t) (z : UpperHalfPlane) :
    ‖gamma0CuspHeightProfile N a f z‖ ≤ ‖gamma0CuspHeightProfile N a (fun t => (b t:ℂ)) z‖ := by
  let H := cuspEisensteinNormalizedHeight N 1 a
  have hs := gamma0CuspHeightProfile_nonneg_summable N a b hε hblow z
  have hle' (v : Gamma0CuspEisensteinRows N 1 a) : ‖f (H v z)‖≤b (H v z) :=
    hle _ (cuspEisensteinNormalizedHeight_pos N 1 a v z)
  have hn := hs.of_nonneg_of_le (fun v => norm_nonneg (f (H v z))) hle'
  rw [gamma0CuspHeightProfile_eq_tsum N a f hε hflow z,norm_mul,
    gamma0CuspHeightProfile_norm_of_nonneg N a b hb hε hblow z]
  rw [show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hle' hs))
    (by norm_num)

theorem gamma0CuspHeightProfile_gradient_norm_le_of_majorant (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (b : ℝ → ℝ) (hb : ∀ t, 0≤b t)
    {ε : ℝ} (hε : 0<ε) (hflow : ∀ t≤ε, f t=0) (hblow : ∀ t≤ε, b t=0)
    {C : ℝ} (hle : ∀ t : ℝ, 0<t → ‖(t:ℂ)*deriv f t‖≤C*b t) (z : UpperHalfPlane) :
    ‖h2SectionGradient (gamma0CuspHeightProfile N a f) z‖ ≤
      C*‖gamma0CuspHeightProfile N a (fun t => (b t:ℂ)) z‖ := by
  let H := cuspEisensteinNormalizedHeight N 1 a
  let g (v : Gamma0CuspEisensteinRows N 1 a) :=
    h2SectionGradient (cuspEisensteinProfileTerm N 1 a f v) z
  have hs := (gamma0CuspHeightProfile_nonneg_summable N a b hε hblow z).mul_left C
  have hle' (v : Gamma0CuspEisensteinRows N 1 a) : ‖g v‖≤C*b (H v z) := by
    have hp := cuspEisensteinNormalizedHeight_pos N 1 a v z
    dsimp only [g]
    rw [cuspEisensteinProfileTerm_gradient_norm N 1 a f hf v z]
    have he := hle (H v z) hp
    rwa [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp] at he
  have hn := hs.of_nonneg_of_le (fun v => norm_nonneg (g v)) hle'
  rw [gamma0CuspHeightProfile_gradient_tsum N a f hf hε hflow z,norm_smul,
    gamma0CuspHeightProfile_norm_of_nonneg N a b hb hε hblow z]
  rw [show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num]
  calc
    _ ≤ (1/2:ℝ)*(∑' v : Gamma0CuspEisensteinRows N 1 a, C*b (H v z)) :=
      mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hle' hs))
        (by norm_num)
    _ = _ := by rw [tsum_mul_left];ring

end ArtinMatthews
