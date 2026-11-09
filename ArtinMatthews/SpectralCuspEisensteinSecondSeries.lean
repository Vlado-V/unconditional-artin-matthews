module

public import ArtinMatthews.SpectralCuspEisensteinC2


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise summability and identity for the genuine second spatial derivative series. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspEisensteinRowPlane_second_summable_rectangle (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re)
    (A a b : ℝ) (ha : 0<a) (hab : a≤b) (p : ℝ × ℝ)
    (hp : |p.1|≤A ∧ a≤p.2 ∧ p.2≤b) :
    Summable (fun v : Gamma0CuspEisensteinRows N r₀ a₀ =>
      fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v)) p) := by
  have hu : Summable (fun v : Gamma0CuspEisensteinRows N r₀ a₀ =>
      ((50*‖s‖^2+42*‖s‖)/a^2)*cuspEisensteinRowMajorant N r₀ a₀ s A a b ha v) :=
    (cuspEisensteinRowMajorant_summable N r₀ a₀ s hs A a b ha).mul_left _
  exact hu.of_norm_bounded
    (f := fun v : Gamma0CuspEisensteinRows N r₀ a₀ =>
      fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v)) p)
    (fun v => (cuspEisensteinRowPlaneTerm_derivative_majorants N r₀ a₀ s hs A a b ha hab v p hp).2)

theorem cuspEisensteinRowPlane_second_series (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    Summable (fun v : Gamma0CuspEisensteinRows N r₀ a₀ => fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v)) p) ∧
    fderiv ℝ (fderiv ℝ (fun q => ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v q)) p =
      ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v)) p := by
  let A := |p.1|+1
  let a := p.2/2
  let b := p.2+1
  have ha : 0<a := by dsimp [a]; positivity
  have hab : a<b := by dsimp [a,b]; linarith
  have hm : p ∈ Ioo (-A) A ×ˢ Ioo a b := by
    constructor
    · constructor <;> dsimp [A] <;> linarith [le_abs_self p.1,neg_abs_le p.1]
    · constructor <;> dsimp [a,b] <;> linarith
  have hb : |p.1|≤A ∧ a≤p.2 ∧ p.2≤b :=
    ⟨by dsimp [A]; linarith,hm.2.1.le,hm.2.2.le⟩
  exact ⟨cuspEisensteinRowPlane_second_summable_rectangle N r₀ a₀ s hs A a b ha hab.le p hb,
    ((cuspEisensteinRowPlane_tsum_C2_rectangle N r₀ a₀ s hs A a b ha hab p hm).2 p hm).2⟩

end ArtinMatthews
