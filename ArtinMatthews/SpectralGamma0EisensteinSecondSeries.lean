module

public import ArtinMatthews.SpectralGamma0EisensteinPlaneTerms
public import ArtinMatthews.SpectralGamma0EisensteinC2
public import ArtinMatthews.SpectralGamma0EisensteinDerivativeBounds
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.MeasureTheory.Covering.Besicovitch


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise summability and identity for the genuine second spatial derivative series. -/
noncomputable section
open Set
namespace ArtinMatthews

theorem gamma0EisensteinPlane_second_summable_rectangle (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (A a b : ℝ) (ha : 0<a) (hab : a≤b) (p : ℝ × ℝ)
    (hp : |p.1|≤A ∧ a≤p.2 ∧ p.2≤b) :
    Summable (fun v : Gamma0EisensteinRows N =>
      fderiv ℝ (fderiv ℝ (gamma0EisensteinPlaneTerm N s v)) p) := by
  have hu : Summable (fun v : Gamma0EisensteinRows N =>
      ((50*‖s‖^2+42*‖s‖)/a^2)*gamma0EisensteinRowMajorant N s A a b ha v) :=
    (gamma0EisensteinRowMajorant_summable N s hs A a b ha).mul_left _
  exact hu.of_norm_bounded
    (f := fun v : Gamma0EisensteinRows N =>
      fderiv ℝ (fderiv ℝ (gamma0EisensteinPlaneTerm N s v)) p)
    (fun v => (gamma0EisensteinPlaneTerm_derivative_majorants N s hs A a b ha hab v p hp).2)

theorem gamma0EisensteinPlane_second_series (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    Summable (fun v : Gamma0EisensteinRows N => fderiv ℝ (fderiv ℝ (gamma0EisensteinPlaneTerm N s v)) p) ∧
    fderiv ℝ (fderiv ℝ (fun q => ∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v q)) p =
      ∑' v : Gamma0EisensteinRows N, fderiv ℝ (fderiv ℝ (gamma0EisensteinPlaneTerm N s v)) p := by
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
  exact ⟨gamma0EisensteinPlane_second_summable_rectangle N s hs A a b ha hab.le p hb,
    ((gamma0EisensteinPlane_tsum_C2_rectangle N s hs A a b ha hab p hm).2 p hm).2⟩

end ArtinMatthews
