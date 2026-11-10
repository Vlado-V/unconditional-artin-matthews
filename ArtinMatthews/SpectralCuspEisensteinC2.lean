module

public import ArtinMatthews.SpectralCuspEisensteinDerivativeBounds
public import ArtinMatthews.SpectralLocalC2Series
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine local C² regularity of the convergent Eisenstein series. -/
noncomputable section
open Set Filter
open scoped ContDiff MatrixGroups
namespace ArtinMatthews

theorem cuspEisensteinRowPlane_tsum_C2_rectangle (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re)
    (A a b : ℝ) (ha : 0<a) (hab : a<b) (p₀ : ℝ × ℝ)
    (hp₀ : p₀ ∈ Ioo (-A) A ×ˢ Ioo a b) :
    ContDiffOn ℝ 2 (fun p => ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v p)
      (Ioo (-A) A ×ˢ Ioo a b) ∧
    ∀ p ∈ Ioo (-A) A ×ˢ Ioo a b,
      fderiv ℝ (fun q => ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v q) p =
        ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, fderiv ℝ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v) p ∧
      fderiv ℝ (fderiv ℝ (fun q => ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, cuspEisensteinRowPlaneTerm N r₀ a₀ s v q)) p =
        ∑' v : Gamma0CuspEisensteinRows N r₀ a₀, fderiv ℝ (fderiv ℝ (cuspEisensteinRowPlaneTerm N r₀ a₀ s v)) p := by
  let U := Ioo (-A) A ×ˢ Ioo a b
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hUc : IsPreconnected U := (convex_Ioo (-A) A).prod (convex_Ioo a b) |>.isPreconnected
  have hbox (p : ℝ × ℝ) (hp : p ∈ U) : |p.1|≤A ∧ a≤p.2 ∧ p.2≤b :=
    ⟨abs_le.mpr ⟨hp.1.1.le,hp.1.2.le⟩,hp.2.1.le,hp.2.2.le⟩
  have hΩ : U ⊆ {p : ℝ × ℝ | 0<p.2} := fun p hp => ha.trans hp.2.1
  let u := cuspEisensteinRowMajorant N r₀ a₀ s A a b ha
  have hu : Summable u := cuspEisensteinRowMajorant_summable N r₀ a₀ s hs A a b ha
  have hf (v : Gamma0CuspEisensteinRows N r₀ a₀) : ContDiffOn ℝ 2 (cuspEisensteinRowPlaneTerm N r₀ a₀ s v) U :=
    ((cuspEisensteinRowPlaneTerm_contDiffOn N r₀ a₀ s v).of_le (by simp)).mono hΩ
  have hd (v : Gamma0CuspEisensteinRows N r₀ a₀) (p : ℝ × ℝ) (hp : p ∈ U) :=
    cuspEisensteinRowPlaneTerm_derivative_majorants N r₀ a₀ s hs A a b ha hab.le v p (hbox p hp)
  have hp₀y : 0<p₀.2 := hΩ hp₀
  have hsum : Summable (fun v : Gamma0CuspEisensteinRows N r₀ a₀ => cuspEisensteinRowPlaneTerm N r₀ a₀ s v p₀) :=
    (cuspEisensteinRowTerm_summable N r₀ a₀ s hs ⟨⟨p₀.1,p₀.2⟩,hp₀y⟩).congr
      (fun v => (cuspEisensteinRowPlaneTerm_eq N r₀ a₀ s v p₀ hp₀y).symm)
  exact spectralLocalC2Series _ hU hUc hf
    (fun v => (5*‖s‖/a)*u v) (fun v => ((50*‖s‖^2+42*‖s‖)/a^2)*u v)
    (hu.mul_left _) (hu.mul_left _) (fun v p hp => (hd v p hp).1)
    (fun v p hp => (hd v p hp).2) p₀ hp₀ hsum

theorem cuspEisensteinRowPlaneSum_contDiffOn (N : ℕ) (r₀ a₀ : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re) :
    ContDiffOn ℝ 2 (cuspEisensteinRowPlaneSum N r₀ a₀ s) {p : ℝ × ℝ | 0<p.2} := by
  intro p hp
  change 0 < p.2 at hp
  let A := |p.1|+1
  let a := p.2/2
  let b := p.2+1
  have ha : 0<a := by dsimp [a]; positivity
  have hab : a<b := by dsimp [a,b]; linarith
  have hmem : p ∈ Ioo (-A) A ×ˢ Ioo a b := by
    constructor
    · constructor <;> dsimp [A] <;> linarith [le_abs_self p.1,neg_abs_le p.1]
    · constructor <;> dsimp [a,b] <;> linarith
  have hraw := (cuspEisensteinRowPlane_tsum_C2_rectangle N r₀ a₀ s hs A a b ha hab p hmem).1
  have hfull : ContDiffOn ℝ 2 (cuspEisensteinRowPlaneSum N r₀ a₀ s) (Ioo (-A) A ×ˢ Ioo a b) :=
    contDiffOn_const.mul hraw
  exact ((hfull p hmem).contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hmem)).contDiffWithinAt

end ArtinMatthews
