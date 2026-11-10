module

public import ArtinMatthews.SpectralGamma0EisensteinPlaneTerms
public import ArtinMatthews.SpectralGamma0EisensteinDerivativeBounds
public import ArtinMatthews.SpectralLocalC2Series
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.MeasureTheory.Covering.Besicovitch


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine local C² regularity of the convergent Eisenstein series. -/
noncomputable section
open Set Filter
open scoped ContDiff
namespace ArtinMatthews

theorem gamma0EisensteinPlane_tsum_C2_rectangle (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (A a b : ℝ) (ha : 0<a) (hab : a<b) (p₀ : ℝ × ℝ)
    (hp₀ : p₀ ∈ Ioo (-A) A ×ˢ Ioo a b) :
    ContDiffOn ℝ 2 (fun p => ∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v p)
      (Ioo (-A) A ×ˢ Ioo a b) ∧
    ∀ p ∈ Ioo (-A) A ×ˢ Ioo a b,
      fderiv ℝ (fun q => ∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v q) p =
        ∑' v : Gamma0EisensteinRows N, fderiv ℝ (gamma0EisensteinPlaneTerm N s v) p ∧
      fderiv ℝ (fderiv ℝ (fun q => ∑' v : Gamma0EisensteinRows N, gamma0EisensteinPlaneTerm N s v q)) p =
        ∑' v : Gamma0EisensteinRows N, fderiv ℝ (fderiv ℝ (gamma0EisensteinPlaneTerm N s v)) p := by
  let U := Ioo (-A) A ×ˢ Ioo a b
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hUc : IsPreconnected U := (convex_Ioo (-A) A).prod (convex_Ioo a b) |>.isPreconnected
  have hbox (p : ℝ × ℝ) (hp : p ∈ U) : |p.1|≤A ∧ a≤p.2 ∧ p.2≤b :=
    ⟨abs_le.mpr ⟨hp.1.1.le,hp.1.2.le⟩,hp.2.1.le,hp.2.2.le⟩
  have hΩ : U ⊆ {p : ℝ × ℝ | 0<p.2} := fun p hp => ha.trans hp.2.1
  let u := gamma0EisensteinRowMajorant N s A a b ha
  have hu : Summable u := gamma0EisensteinRowMajorant_summable N s hs A a b ha
  have hf (v : Gamma0EisensteinRows N) : ContDiffOn ℝ 2 (gamma0EisensteinPlaneTerm N s v) U :=
    ((gamma0EisensteinPlaneTerm_contDiffOn N s v).of_le (by simp)).mono hΩ
  have hd (v : Gamma0EisensteinRows N) (p : ℝ × ℝ) (hp : p ∈ U) :=
    gamma0EisensteinPlaneTerm_derivative_majorants N s hs A a b ha hab.le v p (hbox p hp)
  have hp₀y : 0<p₀.2 := hΩ hp₀
  have hsum : Summable (fun v : Gamma0EisensteinRows N => gamma0EisensteinPlaneTerm N s v p₀) :=
    (gamma0EisensteinSummand_summable N s hs ⟨⟨p₀.1,p₀.2⟩,hp₀y⟩).congr
      (fun v => (gamma0EisensteinPlaneTerm_eq N s v p₀ hp₀y).symm)
  exact spectralLocalC2Series _ hU hUc hf
    (fun v => (5*‖s‖/a)*u v) (fun v => ((50*‖s‖^2+42*‖s‖)/a^2)*u v)
    (hu.mul_left _) (hu.mul_left _) (fun v p hp => (hd v p hp).1)
    (fun v p hp => (hd v p hp).2) p₀ hp₀ hsum

theorem gamma0EisensteinPlaneSum_contDiffOn (N : ℕ) (s : ℂ) (hs : 1<s.re) :
    ContDiffOn ℝ 2 (gamma0EisensteinPlaneSum N s) {p : ℝ × ℝ | 0<p.2} := by
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
  have hraw := (gamma0EisensteinPlane_tsum_C2_rectangle N s hs A a b ha hab p hmem).1
  have hfull : ContDiffOn ℝ 2 (gamma0EisensteinPlaneSum N s) (Ioo (-A) A ×ˢ Ioo a b) :=
    contDiffOn_const.mul hraw
  exact ((hfull p hmem).contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hmem)).contDiffWithinAt

end ArtinMatthews
