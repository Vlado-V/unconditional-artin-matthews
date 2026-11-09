module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The four literal contributions of the two positive spectral
brackets, with the source Bessel scale retained. -/

noncomputable section
namespace ArtinMatthews

private theorem sqrt_one_add_le_one_add_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (1+x) ≤ 1+Real.sqrt x := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  nlinarith [Real.sq_sqrt hx,Real.sqrt_nonneg x]

theorem shiftedABL_spectral_brackets_expand {H F r n R Q g : ℝ}
    (hH : 0 ≤ H) (hF : 0 < F) (hr : 0 < r) (hn : 0 < n)
    (hR : 0 < R) (hQ : 0 < Q) (hg : 0 ≤ g) :
    let X := Real.sqrt (R*n)/(Real.sqrt r*Q)
    let G := Real.sqrt (n*g)
    H*F*Real.sqrt r/Q * Real.sqrt (1+R/(r*F)) * Real.sqrt (1+G/(X*r*F)) ≤
      H*F*Real.sqrt r/Q + H*Real.sqrt F*Real.sqrt R/Q +
      H*Real.sqrt F*Real.sqrt (Real.sqrt g)*Real.sqrt (Real.sqrt r)/
        (Real.sqrt Q*Real.sqrt (Real.sqrt R)) +
      H*Real.sqrt (Real.sqrt g)*Real.sqrt (Real.sqrt R)/
        (Real.sqrt Q*Real.sqrt (Real.sqrt r)) := by
  intro X G
  let qR := Real.sqrt (Real.sqrt R)
  let qn := Real.sqrt (Real.sqrt n)
  let qr := Real.sqrt (Real.sqrt r)
  let qg := Real.sqrt (Real.sqrt g)
  let qQ := Real.sqrt Q
  let qF := Real.sqrt F
  let sr := Real.sqrt r
  let a := R/(r*F)
  let b := G/(X*r*F)
  let C := H*F*sr/Q
  have hqR : 0 < qR := by dsimp [qR]; positivity
  have hqn : 0 < qn := by dsimp [qn]; positivity
  have hqr : 0 < qr := by dsimp [qr]; positivity
  have hqQ : 0 < qQ := by dsimp [qQ]; positivity
  have hqF : 0 < qF := by dsimp [qF]; positivity
  have hsr : 0 < sr := by dsimp [sr]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b,G]; positivity
  have hFq : F=qF^2 := (Real.sq_sqrt hF.le).symm
  have hQq : Q=qQ^2 := (Real.sq_sqrt hQ.le).symm
  have hRq : Real.sqrt R=qR^2 := (Real.sq_sqrt (Real.sqrt_nonneg R)).symm
  have hrq : sr=qr^2 := (Real.sq_sqrt (Real.sqrt_nonneg r)).symm
  have hXs : Real.sqrt X=qR*qn/(qr*qQ) := by
    change Real.sqrt (Real.sqrt (R*n)/(Real.sqrt r*Q)) = _
    rw [Real.sqrt_div (Real.sqrt_nonneg (R*n)),Real.sqrt_mul hR.le,
      Real.sqrt_mul (Real.sqrt_nonneg R),Real.sqrt_mul (Real.sqrt_nonneg r)]
  have hGs : Real.sqrt G=qn*qg := by
    change Real.sqrt (Real.sqrt (n*g)) = _
    rw [Real.sqrt_mul hn.le,Real.sqrt_mul (Real.sqrt_nonneg n)]
  have has : Real.sqrt a=Real.sqrt R/(sr*qF) := by
    change Real.sqrt (R/(r*F)) = _
    rw [Real.sqrt_div hR.le,Real.sqrt_mul hr.le]
  have hbs : Real.sqrt b=(qn*qg)/((qR*qn/(qr*qQ))*sr*qF) := by
    change Real.sqrt (G/(X*r*F)) = _
    rw [Real.sqrt_div (by dsimp [G]; positivity),Real.sqrt_mul (mul_pos hX hr).le,
      Real.sqrt_mul hX.le,hXs,hGs]
  have htermA : C*Real.sqrt a=H*qF*Real.sqrt R/Q := by
    rw [has]
    dsimp only [C]
    rw [hFq]
    field_simp [hQ.ne',hsr.ne',hqF.ne']
    <;> ring
  have htermB : C*Real.sqrt b=H*qF*qg*qr/(qQ*qR) := by
    rw [hbs]
    dsimp only [C]
    rw [hFq,hQq]
    field_simp [hqr.ne',hqQ.ne',hqR.ne',hqn.ne',hsr.ne',hqF.ne']
    <;> ring
  have htermAB : C*Real.sqrt a*Real.sqrt b=H*qg*qR/(qQ*qr) := by
    calc
      _ = (C*Real.sqrt b)*Real.sqrt a := by ring
      _ = (H*qF*qg*qr/(qQ*qR))*(Real.sqrt R/(sr*qF)) := by rw [htermB,has]
      _ = _ := by
        rw [hRq,hrq]
        field_simp [hqF.ne',hqQ.ne',hqR.ne',hqr.ne']
        <;> ring
  change C*Real.sqrt (1+a)*Real.sqrt (1+b) ≤ _
  calc
    _ ≤ C*(1+Real.sqrt a)*(1+Real.sqrt b) := mul_le_mul
      (mul_le_mul_of_nonneg_left (sqrt_one_add_le_one_add_sqrt ha) hC)
      (sqrt_one_add_le_one_add_sqrt hb) (Real.sqrt_nonneg _) (by positivity)
    _ = C+C*Real.sqrt a+C*Real.sqrt b+C*Real.sqrt a*Real.sqrt b := by ring
    _ = _ := by rw [htermAB,htermA,htermB]

end ArtinMatthews
