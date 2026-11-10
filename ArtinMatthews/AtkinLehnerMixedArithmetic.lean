module

public import ArtinMatthews.AtkinLehnerNormalizer
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Actual mixed-cusp integer matrices before the lower-triangular scaling phase. -/
namespace ArtinMatthews

open Matrix CongruenceSubgroup

def atkinMixedNumerator (r s A B c D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![r*A,B;r*s*c,r*D]

def atkinMixedPreimage (r s a b A B c D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  atkinGammaMatrix r s (r*a*A-s*B) (-b*A+B) (a*c-D) (r*D-s*b*c)

theorem atkinMixedPreimage_det (r s a b A B c D : ℤ) :
    (atkinMixedPreimage r s a b A B c D).det =
      (r*a-s*b)*(r*A*D-s*c*B) := by
  rw [atkinMixedPreimage,atkinGammaMatrix_det]
  ring

theorem atkinMixedPreimage_mul (r s a b A B c D : ℤ) :
    atkinMixedPreimage r s a b A B c D * atkinNumerator r s a b =
      (r*a-s*b) • atkinMixedNumerator r s A B c D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinMixedPreimage,atkinGammaMatrix,atkinNumerator,atkinMixedNumerator,
      Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem atkinMixedForward_det (r s a b A B C D : ℤ) :
    r*(A+s*B)*(s*b*C+a*D)-s*(r*C+D)*(b*A+r*a*B) =
      (r*a-s*b)*(A*D-r*s*B*C) := by ring

theorem atkinMixedForward_mul (r s a b A B C D : ℤ) :
    atkinGammaMatrix r s A B C D * atkinNumerator r s a b =
      atkinMixedNumerator r s (A+s*B) (b*A+r*a*B) (r*C+D) (s*b*C+a*D) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinGammaMatrix,atkinNumerator,atkinMixedNumerator,
      Matrix.mul_apply,Fin.sum_univ_two] <;> ring

def atkinMixedPreimageSL (r s : ℕ) (a b A B c D : ℤ)
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (hdet : (r : ℤ)*A*D-(s : ℤ)*c*B = 1) :
    Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨atkinMixedPreimage r s a b A B c D,by rw [atkinMixedPreimage_det,hab,hdet]; norm_num⟩

theorem atkinMixedPreimageSL_mem (r s : ℕ) (a b A B c D : ℤ)
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (hdet : (r : ℤ)*A*D-(s : ℤ)*c*B = 1) :
    atkinMixedPreimageSL r s a b A B c D hab hdet ∈ Gamma0 (r*s) := by
  rw [Gamma0_mem,ZMod.intCast_zmod_eq_zero_iff_dvd]
  change ((r*s : ℕ) : ℤ) ∣ (r : ℤ)*(s : ℤ)*(a*c-D)
  exact ⟨a*c-D,by push_cast; rfl⟩

/-- A mixed-cusp matrix is constructed inside the literal Gamma0-times-scaling
coset, rather than by asserting membership of an abstract shape. -/
noncomputable def atkinMixedSL {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (A B c D : ℤ)
    (hdet : (r : ℤ)*A*D-(s : ℤ)*c*B = 1) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  atkinRealMap (atkinMixedPreimageSL r s a b A B c D hab hdet) * atkinScaling hr hab

set_option backward.isDefEq.respectTransparency false in
theorem atkinMixedSL_coe {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (A B c D : ℤ)
    (hdet : (r : ℤ)*A*D-(s : ℤ)*c*B = 1) :
    (atkinMixedSL hr hab A B c D hdet : Matrix (Fin 2) (Fin 2) ℝ) =
      (1/Real.sqrt (r : ℝ)) •
        (atkinMixedNumerator r s A B c D).map (fun z : ℤ => (z : ℝ)) := by
  have hi := atkinMixedPreimage_mul (r : ℤ) (s : ℤ) a b A B c D
  rw [hab,one_smul] at hi
  have hm := congrArg (Int.castRingHom ℝ).mapMatrix hi
  simp only [map_mul] at hm
  change (atkinMixedPreimage r s a b A B c D).map (fun z : ℤ => (z : ℝ)) *
    ((1/Real.sqrt (r : ℝ)) • (atkinNumerator r s a b).map (fun z : ℤ => (z : ℝ))) = _
  rw [Matrix.mul_smul]
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => (1/Real.sqrt (r : ℝ)) • M) hm

set_option backward.isDefEq.respectTransparency false in
theorem atkinMixedSL_forward {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (A B C D : ℤ)
    (hdet : A*D-(r : ℤ)*(s : ℤ)*B*C = 1) :
    ∃ hmix : (r : ℤ)*(A+(s : ℤ)*B)*((s : ℤ)*b*C+a*D)-
        (s : ℤ)*((r : ℤ)*C+D)*(b*A+(r : ℤ)*a*B) = 1,
      atkinMixedSL hr hab (A+(s : ℤ)*B) (b*A+(r : ℤ)*a*B)
        ((r : ℤ)*C+D) ((s : ℤ)*b*C+a*D) hmix =
      atkinRealMap (atkinGammaSL r s A B C D hdet) * atkinScaling hr hab := by
  have hmix : (r : ℤ)*(A+(s : ℤ)*B)*((s : ℤ)*b*C+a*D)-
      (s : ℤ)*((r : ℤ)*C+D)*(b*A+(r : ℤ)*a*B) = 1 := by
    rw [atkinMixedForward_det,hab,hdet,mul_one]
  refine ⟨hmix,?_⟩
  apply Subtype.ext
  rw [atkinMixedSL_coe]
  have hi := atkinMixedForward_mul (r : ℤ) (s : ℤ) a b A B C D
  have hm := congrArg (Int.castRingHom ℝ).mapMatrix hi
  simp only [map_mul] at hm
  change _ = (atkinGammaMatrix r s A B C D).map (fun z : ℤ => (z : ℝ)) *
    ((1/Real.sqrt (r : ℝ)) • (atkinNumerator r s a b).map (fun z : ℤ => (z : ℝ)))
  rw [Matrix.mul_smul]
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => (1/Real.sqrt (r : ℝ)) • M) hm.symm

/-- Every actual mixed-cusp matrix has the literal determinant constraint. -/
theorem atkinMixedSL_parameterization {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ Gamma0 (r*s)) :
    ∃ (A B c D : ℤ) (hdet : (r : ℤ)*A*D-(s : ℤ)*c*B = 1),
      atkinMixedSL hr hab A B c D hdet = atkinRealMap γ * atkinScaling hr hab := by
  obtain ⟨A,B,C,D,hdet,rfl⟩ := atkinGammaSL_parameterization γ hγ
  obtain ⟨hmix,heq⟩ := atkinMixedSL_forward hr hab A B C D hdet
  exact ⟨_,_,_,_,hmix,heq⟩

end ArtinMatthews
