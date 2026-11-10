module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
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

/-! The mass Gram operator of a genuine faithful compact form inclusion. -/
noncomputable section
open scoped InnerProductSpace
namespace ArtinMatthews

theorem spectralFormMassGram_norm_ratio_range (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (hab : a≤b) (μ : ℂ) (h : μ*(b:ℂ)^(2:ℕ)=(a:ℂ)^(2:ℕ)) :
    ∃ t : ℝ, 0<t ∧ t≤1 ∧ μ=(t:ℂ) := by
  have hden : (b:ℂ)^(2:ℕ)≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hb.ne')
  refine ⟨a^2/b^2,div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb),?_,?_⟩
  · exact (div_le_one (sq_pos_of_pos hb)).mpr ((sq_le_sq₀ ha.le hb.le).mpr hab)
  · simp only [Complex.ofReal_div,Complex.ofReal_pow]
    exact (eq_div_iff hden).mpr h

section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralFormMassGram (J : V →L[ℂ] H) : V →L[ℂ] V := J.adjoint.comp J

theorem spectralFormMassGram_inner (J : V →L[ℂ] H) (v u : V) :
    inner ℂ v (spectralFormMassGram J u)=inner ℂ (J v) (J u) :=
  J.adjoint_inner_right v (J u)

theorem spectralFormMassGram_compact (J : V →L[ℂ] H) (hJ : IsCompactOperator J) :
    IsCompactOperator (spectralFormMassGram J) := hJ.clm_comp J.adjoint

theorem spectralFormMassGram_selfAdjoint (J : V →L[ℂ] H) : IsSelfAdjoint (spectralFormMassGram J) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [spectralFormMassGram,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

theorem spectralFormMassGram_injective (J : V →L[ℂ] H) (hJ : Function.Injective J) :
    Function.Injective (spectralFormMassGram J) :=
  (J.adjoint_comp_self_injective_iff).mpr hJ

theorem spectralFormMassGram_eigenvalue_range (J : V →L[ℂ] H) (hJ : Function.Injective J)
    (hJn : ‖J‖≤1) (u : V) (hu : u≠0) (μ : ℂ)
    (he : spectralFormMassGram J u=μ • u) : ∃ t : ℝ, 0<t ∧ t≤1 ∧ μ=(t:ℂ) := by
  have hJu : J u≠0 := fun hz => hu (hJ (hz.trans J.map_zero.symm))
  have h := spectralFormMassGram_inner J u u
  rw [he,inner_smul_right,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at h
  have hun : 0<‖u‖ := norm_pos_iff.mpr hu
  have hnum : ‖J u‖≤‖u‖ := (J.le_opNorm u).trans
    (mul_le_of_le_one_left (norm_nonneg _) hJn)
  exact spectralFormMassGram_norm_ratio_range ‖J u‖ ‖u‖ (norm_pos_iff.mpr hJu) hun hnum μ h

end
end ArtinMatthews
