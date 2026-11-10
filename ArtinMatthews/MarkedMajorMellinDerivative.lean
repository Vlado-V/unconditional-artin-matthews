module

public import ArtinMatthews.MarkedMajorMellinFamily
public import ArtinMatthews.MarkedMajorOscillatoryDerivatives
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

/-- A parameter slice does not increase the norm of any derivative. -/
theorem majorMellin_slice_derivative_bound (f : ℝ × (ℝ × ℝ) → ℂ)
    (hf : ContDiff ℝ ∞ f) (u : ℝ) (p : ℝ × ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z : ℝ × ℝ => f (u,z)) p‖ ≤
      ‖iteratedFDeriv ℝ n f (u,p)‖ := by
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × (ℝ × ℝ)) := ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)
  let F : ℝ × (ℝ × ℝ) → ℂ := fun z => f ((u,0)+z)
  have hF : ContDiff ℝ ∞ F := hf.comp (contDiff_const.add contDiff_id)
  have he : (fun z : ℝ × ℝ => f (u,z)) = F ∘ L := by funext z; simp [F,L]
  rw [he,L.iteratedFDeriv_comp_right hF p (by simp)]
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (by
    intro z
    simp [L])
  have hn := (iteratedFDeriv ℝ n F (L p)).norm_compContinuousLinearMap_le (fun _ => L)
  have hprod : (∏ _ : Fin n, ‖L‖) ≤ 1 := by
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)
  have H := hn.trans (mul_le_of_le_one_right (norm_nonneg _) hprod)
  simpa only [F,iteratedFDeriv_comp_add_left,L,ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk,add_zero,zero_add] using H

def markedMajorMellinFamilyPhase (p : ℝ × (ℝ × ℝ)) : ℝ :=
  2*Real.pi*markedMajorMellinFamilyArgument p

theorem markedMajorMellinFamilyPhase_contDiff : ContDiff ℝ ∞ markedMajorMellinFamilyPhase :=
  contDiff_const.mul markedMajorMellinFamilyArgument_contDiff

theorem markedMajorMellinKernel_oscillatory (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {X : ℝ} (hX : X ≠ 0) (theta : ℝ) :
    markedMajorMellinKernelFun ρ ρ' ψ X theta = fun p =>
      markedOscillatoryFamily (markedMajorMellinFamilyAmplitude ρ ρ' ψ)
        markedMajorMellinFamilyPhase theta (X⁻¹,p) := by
  funext p
  rw [markedMajorMellinKernel_family ρ ρ' ψ hX]
  unfold markedOscillatoryFamily markedOscillatoryPhase markedRealOscillator
    OAI.Problem337.RealPhase.phase markedMajorMellinFamilyPhase
  congr 2
  push_cast
  ring

theorem markedMajorMellinKernel_compact_derivative_bound (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    (a b R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X ≥ 1, ∀ theta : ℝ, ∀ p ∈ markedMajorMellinSupportBox a b R,
      ‖iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p‖ ≤
        C*(1+|theta|)^n := by
  let K := Set.Icc (0 : ℝ) 1 ×ˢ markedMajorMellinSupportBox a b R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C,hC,hbound⟩ := markedOscillatoryFamily_compact_derivative_bound
    (markedMajorMellinFamilyAmplitude ρ ρ' ψ) markedMajorMellinFamilyPhase
    (markedMajorMellinFamilyAmplitude_contDiff ρ ρ' ψ)
    markedMajorMellinFamilyPhase_contDiff K hK n
  refine ⟨C,hC,fun X hX theta p hp => ?_⟩
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hx : X⁻¹ ∈ Icc (0 : ℝ) 1 := ⟨inv_nonneg.mpr hXpos.le,inv_le_one_of_one_le₀ hX⟩
  rw [markedMajorMellinKernel_oscillatory ρ ρ' ψ hXpos.ne']
  exact (majorMellin_slice_derivative_bound _
    (markedOscillatoryFamily_contDiff _ _ (markedMajorMellinFamilyAmplitude_contDiff ρ ρ' ψ)
      markedMajorMellinFamilyPhase_contDiff theta) _ _ n).trans (hbound theta _ ⟨hx,hp⟩)

end
end ArtinMatthews
