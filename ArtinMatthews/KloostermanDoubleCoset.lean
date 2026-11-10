module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Exact upper-unipotent double-coset classification at a fixed nonzero modulus. -/
namespace ArtinMatthews

open Matrix

def integerTranslation (k : ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1,k;0,1],by simp [Matrix.det_fin_two]⟩

set_option backward.isDefEq.respectTransparency false in
theorem integerTranslation_entries (l k : ℤ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (integerTranslation l * γ * integerTranslation k) 0 0 = γ 0 0+l*γ 1 0 ∧
    (integerTranslation l * γ * integerTranslation k) 1 0 = γ 1 0 ∧
    (integerTranslation l * γ * integerTranslation k) 1 1 = γ 1 1+γ 1 0*k := by
  simp [integerTranslation,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,
    Matrix.vecMul,dotProduct,Fin.sum_univ_two,add_comm]

/-- At a fixed nonzero lower-left entry, upper and lower diagonal residues
classify the actual left/right integer-translation double cosets. -/
theorem integerTranslation_double_coset_iff {c : ℤ} (hc : c ≠ 0)
    (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ 1 0 = c) (hδ : δ 1 0 = c) :
    (Int.ModEq c (γ 0 0) (δ 0 0) ∧ Int.ModEq c (γ 1 1) (δ 1 1)) ↔
      ∃ l k : ℤ, δ = integerTranslation l * γ * integerTranslation k := by
  constructor
  · rintro ⟨hA,hD⟩
    obtain ⟨l,hl⟩ := hA.dvd
    obtain ⟨k,hk⟩ := hD.dvd
    let θ := integerTranslation l * γ * integerTranslation k
    obtain ⟨hθA,hθC,hθD⟩ := integerTranslation_entries l k γ
    have hA' : θ 0 0 = δ 0 0 := by rw [hθA,hγ]; nlinarith
    have hC' : θ 1 0 = c := hθC.trans hγ
    have hD' : θ 1 1 = δ 1 1 := by rw [hθD,hγ]; nlinarith
    have hB' : θ 0 1 = δ 0 1 := by
      have ht := θ.prop
      have hd := δ.prop
      rw [Matrix.det_fin_two,hA',hC',hD'] at ht
      rw [Matrix.det_fin_two,hδ] at hd
      apply mul_right_cancel₀ hc
      nlinarith
    refine ⟨l,k,?_⟩
    change δ = θ
    ext i j
    fin_cases i <;> fin_cases j
    · exact hA'.symm
    · exact hB'.symm
    · exact hδ.trans hC'.symm
    · exact hD'.symm
  · rintro ⟨l,k,rfl⟩
    obtain ⟨hA,_hC,hD⟩ := integerTranslation_entries l k γ
    constructor
    · apply Int.modEq_iff_dvd.mpr
      refine ⟨l,?_⟩
      rw [hA,hγ]
      ring
    · apply Int.modEq_iff_dvd.mpr
      refine ⟨k,?_⟩
      rw [hD,hγ]
      ring

end ArtinMatthews
