module

public import ArtinMatthews.AtkinLehnerMixedPhase
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual mixed-cusp residues classify the integer-translation double cosets. -/
namespace ArtinMatthews

open Matrix

set_option backward.isDefEq.respectTransparency false in
theorem realTranslations_entries (l k : ℤ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (realTranslation (l : ℝ)*γ*realTranslation (k : ℝ)) 0 0 = γ 0 0+(l : ℝ)*γ 1 0 ∧
    (realTranslation (l : ℝ)*γ*realTranslation (k : ℝ)) 1 0 = γ 1 0 ∧
    (realTranslation (l : ℝ)*γ*realTranslation (k : ℝ)) 1 1 = γ 1 1+γ 1 0*(k : ℝ) := by
  simp [realTranslation,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,
    Matrix.vecMul,dotProduct,Fin.sum_univ_two,add_comm]

theorem realTranslations_double_coset_iff {c : ℝ} (hc : c ≠ 0)
    (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ : γ 1 0 = c) (hδ : δ 1 0 = c) :
    (∃ l k : ℤ, δ 0 0 = γ 0 0+c*(l : ℝ) ∧ δ 1 1 = γ 1 1+c*(k : ℝ)) ↔
      ∃ l k : ℤ, δ = realTranslation (l : ℝ)*γ*realTranslation (k : ℝ) := by
  constructor
  · rintro ⟨l,k,hA,hD⟩
    let θ := realTranslation (l : ℝ)*γ*realTranslation (k : ℝ)
    obtain ⟨hθA,hθC,hθD⟩ := realTranslations_entries l k γ
    have hA' : θ 0 0 = δ 0 0 := by rw [hθA,hγ,hA]; ring
    have hC' : θ 1 0 = c := hθC.trans hγ
    have hD' : θ 1 1 = δ 1 1 := by rw [hθD,hγ,hD]
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
    obtain ⟨hA,_hC,hD⟩ := realTranslations_entries l k γ
    exact ⟨l,k,by rw [hA,hγ]; ring,by rw [hD,hγ]⟩

/-- The finite `A,D mod sc` representatives in the mixed kernel are exactly
the genuine double cosets at lower-left entry `s*sqrt(r)*c`. -/
theorem atkinMixed_residue_eq_iff_double_coset {r s c : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hc : 0 < c) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (A₁ B₁ D₁ A₂ B₂ D₂ : ℤ)
    (h₁ : (r : ℤ)*A₁*D₁-(s : ℤ)*(c : ℤ)*B₁ = 1)
    (h₂ : (r : ℤ)*A₂*D₂-(s : ℤ)*(c : ℤ)*B₂ = 1) :
    (((A₁ : ZMod (s*c)),(D₁ : ZMod (s*c))) = ((A₂ : ZMod (s*c)),(D₂ : ZMod (s*c)))) ↔
      ∃ l k : ℤ, atkinMixedSL hr hab A₂ B₂ c D₂ h₂ =
        realTranslation (l : ℝ)*atkinMixedSL hr hab A₁ B₁ c D₁ h₁*realTranslation (k : ℝ) := by
  let t := Real.sqrt (r : ℝ)
  let q := (s : ℝ)*t*(c : ℝ)
  have ht : t ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hr)).ne'
  have hq : q ≠ 0 := (mul_pos (mul_pos (by exact_mod_cast hs)
    (Real.sqrt_pos.mpr (by exact_mod_cast hr))) (by exact_mod_cast hc)).ne'
  have hg₁ := atkinMixedSL_lower hr hab A₁ B₁ c D₁ h₁
  have hg₂ := atkinMixedSL_lower hr hab A₂ B₂ c D₂ h₂
  obtain ⟨hA₁,hD₁⟩ := atkinMixedSL_diagonal hr hab A₁ B₁ c D₁ h₁
  obtain ⟨hA₂,hD₂⟩ := atkinMixedSL_diagonal hr hab A₂ B₂ c D₂ h₂
  rw [← realTranslations_double_coset_iff hq _ _ hg₁ hg₂]
  rw [Prod.mk.injEq,ZMod.intCast_eq_intCast_iff,ZMod.intCast_eq_intCast_iff]
  constructor
  · rintro ⟨hA,hD⟩
    obtain ⟨l,hl⟩ := hA.dvd
    obtain ⟨k,hk⟩ := hD.dvd
    have hlR := congrArg (fun z : ℤ => (z : ℝ)) hl
    have hkR := congrArg (fun z : ℤ => (z : ℝ)) hk
    push_cast at hlR hkR
    refine ⟨l,k,?_,?_⟩
    · rw [hA₁,hA₂]
      dsimp [q,t]
      linear_combination Real.sqrt (r : ℝ)*hlR
    · rw [hD₁,hD₂]
      dsimp [q,t]
      linear_combination Real.sqrt (r : ℝ)*hkR
  · rintro ⟨l,k,hA,hD⟩
    rw [hA₁,hA₂] at hA
    rw [hD₁,hD₂] at hD
    have hlR : (A₂ : ℝ)-(A₁ : ℝ) = ((s*c : ℕ) : ℝ)*(l : ℝ) := by
      apply mul_left_cancel₀ ht
      dsimp [q,t] at hA ⊢
      push_cast
      linear_combination hA
    have hkR : (D₂ : ℝ)-(D₁ : ℝ) = ((s*c : ℕ) : ℝ)*(k : ℝ) := by
      apply mul_left_cancel₀ ht
      dsimp [q,t] at hD ⊢
      push_cast
      linear_combination hD
    constructor
    · apply Int.modEq_iff_dvd.mpr
      exact ⟨l,by exact_mod_cast hlR⟩
    · apply Int.modEq_iff_dvd.mpr
      exact ⟨k,by exact_mod_cast hkR⟩

end ArtinMatthews
