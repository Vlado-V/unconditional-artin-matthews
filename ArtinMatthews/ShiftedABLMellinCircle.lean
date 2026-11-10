module

public import ArtinMatthews.ShiftedABLMellinCoefficient
public import ArtinMatthews.ShiftedABLMellinModuli
public import ArtinMatthews.ShiftedABLThetaSignedReassembly
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Exact finite sum and Mellin integral interchange for the original
signed circle block, in its actual `q=Fc` parametrization. -/

noncomputable section
open Complex MeasureTheory Set OAI
open scoped ContDiff BigOperators

namespace ArtinMatthews

/-- The original Kloosterman term at a literal modulus. -/
def shiftedABLMellinKloosterman (q m3 m4 : ℕ) (ρ : ℤ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    shiftedABLThetaRhoKloosterman q m3 m4 ρ

/-- The exact spectral sum for one pair of Mellin heights, with the
sharp signed block restriction carried by the coefficient indices. -/
def shiftedABLMellinSignedSum (χ : SevenEighths.HeckeFamily.Character)
    (D m3 m4 F r L : ℕ) (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) : ℂ :=
  ∑ c ∈ shiftedABLMellinModuli F r L, shiftedABLMellinModulusWeight F L z c/(c : ℂ) *
    ∑ ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter
        (fun ρ => shiftedABLSignedFrequencyIndex ρ = i),
      shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z *
        shiftedABLMellinKloosterman (F*c) m3 m4 ρ

private theorem shiftedABLMellinModuli_mul_mem {F r L c : ℕ}
    (hc : c ∈ shiftedABLMellinModuli F r L) :
    F*c ∈ circleModuli F r L := by
  obtain ⟨q,hq,hqc⟩ := Finset.mem_image.mp hc
  rw [← hqc, Nat.mul_div_cancel' (Finset.mem_filter.mp hq).2.1]
  exact hq

/-- Exact interchange, using the already constructed source kernel
identities for the two dual windows. -/
theorem shiftedABLThetaSignedCircleBlock_eq_mellin
    (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
    (K1 K2 : ℝ) (D m3 m4 F r L : ℕ) (hF : 0 < F) (hL : 0 < L)
    (d : ℕ × ℕ) (i : ℕ × Bool) (b1 b2 : SchwartzMap ℝ ℂ)
    (h1 : ∀ q ∈ circleModuli F r L, ∀ k ∈ shiftedABLDualWindow d.1,
      (spectralDyadicBlock d.1 k : ℂ) *
        weightOneBesselTransform (fun x => W1 (x/K1)) ((k : ℝ)/(q : ℝ)^2) =
          ∫ t : ℝ, shiftedABLMellinDualPhase d.1 k t *
            shiftedABLMellinCirclePhase (3*(L : ℝ)) t q * b1 t)
    (h2 : ∀ q ∈ circleModuli F r L, ∀ k ∈ shiftedABLDualWindow d.2,
      (spectralDyadicBlock d.2 k : ℂ) *
        weightOneBesselTransform (fun x => W2 (x/K2)) ((k : ℝ)/(q : ℝ)^2) =
          ∫ t : ℝ, shiftedABLMellinDualPhase d.2 k t *
            shiftedABLMellinCirclePhase (3*(L : ℝ)) t q * b2 t) :
    let Λ := circleNormalizer (circleModuli F r L) (circleSmoothWeight L)
    let Q : ℝ := 3*(L : ℝ)
    let f (z : ℝ × ℝ) := shiftedABLMellinSignedSum χ D m3 m4 F r L d i z*(b1 z.1*b2 z.2)
    Integrable f ∧
      shiftedABLThetaSignedCircleBlock χ W1 W2 K1 K2 D m3 m4 F r L d i =
        (cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4) / ((Λ : ℂ)*(F : ℂ)*(Q : ℂ))) *
          ∫ z : ℝ × ℝ, f z := by
  intro Λ Q f
  let ψ := cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4)
  let N := ψ/((Λ : ℂ)*(F : ℂ)*(Q : ℂ))
  let R := (shiftedABLDualFrequencies m3 m4 d).filter
    (fun ρ => shiftedABLSignedFrequencyIndex ρ = i)
  let C := shiftedABLMellinModuli F r L
  let u (ρ : ℤ) (c : ℕ) (z : ℝ × ℝ) : ℂ :=
    shiftedABLMellinModulusWeight F L z c/(c : ℂ) *
      (shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z *
        shiftedABLMellinKloosterman (F*c) m3 m4 ρ)*(b1 z.1*b2 z.2)
  let v (ρ : ℤ) (c : ℕ) : ℂ :=
    (circleSmoothWeight L (F*c) : ℂ) *
      ((Q/((F*c : ℕ) : ℝ) : ℝ) : ℂ)/(c : ℂ) *
        shiftedABLMellinKloosterman (F*c) m3 m4 ρ
  let w (ρ : ℤ) (c : ℕ) (z : ℝ × ℝ) : ℂ :=
    shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z *
      shiftedABLMellinKernelFactor Q (F*c : ℕ) b1 b2 z
  have huw (ρ : ℤ) (c : ℕ) : u ρ c = fun z => v ρ c*w ρ c z := by
    funext z
    simp only [u,v,w,shiftedABLMellinModulusWeight,shiftedABLMellinKernelFactor,
      circleSmoothWeight,Nat.cast_mul,Q]
    ring
  have hw (ρ : ℤ) (c : ℕ) (hc : c ∈ C) := shiftedABLThetaRhoCoefficient_eq_mellin
    χ W1 W2 K1 K2 Q D m3 m4 (F*c) d ρ b1 b2
      (h1 _ (shiftedABLMellinModuli_mul_mem hc)) (h2 _ (shiftedABLMellinModuli_mul_mem hc))
  have hu (ρ : ℤ) (c : ℕ) (hc : c ∈ C) : Integrable (u ρ c) := by
    rw [huw]
    exact (hw ρ c hc).1.const_mul _
  have hpoint : (fun z : ℝ × ℝ => ∑ ρ ∈ R, ∑ c ∈ C, u ρ c z) = f := by
    funext z
    rw [Finset.sum_comm]
    unfold f shiftedABLMellinSignedSum
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    simp only [Finset.mul_sum,Finset.sum_mul,u,R]
  refine ⟨hpoint ▸ integrable_finsetSum R
    (fun ρ _ => integrable_finsetSum C (fun c hc => hu ρ c hc)), ?_⟩
  have hF0 : (F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hF.ne'
  have hQ0 : Q ≠ 0 := by
    change 3*(L : ℝ) ≠ 0
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have hone (ρ : ℤ) (c : ℕ) (hc : c ∈ C) :
      ((circleSmoothWeight L (F*c) : ℂ) *
        shiftedABLThetaRhoNormalized χ W1 W2 K1 K2 D m3 m4 (F*c) d ρ)/(Λ : ℂ) =
        N*(∫ z : ℝ × ℝ, u ρ c z) := by
    have hqmem := shiftedABLMellinModuli_mul_mem hc
    have hq : 0 < F*c := (by omega : 0 < 3*L).trans_le
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hqmem).1).1
    have hc0 : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mul_pos_left hq).ne'
    let : NeZero (F*c) := ⟨hq.ne'⟩
    simp only [shiftedABLThetaRhoNormalized,dite_eq_right hq.ne', (hw ρ c hc).2,
      huw, integral_const_mul, N,v,shiftedABLMellinKloosterman,ψ]
    by_cases hΛ : (Λ : ℂ) = 0
    · simp [hΛ]
    dsimp only [w]
    push_cast
    field_simp [hΛ,hF0,hc0,Complex.ofReal_ne_zero.mpr hQ0] <;> ring
  change (∑ ρ ∈ R, (∑ q ∈ circleModuli F r L, (circleSmoothWeight L q : ℂ) *
      shiftedABLThetaRhoNormalized χ W1 W2 K1 K2 D m3 m4 q d ρ)/(Λ : ℂ)) =
    N*(∫ z : ℝ × ℝ, f z)
  simp_rw [shiftedABLMellinModuli_reindex F r L, Finset.sum_div]
  calc
    _ = ∑ ρ ∈ R, ∑ c ∈ C, N*(∫ z : ℝ × ℝ, u ρ c z) := by
      apply Finset.sum_congr rfl
      intro ρ _
      exact Finset.sum_congr rfl (fun c hc => hone ρ c hc)
    _ = N*(∑ ρ ∈ R, ∑ c ∈ C, ∫ z : ℝ × ℝ, u ρ c z) := by simp only [Finset.mul_sum]
    _ = _ := by
      rw [← hpoint, integral_finsetSum R
        (fun ρ _ => integrable_finsetSum C (fun c hc => hu ρ c hc))]
      congr 1
      exact Finset.sum_congr rfl (fun ρ _ => (integral_finsetSum C (fun c hc => hu ρ c hc)).symm)

end ArtinMatthews
