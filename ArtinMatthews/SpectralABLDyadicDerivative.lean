module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
open Set Finset
open scoped ContDiff
noncomputable section

/-- Multiplying by a fixed smooth coefficient in the variable `x / X`
costs a constant independent of the spatial scale. -/
theorem spectralDyadic_scaled_mul_deriv_bound (φ : ℝ → ℂ)
    (hφ : ContDiffOn ℝ ∞ φ (Ioi (0 : ℝ))) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X b M : ℝ) (f : ℝ → ℂ),
      0 < X → 0 ≤ b → b ≤ X → 0 ≤ M → ContDiff ℝ ∞ f →
      (∀ j ≤ J, ∀ x ∈ Icc X (2*X), b^j*‖iteratedDeriv j f x‖ ≤ M) →
      ∀ j ≤ J, ∀ x ∈ Icc X (2*X),
        b^j*‖iteratedDeriv j (fun y => φ (y/X)*f y) x‖ ≤ C*M := by
  have hI : Icc (1 : ℝ) 2 ⊆ Ioi 0 := fun x hx => zero_lt_one.trans_le hx.1
  have hcont (i : ℕ) : ContinuousOn (iteratedDeriv i φ) (Icc (1 : ℝ) 2) := by
    refine ((hφ.continuousOn_iteratedDerivWithin (m := i) (by simp)
      (uniqueDiffOn_Ioi 0)).mono hI).congr ?_
    intro x hx
    exact (iteratedDerivWithin_of_isOpen isOpen_Ioi (hI hx)).symm
  choose B hB using fun i => (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    (hcont i)
  let D : ℝ := 1 + ∑ i ∈ range (J+1), max (B i) 0
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hB' (i : ℕ) (hi : i ≤ J) (x : ℝ) (hx : x ∈ Icc (1 : ℝ) 2) :
      ‖iteratedDeriv i φ x‖ ≤ D := by
    have hle : max (B i) 0 ≤ ∑ k ∈ range (J+1), max (B k) 0 :=
      single_le_sum (fun k _ => le_max_right (B k) 0) (mem_range.mpr (by omega))
    exact (hB i x hx).trans ((le_max_left _ _).trans (hle.trans (by dsimp [D]; linarith)))
  refine ⟨2^J*D,by positivity,?_⟩
  intro X b M f hX hb hbX hM hf hF j hj x hx
  let P : ℝ → ℂ := fun y => φ (y/X)
  have hxpos : 0 < x := hX.trans_le hx.1
  have hx' : x/X ∈ Icc (1 : ℝ) 2 :=
    ⟨(le_div_iff₀ hX).mpr (by simpa using hx.1), (div_le_iff₀ hX).mpr hx.2⟩
  have hP : ContDiffAt ℝ j P x := by
    apply ((hφ (x/X) (hI hx')).contDiffAt (isOpen_Ioi.mem_nhds (hI hx'))).of_le (by simp) |>.comp x
    fun_prop
  have hscale (i : ℕ) (hi : i ≤ J) : b^i*‖iteratedDeriv i P x‖ ≤ D := by
    have hX' : 0 < X⁻¹ := inv_pos.mpr hX
    have hxmem : x ∈ Ioi (0 : ℝ) := hxpos
    have hm : MapsTo (X⁻¹ * ·) (Ioi (0 : ℝ)) (Ioi 0) :=
      fun _ hu => mul_pos hX' hu
    have h := iteratedDerivWithin_comp_const_smul (n := i) hxmem
      (uniqueDiffOn_Ioi 0) (hφ.of_le (by simp)) X⁻¹ hm
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioi hxmem,
      iteratedDerivWithin_of_isOpen isOpen_Ioi (hm hxpos)] at h
    have hder : iteratedDeriv i P x = (X⁻¹)^i • iteratedDeriv i φ (x/X) := by
      simpa only [P,div_eq_mul_inv,mul_comm] using h
    rw [hder,norm_smul,Real.norm_of_nonneg (pow_nonneg hX'.le _),← mul_assoc,← mul_pow]
    have hb' : b*X⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hX, one_mul]
      exact hbX
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by positivity) hb')).trans
      (hB' i hi _ hx')
  change b^j*‖iteratedDeriv j (fun y => P y*f y) x‖ ≤ _
  rw [iteratedDeriv_fun_mul hP (hf.contDiffAt.of_le (by simp))]
  calc
    _ ≤ b^j*(∑ i ∈ range (j+1), ‖(j.choose i : ℂ)*iteratedDeriv i P x*
      iteratedDeriv (j-i) f x‖) := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hb _)
    _ = ∑ i ∈ range (j+1), b^j*‖(j.choose i : ℂ)*iteratedDeriv i P x*
      iteratedDeriv (j-i) f x‖ := by rw [mul_sum]
    _ ≤ ∑ i ∈ range (j+1), (j.choose i : ℝ)*(D*M) := by
      apply sum_le_sum
      intro i hi
      have hij : i ≤ j := by have := mem_range.mp hi; omega
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      calc
        _ = (j.choose i : ℝ)*((b^i*‖iteratedDeriv i P x‖)*
            (b^(j-i)*‖iteratedDeriv (j-i) f x‖)) := by
          have hp : b^j = b^i*b^(j-i) := by rw [← pow_add,Nat.add_sub_of_le hij]
          rw [hp]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul (hscale i (hij.trans hj)) (hF (j-i) (by omega) x hx) (by positivity) hD.le)
          (by positivity)
    _ = 2^j*(D*M) := by
      rw [← sum_mul]
      have heq : (∑ i ∈ range (j+1), (j.choose i : ℝ)) = 2^j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [heq]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (by positivity)

end
end ArtinMatthews
