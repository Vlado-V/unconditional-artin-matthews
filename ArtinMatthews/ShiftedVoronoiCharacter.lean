module

public import ArtinMatthews.ShiftedVoronoiSummation
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic


set_option backward.privateInPublic true
@[expose] public section

/-!
# The exact congruence subgroup for the cubic theta nebentypus

For the character χ₋₃, the invariance subgroup at level N is Γ₀(N) ∩ Γ₁(3).
It is not in general Γ₁(N): using the latter would impose an unwarranted
condition d ≡ ±1 (mod N) on the cusp matrix. This file discharges the matrix
membership and sign from N | q and 3 | N. Constructing the actual Hecke theta
as a cusp form on this subgroup remains a separate arithmetic theorem.
-/

noncomputable section
open Complex UpperHalfPlane Set CongruenceSubgroup
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

/-- The kernel of the quadratic nebentypus at a level divisible by three. -/
def cubicThetaKernel (N : ℕ) : Subgroup SL(2, ℤ) := Gamma0 N ⊓ Gamma1 3

instance cubicThetaKernel_finiteIndex (N : ℕ) [NeZero N] : (cubicThetaKernel N).FiniteIndex :=
  inferInstanceAs (Gamma0 N ⊓ Gamma1 3).FiniteIndex

/-- The kernel subgroup always contains translation by one. -/
theorem cubicThetaKernel_periodOne (N : ℕ) :
    (1 : ℝ) ∈ (cubicThetaKernel N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT : ModularGroup.T ∈ cubicThetaKernel N := by
    change ModularGroup.T ∈ Gamma0 N ∧ ModularGroup.T ∈ Gamma1 3
    constructor
    · apply Gamma0_mem.mpr
      simp [ModularGroup.T]
    · apply (Gamma1_mem 3 ModularGroup.T).mpr
      simp [ModularGroup.T]
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

/-- The negative matrix supplies the negative character branch. -/
theorem weightOne_voronoi_neg
    {Γ : Subgroup SL(2, ℤ)} [(Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic]
    (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (γ : SL(2, ℤ)) (hγ : -γ ∈ Γ) (hq : γ 1 0 ≠ 0)
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (a b : ℝ) (ha : 0 < a)
    (hHs : Function.support H ⊆ Icc a b) :
    (∑' n : ℕ, cuspAdditiveCoeff f ((γ 0 0 : ℝ) / γ 1 0) n * H (n : ℝ)) =
      (-1 / (γ 1 0 : ℂ)) * ∑' n : ℕ,
        cuspAdditiveCoeff f (-(γ 1 1 : ℝ) / γ 1 0) n *
          weightOneBesselTransform H ((n : ℝ) / (γ 1 0 : ℝ) ^ 2) := by
  have hn : (-γ) 1 0 ≠ 0 := by simpa using hq
  have hv := weightOne_voronoi_of_smooth_compact f hperiod (-γ) hγ hn H hH a b ha hHs
  simpa [div_neg, neg_div, one_div, neg_mul] using hv

/-- The actual χ₋₃ value, expressed as the quadratic character of the field with three elements. -/
def cubicThetaNebentypus (d : ℤ) : ℂ := (quadraticChar (ZMod 3) (d : ZMod 3) : ℤ)

/-- At a multiple of the actual level, the two possible nebentypus branches
are exactly the two signs of the cusp matrix in the kernel subgroup. -/
theorem cubicThetaKernel_signed_membership (N : ℕ) (hN : 3 ∣ N)
    (γ : SL(2, ℤ)) (hlevel : (N : ℤ) ∣ γ 1 0) :
    (γ ∈ cubicThetaKernel N ∧ cubicThetaNebentypus (γ 1 1) = 1) ∨
      (-γ ∈ cubicThetaKernel N ∧ cubicThetaNebentypus (γ 1 1) = -1) := by
  have hqN : (γ 1 0 : ZMod N) = 0 := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h3N : (3 : ℤ) ∣ N := by exact_mod_cast hN
  have hq3 : (γ 1 0 : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h3N.trans hlevel
  have hdet : (γ 0 0 : ZMod 3) * (γ 1 1 : ZMod 3) = 1 := by
    have hi : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using γ.det_coe
    have hm := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hi
    simpa [hq3] using hm
  have hchoices : ∀ x y : ZMod 3, x * y = 1 →
      (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) := by decide
  rcases hchoices _ _ hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · left
    refine ⟨⟨hqN, ?_⟩, ?_⟩
    · exact (Gamma1_mem 3 γ).mpr ⟨ha, hd, hq3⟩
    · simp [cubicThetaNebentypus, hd]
  · right
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change -γ ∈ Gamma0 N
      apply Gamma0_mem.mpr
      simpa using hqN
    · apply (Gamma1_mem 3 (-γ)).mpr
      simp [ha, hd, hq3]
    · rw [cubicThetaNebentypus, hd]
      have hchar : quadraticChar (ZMod 3) (-1) = -1 := by decide
      rw [hchar]
      norm_num

/-- The character factor in (5.3), with cusp-matrix membership discharged
from its level condition for the correct kernel of χ₋₃. -/
theorem weightOne_voronoi_cubicNebentypus
    (N : ℕ) [NeZero N] (hN : 3 ∣ N) (f : CuspForm (cubicThetaKernel N) 1)
    (γ : SL(2, ℤ)) (hlevel : (N : ℤ) ∣ γ 1 0) (hq : γ 1 0 ≠ 0)
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (a b : ℝ) (ha : 0 < a)
    (hHs : Function.support H ⊆ Icc a b) :
    (∑' n : ℕ, cuspAdditiveCoeff f ((γ 0 0 : ℝ) / γ 1 0) n * H (n : ℝ)) =
      (cubicThetaNebentypus (γ 1 1) / (γ 1 0 : ℂ)) * ∑' n : ℕ,
        cuspAdditiveCoeff f (-(γ 1 1 : ℝ) / γ 1 0) n *
          weightOneBesselTransform H ((n : ℝ) / (γ 1 0 : ℝ) ^ 2) := by
  rcases cubicThetaKernel_signed_membership N hN γ hlevel with ⟨hγ, hψ⟩ | ⟨hγ, hψ⟩
  · rw [hψ]
    exact weightOne_voronoi_of_smooth_compact f (cubicThetaKernel_periodOne N)
      γ hγ hq H hH a b ha hHs
  · rw [hψ]
    exact weightOne_voronoi_neg f (cubicThetaKernel_periodOne N)
      γ hγ hq H hH a b ha hHs

end ArtinMatthews
