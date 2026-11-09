module

public import ArtinMatthews.MarkedPhysicalLocalizedMoment


set_option backward.privateInPublic true
@[expose] public section

/-! The physical moment is exactly the original constant-mass trace on
vectors one on every list at one position. No list normalization occurs. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

theorem markedPSD_quadratic_real_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (r : ℝ) (f : ι → ℂ) :
    markedQuadraticForm B ((r:ℂ) • f)=r^2*markedQuadraticForm B f := by
  simp_rw [markedQuadraticForm_spectral B hB.isHermitian,Matrix.mulVec_smul,
    Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def markedPhysicalUnnormalizedPositionVector {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (z : Z) :
    MarkedPhysicalState P M Z → ℂ := fun s => if s.1.1=z then 1 else 0

theorem markedPhysicalPositionMoment_eq_original_mass
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ) (hV : ∀ j,0≤V j)
    (A : Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ) (r : ℕ) :
    markedPhysicalPositionMoment P M Z V A r =
      markedPhysicalMass V M * ∑ z : Z, markedQuadraticForm ((A*Aᴴ)^r)
        (markedPhysicalUnnormalizedPositionVector P M Z z) := by
  unfold markedPhysicalPositionMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have he : markedPositionVector
      (fun s : MarkedPhysicalState P M Z => s.1.1) (markedPhysicalMass V M) z =
      (Real.sqrt (markedPhysicalMass V M):ℂ) • markedPhysicalUnnormalizedPositionVector P M Z z := by
    funext s
    by_cases hs : s.1.1=z <;>
      simp [markedPositionVector,markedPhysicalUnnormalizedPositionVector,hs]
  rw [he,markedPSD_quadratic_real_scale _ ((Matrix.posSemidef_self_mul_conjTranspose A).pow r),
    Real.sq_sqrt (markedPhysicalMass_nonneg V M hV)]

end
end ArtinMatthews
