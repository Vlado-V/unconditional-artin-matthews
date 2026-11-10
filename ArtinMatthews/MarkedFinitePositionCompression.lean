module

public import ArtinMatthews.MarkedFiniteCells
public import Mathlib.Analysis.Matrix.PosDef


set_option backward.privateInPublic true
@[expose] public section

/-! Position vectors are constant on all states over one position and
are not normalized. PSD compression retains their literal moments. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section

def markedPositionVector {ι κ : Type*} [DecidableEq κ]
    (p : ι → κ) (σ : ℝ) (x : κ) : ι → ℂ :=
  fun s => if p s=x then (Real.sqrt σ : ℂ) else 0

def markedPositionLift {ι κ : Type*} (p : ι → κ) (σ : ℝ) (a : κ → ℂ) : ι → ℂ :=
  fun s => (Real.sqrt σ : ℂ)*a (p s)

theorem markedPositionLift_energy {ι κ : Type*} [Fintype ι]
    (p : ι → κ) (σ : ℝ) (hσ : 0 ≤ σ) (a : κ → ℂ) :
    (∑ s, ‖markedPositionLift p σ a s‖^2)=∑ s, σ*‖a (p s)‖^2 := by
  apply Finset.sum_congr rfl
  intro s _
  simp only [markedPositionLift,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg σ),mul_pow,Real.sq_sqrt hσ]

theorem markedPositionLift_cell_mulVec {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : ι → κ) (c : κ → ℤ) (σ : ℝ) (a : κ → ℂ) (j : ℤ) :
    (fun s x => if c x=j then markedPositionVector p σ x s else 0) *ᵥ
        (fun x => if c x=j then a x else 0) =
      markedCellPart c p j (markedPositionLift p σ a) := by
  funext s
  change (∑ x, (if c x=j then markedPositionVector p σ x s else 0) *
    (if c x=j then a x else 0)) = _
  rw [Finset.sum_eq_single (p s)]
  · by_cases h : c (p s)=j <;>
      simp only [h,ite_true,ite_false,markedPositionVector,markedPositionLift,markedCellPart,
        mul_zero]
  · intro x _ hx
    have hs : p s≠x := Ne.symm hx
    by_cases h : c x=j <;>
      simp only [h,ite_true,ite_false,markedPositionVector,ite_eq_right hs,zero_mul]
  · simp

theorem markedPSD_positionCell_compression {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (p : ι → κ) (c : κ → ℤ)
    (σ : ℝ) (a : κ → ℂ) (j : ℤ) :
    markedQuadraticForm B (markedCellPart c p j (markedPositionLift p σ a)) ≤
      (∑ x, if c x=j then markedQuadraticForm B (markedPositionVector p σ x) else 0) *
        ∑ x, if c x=j then ‖a x‖^2 else 0 := by
  have h := markedPSD_compression B hB
    (fun s x => if c x=j then markedPositionVector p σ x s else 0)
    (fun x => if c x=j then a x else 0)
  rw [markedPositionLift_cell_mulVec] at h
  have hq (x : κ) :
      markedQuadraticForm B (fun s => if c x=j then markedPositionVector p σ x s else 0) =
        if c x=j then markedQuadraticForm B (markedPositionVector p σ x) else 0 := by
    by_cases hc : c x=j
    · simp only [hc,ite_true]
    · simp [hc,markedQuadraticForm,Matrix.mulVec,dotProduct]
  simpa only [hq,apply_ite (fun z : ℂ => ‖z‖^2),norm_zero,zero_pow (by decide : 2≠0)] using h

theorem markedPSD_positionCell_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (p : ι → κ) (c : κ → ℤ)
    (σ : ℝ) (a : κ → ℂ) (j : ℤ) (D M : ℝ) (hM : 0 ≤ M)
    (hc : ((Finset.univ.filter (fun x => c x=j)).card : ℝ) ≤ D)
    (ha : ∀ x, ‖a x‖^2 ≤ M) :
    markedQuadraticForm B (markedCellPart c p j (markedPositionLift p σ a)) ≤
      D*M*(∑ x, if c x=j then markedQuadraticForm B (markedPositionVector p σ x) else 0) := by
  let d := ∑ x, if c x=j then markedQuadraticForm B (markedPositionVector p σ x) else 0
  have hd : 0 ≤ d := Finset.sum_nonneg (fun x _ => by
    split_ifs
    · exact hB.re_dotProduct_nonneg _
    · exact le_rfl)
  have he : (∑ x, if c x=j then ‖a x‖^2 else 0) ≤ D*M := by
    calc
      _ = ∑ x ∈ Finset.univ.filter (fun x => c x=j), ‖a x‖^2 :=
        (Finset.sum_filter _ _).symm
      _ ≤ ∑ _x ∈ Finset.univ.filter (fun x => c x=j), M :=
        Finset.sum_le_sum (fun x _ => ha x)
      _ = ((Finset.univ.filter (fun x => c x=j)).card : ℝ)*M := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ D*M := mul_le_mul_of_nonneg_right hc hM
  calc
    _ ≤ d*(∑ x, if c x=j then ‖a x‖^2 else 0) := markedPSD_positionCell_compression B hB p c σ a j
    _ ≤ d*(D*M) := mul_le_mul_of_nonneg_left he hd
    _ = _ := by ring

end
end ArtinMatthews
