module

public import ArtinMatthews.MarkedFinitePositionCompression


set_option backward.privateInPublic true
@[expose] public section

/-! Localized high moments control the physical position pairing. The
loss is the number of positions in one cell, never the number of states. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section

theorem markedPSD_positionCells_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (p : ι → κ) (c : κ → ℤ)
    (σ : ℝ) (a : κ → ℂ) (D M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ j, ((Finset.univ.filter (fun x => c x=j)).card : ℝ) ≤ D)
    (ha : ∀ x, ‖a x‖^2 ≤ M) :
    (∑ j : markedCellIndices c,
      markedQuadraticForm B (markedCellPart c p j.1 (markedPositionLift p σ a))) ≤
      D*M*∑ x, markedQuadraticForm B (markedPositionVector p σ x) := by
  calc
    _ ≤ ∑ j : markedCellIndices c, D*M*
        (∑ x, if c x=j.1 then markedQuadraticForm B (markedPositionVector p σ x) else 0) :=
      Finset.sum_le_sum (fun j _ => markedPSD_positionCell_bound B hB p c σ a j.1 D M hM (hc j.1) ha)
    _ = D*M*∑ x, markedQuadraticForm B (markedPositionVector p σ x) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      exact markedCell_sum_indicator c x _

theorem markedPositionPairing_localized_moment {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (p : ι → κ) (c : κ → ℤ) (R : ℤ) (hR : 0 ≤ R)
    (hA : ∀ s t, A s t≠0 → c (p t)-c (p s) ∈ Finset.Icc (-R) R)
    (σ : ℝ) (a : κ → ℂ) (g : ι → ℂ) (D M : ℝ) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hc : ∀ j, ((Finset.univ.filter (fun x => c x=j)).card : ℝ) ≤ D)
    (ha : ∀ x, ‖a x‖^2 ≤ M) (k : ℕ) :
    ‖markedMatrixPairing A (markedPositionLift p σ a) g‖^(2*(k+1)) ≤
      (2*(R:ℝ)+1)^(k+1) * (∑ s, ‖g s‖^2)^(k+1) *
        (∑ s, ‖markedPositionLift p σ a s‖^2)^k * (D*M) *
          ∑ x, markedQuadraticForm ((A*Aᴴ)^(k+1)) (markedPositionVector p σ x) := by
  let f := markedPositionLift p σ a
  let F := fun j : markedCellIndices c => markedCellPart c p j.1 f
  let G := fun j : markedCellIndices c => markedCellNeighbors c p R j.1 g
  let B := A*Aᴴ
  have hB : B.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have hpow := hB.pow (k+1)
  have hpair := markedMatrixPairing_cell_decomposition A c p R hA f g
  have hm := markedMatrixPairing_sum_moment A F G k
  change ‖∑ j : markedCellIndices c, markedMatrixPairing A (F j) (G j)‖^(2*(k+1)) ≤ _ at hm
  rw [← hpair] at hm
  have hfe : (∑ j, ∑ s, ‖F j s‖^2)=∑ s, ‖f s‖^2 := markedCellPart_energy c p f
  rw [hfe] at hm
  have hge : (∑ j, ∑ s, ‖G j s‖^2) ≤ (2*(R:ℝ)+1)*∑ s, ‖g s‖^2 :=
    markedCellNeighbors_energy c p R hR g
  have hcomp := markedPSD_positionCells_bound (B^(k+1)) hpow p c σ a D M hM hc ha
  have heF : 0 ≤ ∑ s, ‖f s‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have heG : 0 ≤ ∑ j, ∑ s, ‖G j s‖^2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have htrace : 0 ≤ ∑ x, markedQuadraticForm (B^(k+1)) (markedPositionVector p σ x) :=
    Finset.sum_nonneg (fun x _ => hpow.re_dotProduct_nonneg _)
  have hDM : 0 ≤ D*M := mul_nonneg hD hM
  calc
    _ ≤ (∑ j, ∑ s, ‖G j s‖^2)^(k+1) * (∑ s, ‖f s‖^2)^k *
        ∑ j, markedQuadraticForm (B^(k+1)) (F j) := hm
    _ ≤ (∑ j, ∑ s, ‖G j s‖^2)^(k+1) * (∑ s, ‖f s‖^2)^k *
        (D*M*∑ x, markedQuadraticForm (B^(k+1)) (markedPositionVector p σ x)) :=
      mul_le_mul_of_nonneg_left hcomp (mul_nonneg (pow_nonneg heG _) (pow_nonneg heF _))
    _ ≤ ((2*(R:ℝ)+1)*(∑ s, ‖g s‖^2))^(k+1) * (∑ s, ‖f s‖^2)^k *
        (D*M*∑ x, markedQuadraticForm (B^(k+1)) (markedPositionVector p σ x)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ heG hge (k+1)) (pow_nonneg heF _))
        (mul_nonneg hDM htrace)
    _ = _ := by rw [mul_pow]; ring

end
end ArtinMatthews
