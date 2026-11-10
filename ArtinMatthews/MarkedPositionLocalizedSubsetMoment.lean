module

public import ArtinMatthews.MarkedFinitePositionCompression
public import ArtinMatthews.MarkedFiniteLocalizedMoments
public import ArtinMatthews.MarkedLocalizedMomentRoots
public import Mathlib.Analysis.Matrix.PosDef


set_option backward.privateInPublic true
@[expose] public section

/-! A position-supported left test needs only the moment trace on its
support. Each compression uses the actual positions in that cell and
retains the full physical vectors over those positions. -/

namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section

theorem markedPositionLift_subset_cell_mulVec {ι κ : Type*} [DecidableEq κ]
    (p : ι → κ) (c : κ → ℤ) (σ : ℝ) (a : κ → ℂ) (roots : Finset κ)
    (hroots : ∀ x ∉ roots, a x = 0) (j : ℤ) :
    (fun s (x : ↥(roots.filter fun x => c x = j)) => markedPositionVector p σ x.val s) *ᵥ
        (fun x => a x.val) = markedCellPart c p j (markedPositionLift p σ a) := by
  funext s
  let cell := roots.filter (fun x => c x = j)
  change (∑ x : ↥cell, markedPositionVector p σ x.val s * a x.val) = _
  rw [Finset.sum_coe_sort cell (fun x => markedPositionVector p σ x s * a x)]
  by_cases hp : p s ∈ cell
  · rw [Finset.sum_eq_single_of_mem (p s) hp]
    · have hcell := (Finset.mem_filter.mp hp).2
      simp only [markedPositionVector,markedPositionLift,markedCellPart,hcell,ite_true]
    · intro x _ hne
      simp only [markedPositionVector,ite_eq_right (Ne.symm hne),zero_mul]
  · rw [Finset.sum_eq_zero (fun x hx => by
      have hne : p s ≠ x := fun he => hp (he ▸ hx)
      simp only [markedPositionVector,ite_eq_right hne,zero_mul])]
    by_cases hcell : c (p s) = j
    · have hout : p s ∉ roots := fun hr => hp (Finset.mem_filter.mpr ⟨hr,hcell⟩)
      simp only [markedCellPart,markedPositionLift,hcell,ite_true,hroots _ hout,mul_zero]
    · simp only [markedCellPart,hcell,ite_false]

theorem markedPSD_positionSubsetCell_compression {ι κ : Type*}
    [Fintype ι] [DecidableEq κ]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (p : ι → κ) (c : κ → ℤ)
    (σ : ℝ) (a : κ → ℂ) (roots : Finset κ) (hroots : ∀ x ∉ roots, a x = 0) (j : ℤ) :
    markedQuadraticForm B (markedCellPart c p j (markedPositionLift p σ a)) ≤
      (∑ x ∈ roots.filter (fun x => c x = j), markedQuadraticForm B (markedPositionVector p σ x)) *
        ∑ x ∈ roots.filter (fun x => c x = j), ‖a x‖^2 := by
  let cell := roots.filter (fun x => c x = j)
  have h := markedPSD_compression B hB
    (fun s (x : ↥cell) => markedPositionVector p σ x.val s) (fun x => a x.val)
  rw [markedPositionLift_subset_cell_mulVec p c σ a roots hroots j] at h
  change _ ≤ (∑ x : ↥cell, markedQuadraticForm B (markedPositionVector p σ x.val)) *
    ∑ x : ↥cell, ‖a x.val‖^2 at h
  rw [Finset.sum_coe_sort cell (fun x => markedQuadraticForm B (markedPositionVector p σ x)),
    Finset.sum_coe_sort cell (fun x => ‖a x‖^2)] at h
  exact h

theorem markedPSD_positionSubsetCell_bound {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (p : ι → κ) (c : κ → ℤ)
    (σ : ℝ) (a : κ → ℂ) (roots : Finset κ) (hroots : ∀ x ∉ roots, a x = 0)
    (j : ℤ) (D M : ℝ) (hM : 0 ≤ M)
    (hc : ((roots.filter (fun x => c x = j)).card : ℝ) ≤ D) (ha : ∀ x ∈ roots, ‖a x‖^2 ≤ M) :
    markedQuadraticForm B (markedCellPart c p j (markedPositionLift p σ a)) ≤
      D*M*(∑ x ∈ roots.filter (fun x => c x = j), markedQuadraticForm B (markedPositionVector p σ x)) := by
  let cell := roots.filter (fun x => c x = j)
  let T := ∑ x ∈ cell, markedQuadraticForm B (markedPositionVector p σ x)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun _ _ => hB.re_dotProduct_nonneg _)
  have he : (∑ x ∈ cell, ‖a x‖^2) ≤ D*M := by
    calc
      _ ≤ ∑ _x ∈ cell, M := Finset.sum_le_sum (fun x hx => ha x (Finset.mem_filter.mp hx).1)
      _ = (cell.card : ℝ)*M := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ D*M := mul_le_mul_of_nonneg_right hc hM
  calc
    _ ≤ T*(∑ x ∈ cell, ‖a x‖^2) := markedPSD_positionSubsetCell_compression B hB p c σ a roots hroots j
    _ ≤ T*(D*M) := mul_le_mul_of_nonneg_left he hT
    _ = _ := mul_comm _ _

theorem markedPSD_positionSubsetCells_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (p : ι → κ) (c : κ → ℤ)
    (σ : ℝ) (a : κ → ℂ) (roots : Finset κ) (hroots : ∀ x ∉ roots, a x = 0)
    (D M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ j, ((roots.filter (fun x => c x = j)).card : ℝ) ≤ D)
    (ha : ∀ x ∈ roots, ‖a x‖^2 ≤ M) :
    (∑ j : markedCellIndices c,
      markedQuadraticForm B (markedCellPart c p j.val (markedPositionLift p σ a))) ≤
      D*M*(∑ x ∈ roots, markedQuadraticForm B (markedPositionVector p σ x)) := by
  calc
    _ ≤ ∑ j : markedCellIndices c, D*M*
        (∑ x ∈ roots.filter (fun x => c x = j.val), markedQuadraticForm B (markedPositionVector p σ x)) :=
      Finset.sum_le_sum (fun j _ => markedPSD_positionSubsetCell_bound B hB p c σ a roots hroots
        j.val D M hM (hc j.val) ha)
    _ = _ := by
      simp_rw [Finset.sum_filter]
      rw [← Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      exact markedCell_sum_indicator c x _

theorem markedPositionPairing_localized_subset_moment {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (p : ι → κ) (c : κ → ℤ) (R : ℤ) (hR : 0 ≤ R)
    (hA : ∀ s t, A s t ≠ 0 → c (p t)-c (p s) ∈ Finset.Icc (-R) R)
    (σ : ℝ) (a : κ → ℂ) (g : ι → ℂ) (roots : Finset κ) (D M : ℝ)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hroots : ∀ x ∉ roots, a x = 0)
    (hc : ∀ j, ((roots.filter (fun x => c x = j)).card : ℝ) ≤ D)
    (ha : ∀ x ∈ roots, ‖a x‖^2 ≤ M) (k : ℕ) :
    ‖markedMatrixPairing A (markedPositionLift p σ a) g‖^(2*(k+1)) ≤
      (2*(R:ℝ)+1)^(k+1) * (∑ s, ‖g s‖^2)^(k+1) *
        (∑ s, ‖markedPositionLift p σ a s‖^2)^k * (D*M) *
          ∑ x ∈ roots, markedQuadraticForm ((A*Aᴴ)^(k+1)) (markedPositionVector p σ x) := by
  let f := markedPositionLift p σ a
  let F := fun j : markedCellIndices c => markedCellPart c p j.val f
  let G := fun j : markedCellIndices c => markedCellNeighbors c p R j.val g
  let B := A*Aᴴ
  have hB : B.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have hpow := hB.pow (k+1)
  have hpair := markedMatrixPairing_cell_decomposition A c p R hA f g
  have hmoment := markedMatrixPairing_sum_moment A F G k
  change ‖∑ j : markedCellIndices c, markedMatrixPairing A (F j) (G j)‖^(2*(k+1)) ≤ _ at hmoment
  rw [← hpair,show (∑ j, ∑ s, ‖F j s‖^2) = ∑ s, ‖f s‖^2 from markedCellPart_energy c p f] at hmoment
  have hG : (∑ j, ∑ s, ‖G j s‖^2) ≤ (2*(R:ℝ)+1)*∑ s, ‖g s‖^2 :=
    markedCellNeighbors_energy c p R hR g
  have hcomp := markedPSD_positionSubsetCells_bound (B^(k+1)) hpow p c σ a roots hroots D M hM hc ha
  have hf0 : 0 ≤ ∑ s, ‖f s‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hG0 : 0 ≤ ∑ j, ∑ s, ‖G j s‖^2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hT : 0 ≤ ∑ x ∈ roots, markedQuadraticForm (B^(k+1)) (markedPositionVector p σ x) :=
    Finset.sum_nonneg (fun _ _ => hpow.re_dotProduct_nonneg _)
  calc
    _ ≤ (∑ j, ∑ s, ‖G j s‖^2)^(k+1) * (∑ s, ‖f s‖^2)^k *
        ∑ j, markedQuadraticForm (B^(k+1)) (F j) := hmoment
    _ ≤ (∑ j, ∑ s, ‖G j s‖^2)^(k+1) * (∑ s, ‖f s‖^2)^k *
        (D*M*∑ x ∈ roots, markedQuadraticForm (B^(k+1)) (markedPositionVector p σ x)) :=
      mul_le_mul_of_nonneg_left hcomp (mul_nonneg (pow_nonneg hG0 _) (pow_nonneg hf0 _))
    _ ≤ ((2*(R:ℝ)+1)*(∑ s, ‖g s‖^2))^(k+1) * (∑ s, ‖f s‖^2)^k *
        (D*M*∑ x ∈ roots, markedQuadraticForm (B^(k+1)) (markedPositionVector p σ x)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hG0 hG (k+1)) (pow_nonneg hf0 _))
        (mul_nonneg (mul_nonneg hD hM) hT)
    _ = _ := by rw [mul_pow]; ring

theorem markedPositionPairing_localized_subset_moment_root {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (p : ι → κ) (c : κ → ℤ) (R : ℤ) (hR : 0 ≤ R)
    (hA : ∀ s t, A s t ≠ 0 → c (p t)-c (p s) ∈ Finset.Icc (-R) R)
    (σ : ℝ) (a : κ → ℂ) (g : ι → ℂ) (roots : Finset κ) (D M : ℝ)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hroots : ∀ x ∉ roots, a x = 0)
    (hc : ∀ j, ((roots.filter (fun x => c x = j)).card : ℝ) ≤ D)
    (ha : ∀ x ∈ roots, ‖a x‖^2 ≤ M) (k : ℕ) :
    ‖markedMatrixPairing A (markedPositionLift p σ a) g‖ ≤
      Real.sqrt (2*(R:ℝ)+1) * Real.sqrt (∑ s, ‖g s‖^2) *
        (∑ s, ‖markedPositionLift p σ a s‖^2)^((k:ℝ)/(2*((k+1:ℕ):ℝ))) *
        (D*M)^((2*((k+1:ℕ):ℝ))⁻¹) *
          (∑ x ∈ roots, markedQuadraticForm ((A*Aᴴ)^(k+1)) (markedPositionVector p σ x))^
            ((2*((k+1:ℕ):ℝ))⁻¹) := by
  have hR0 : (0:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hpow := (Matrix.posSemidef_self_mul_conjTranspose A).pow (k+1)
  exact markedLocalizedMoment_root_bound _ _ _ _ _ _ (norm_nonneg _) (by positivity)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg hD hM) (Finset.sum_nonneg (fun _ _ => hpow.re_dotProduct_nonneg _)) k
    (markedPositionPairing_localized_subset_moment A p c R hR hA σ a g roots D M hD hM hroots hc ha k)

end
end ArtinMatthews
