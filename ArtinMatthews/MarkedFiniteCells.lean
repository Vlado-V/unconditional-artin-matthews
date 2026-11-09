module

public import ArtinMatthews.MarkedFiniteSpectralMoments


set_option backward.privateInPublic true
@[expose] public section

/-! Exact cell restrictions and bounded overlap on finite state spaces. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical
noncomputable section

abbrev markedCellIndices {κ : Type*} [Fintype κ] (c : κ → ℤ) :=
  (Finset.univ.image c : Finset ℤ)

def markedCellOf {κ : Type*} [Fintype κ] (c : κ → ℤ) (x : κ) : markedCellIndices c :=
  ⟨c x,Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩⟩

def markedCellPart {ι κ : Type*} (c : κ → ℤ) (p : ι → κ)
    (j : ℤ) (f : ι → ℂ) : ι → ℂ := fun s => if c (p s)=j then f s else 0

def markedCellNeighbors {ι κ : Type*} (c : κ → ℤ) (p : ι → κ)
    (R j : ℤ) (g : ι → ℂ) : ι → ℂ :=
  fun s => if c (p s)-j ∈ Finset.Icc (-R) R then g s else 0

theorem markedCell_sum_indicator {κ : Type*} [Fintype κ]
    (c : κ → ℤ) (x : κ) (z : ℝ) :
    (∑ j : markedCellIndices c, if c x=j.1 then z else 0)=z := by
  have he (j : markedCellIndices c) : c x=j.1 ↔ j=markedCellOf c x := by
    constructor
    · intro h; exact Subtype.ext h.symm
    · rintro rfl; rfl
  simp_rw [he]
  simp

theorem markedCellPart_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : κ → ℤ) (p : ι → κ) (f : ι → ℂ) :
    (∑ j : markedCellIndices c, ∑ s, ‖markedCellPart c p j.1 f s‖^2)=∑ s, ‖f s‖^2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [markedCellPart,apply_ite (fun z : ℂ => ‖z‖^2),norm_zero,zero_pow (by decide : 2≠0)]
    using markedCell_sum_indicator c (p s) (‖f s‖^2)

theorem markedCellNeighbors_card {κ : Type*} [Fintype κ]
    (c : κ → ℤ) (x : κ) (R : ℤ) (hR : 0 ≤ R) :
    ((Finset.univ.filter (fun j : markedCellIndices c =>
      c x-j.1 ∈ Finset.Icc (-R) R)).card : ℝ) ≤ 2*(R:ℝ)+1 := by
  let S := Finset.univ.filter (fun j : markedCellIndices c => c x-j.1 ∈ Finset.Icc (-R) R)
  let v : markedCellIndices c → ℤ := fun j => c x-j.1
  have hinj : Set.InjOn v S := by
    intro a _ b _ h
    apply Subtype.ext
    dsimp [v] at h
    omega
  have hsub : S.image v ⊆ Finset.Icc (-R) R := by
    intro z hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hj).2
  have hc : S.card ≤ (Finset.Icc (-R) R).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hi : ((Finset.Icc (-R) R).card : ℤ)=2*R+1 := by
    have h := Int.card_Icc_of_le (-R) R (by omega : -R ≤ R+1)
    omega
  calc
    _ ≤ ((Finset.Icc (-R) R).card : ℝ) := by exact_mod_cast hc
    _ = 2*(R:ℝ)+1 := by exact_mod_cast hi

theorem markedCellNeighbors_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : κ → ℤ) (p : ι → κ) (R : ℤ) (hR : 0 ≤ R) (g : ι → ℂ) :
    (∑ j : markedCellIndices c, ∑ s, ‖markedCellNeighbors c p R j.1 g s‖^2) ≤
      (2*(R:ℝ)+1)*∑ s, ‖g s‖^2 := by
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have he : (∑ j : markedCellIndices c, ‖markedCellNeighbors c p R j.1 g s‖^2) =
      ((Finset.univ.filter (fun j : markedCellIndices c =>
        c (p s)-j.1 ∈ Finset.Icc (-R) R)).card : ℝ)*‖g s‖^2 := by
    simp only [markedCellNeighbors,apply_ite (fun z : ℂ => ‖z‖^2),norm_zero,
      zero_pow (by decide : 2≠0),← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rw [he]
  exact mul_le_mul_of_nonneg_right (markedCellNeighbors_card c (p s) R hR) (sq_nonneg _)

theorem markedMatrixPairing_expansion {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (f g : ι → ℂ) :
    markedMatrixPairing A f g=∑ s, ∑ t, A s t*star (f s)*g t := by
  simp only [markedMatrixPairing,dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem markedMatrixPairing_cell_decomposition {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (c : κ → ℤ) (p : ι → κ) (R : ℤ)
    (hA : ∀ s t, A s t≠0 → c (p t)-c (p s) ∈ Finset.Icc (-R) R)
    (f g : ι → ℂ) :
    markedMatrixPairing A f g =
      ∑ j : markedCellIndices c, markedMatrixPairing A
        (markedCellPart c p j.1 f) (markedCellNeighbors c p R j.1 g) := by
  simp_rw [markedMatrixPairing_expansion]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  symm
  rw [Finset.sum_eq_single (markedCellOf c (p s))]
  · by_cases h : A s t=0
    · simp only [h,zero_mul]
    · simp only [markedCellOf,markedCellPart,ite_true,markedCellNeighbors]
      simp only [hA s t h,ite_true]
  · intro j _ hj
    have hs : c (p s)≠j.1 := fun h => hj (Subtype.ext h.symm)
    simp only [markedCellPart,ite_eq_right hs,star_zero,mul_zero,zero_mul]
  · simp

end
end ArtinMatthews
