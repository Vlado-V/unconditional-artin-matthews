module

public import ArtinMatthews.GiantSamplingShiftedInput
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.Divisors


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite bad-level-prime partition of the source bilinear sum.
The product argument, original coefficients and selected source supports
are transported exactly by `m=d*m0` and `n0=d*n`. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews
open OAI OAI.SevenEighths

def shiftedABLLevelRow (N : ℕ) (A : Finset ℕ) (d : ℕ) : Finset ℕ :=
  (A.filter (fun m => m.gcd N = d)).image (fun m => m/d)

def shiftedABLLevelColumn (B : Finset ℕ) (d : ℕ) : Finset ℕ :=
  B.image (fun n => d*n)

def shiftedABLLevelLeft (α : ℕ → ℂ) (d m : ℕ) : ℂ := α (d*m)

def shiftedABLLevelRight (β : ℕ → ℂ) (d n : ℕ) : ℂ :=
  if d ∣ n then β (n/d) else 0

theorem shiftedABLLevelRow_mem {N d m0 : ℕ} {A : Finset ℕ}
    (hm : m0 ∈ shiftedABLLevelRow N A d) :
    d*m0 ∈ A ∧ (d*m0).gcd N = d := by
  change m0 ∈ (A.filter (fun m => m.gcd N=d)).image (fun m => m/d) at hm
  obtain ⟨m,hmSource,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hmA,hmd⟩ := Finset.mem_filter.mp hmSource
  have he : d*(m/d)=m := by rw [← hmd]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left m N)
  simpa only [he] using And.intro hmA hmd

theorem shiftedABLLevelRow_source {N d m0 : ℕ} {A : Finset ℕ}
    (hN : N ≠ 0) (hA : ∀ m ∈ A, 0 < m ∧ Squarefree m)
    (hm : m0 ∈ shiftedABLLevelRow N A d) :
    0 < m0 ∧ Squarefree m0 ∧ m0.Coprime N := by
  obtain ⟨hmA,hmd⟩ := shiftedABLLevelRow_mem hm
  have hsource := hA _ hmA
  have hd : 0 < d := by rw [← hmd]; exact Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hN)
  have hquot : (d*m0)/((d*m0).gcd N)=m0 := by
    rw [hmd,Nat.mul_div_cancel_left _ hd]
  refine ⟨Nat.pos_of_mul_pos_left hsource.1,
    hsource.2.squarefree_of_dvd (Nat.dvd_mul_left m0 d),?_⟩
  simpa only [hquot] using Nat.coprime_div_gcd_of_squarefree hsource.2 hN

theorem shiftedABLLevelColumn_source {B : Finset ℕ} {d n0 : ℕ}
    (hd : 0 < d) (hB : ∀ n ∈ B, 0 < n)
    (hn : n0 ∈ shiftedABLLevelColumn B d) : 0 < n0 := by
  change n0 ∈ B.image (fun n => d*n) at hn
  obtain ⟨n,hnSource,rfl⟩ := Finset.mem_image.mp hn
  exact Nat.mul_pos hd (hB n hnSource)

theorem shiftedABLLevelRow_alpha_bound {N d m : ℕ} {A : Finset ℕ} {α : ℕ → ℂ}
    (hα : ∀ m ∈ A, ‖α m‖ ≤ 1) (hm : m ∈ shiftedABLLevelRow N A d) :
    ‖shiftedABLLevelLeft α d m‖ ≤ 1 :=
  hα _ (shiftedABLLevelRow_mem hm).1

theorem shiftedABLLevelColumn_beta_bound {B : Finset ℕ} {β : ℕ → ℂ} {d n0 : ℕ}
    (hd : 0 < d) (hβ : ∀ n ∈ B, ‖β n‖ ≤ 1)
    (hn : n0 ∈ shiftedABLLevelColumn B d) :
    ‖shiftedABLLevelRight β d n0‖ ≤ 1 := by
  change n0 ∈ B.image (fun n => d*n) at hn
  obtain ⟨n,hnSource,rfl⟩ := Finset.mem_image.mp hn
  simpa only [shiftedABLLevelRight,ite_eq_left (Nat.dvd_mul_right d n),
    Nat.mul_div_cancel_left _ hd] using hβ n hnSource

theorem giantCubicSamplingBilinear_level_fiber
    (η : HeckeFamily.Character) (Φ : ℝ → ℝ) (x : ℝ)
    (N d : ℕ) (hd : 0 < d) (A B : Finset ℕ) (α β : ℕ → ℂ) :
    giantCubicSamplingBilinear η Φ x (A.filter (fun m => m.gcd N=d)) B α β =
      giantCubicSamplingBilinear η Φ x (shiftedABLLevelRow N A d)
        (shiftedABLLevelColumn B d) (shiftedABLLevelLeft α d) (shiftedABLLevelRight β d) := by
  classical
  have hinj : Set.InjOn (fun m : ℕ => m/d) (A.filter (fun m => m.gcd N=d)) := by
    intro m hm m' hm' he
    change m/d=m'/d at he
    have hd1 : d ∣ m := (Finset.mem_filter.mp hm).2 ▸ Nat.gcd_dvd_left m N
    have hd2 : d ∣ m' := (Finset.mem_filter.mp hm').2 ▸ Nat.gcd_dvd_left m' N
    calc
      m = d*(m/d) := (Nat.mul_div_cancel' hd1).symm
      _ = d*(m'/d) := by rw [he]
      _ = m' := Nat.mul_div_cancel' hd2
  unfold giantCubicSamplingBilinear shiftedABLLevelRow
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro m hm
  have hdm : d*(m/d)=m := Nat.mul_div_cancel' ((Finset.mem_filter.mp hm).2 ▸ Nat.gcd_dvd_left m N)
  unfold shiftedABLLevelColumn
  rw [Finset.sum_image (fun n _ n' _ he => Nat.eq_of_mul_eq_mul_left hd he)]
  apply Finset.sum_congr rfl
  intro n _hn
  have hprod : (m/d)*(d*n)=m*n := by
    calc
      _ = (d*(m/d))*n := by ring
      _ = _ := by rw [hdm]
  simp only [shiftedABLLevelLeft,shiftedABLLevelRight,
    ite_eq_left (Nat.dvd_mul_right d n),Nat.mul_div_cancel_left _ hd,hdm,hprod]

theorem giantCubicSamplingBilinear_level_partition
    (η : HeckeFamily.Character) (Φ : ℝ → ℝ) (x : ℝ)
    (N : ℕ) (hN : N ≠ 0) (A B : Finset ℕ) (α β : ℕ → ℂ) :
    giantCubicSamplingBilinear η Φ x A B α β =
      ∑ d ∈ N.divisors, giantCubicSamplingBilinear η Φ x (shiftedABLLevelRow N A d)
        (shiftedABLLevelColumn B d) (shiftedABLLevelLeft α d) (shiftedABLLevelRight β d) := by
  classical
  have hsplit := Finset.sum_fiberwise_of_maps_to (s := A) (t := N.divisors)
    (g := fun m : ℕ => m.gcd N)
    (fun m _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right m N,hN⟩)
    (fun m => ∑ n ∈ B, α m*β n*(Φ (((m*n : ℕ) : ℝ)/x) : ℂ)*idealThetaCoeff η (m*n+1))
  change (∑ m ∈ A, ∑ n ∈ B, _) = _
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro d hd
  exact giantCubicSamplingBilinear_level_fiber η Φ x N d (Nat.pos_of_mem_divisors hd) A B α β

end ArtinMatthews
