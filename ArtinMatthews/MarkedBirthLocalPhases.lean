module

public import ArtinMatthews.MarkedBirthDistinctPermutation
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Pi


set_option backward.privateInPublic true
@[expose] public section

/-! Exact local Fourier phases for a performed-address permutation event.
An unperformed address has zero phase, rather than an invented prime value.
Each regrouped multiplier depends only on the prime created at that address. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedBirthValuePhase (θ : AddCircle (1:ℝ)) : Option Nat.Primes → ℂ
  | none => 0
  | some p => fourier (p.1:ℤ) θ

theorem markedBirthValuePhase_norm_le (θ : AddCircle (1:ℝ)) (p : Option Nat.Primes) :
    ‖markedBirthValuePhase θ p‖ ≤ 1 := by
  cases p with
  | none => simp [markedBirthValuePhase]
  | some p => exact (Circle.norm_coe _).le

theorem markedBirth_fourier_integral (n : ℤ) :
    (∫ θ : AddCircle (1:ℝ), fourier n θ ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hn (by norm_num : (0:ℝ)<1))

set_option backward.isDefEq.respectTransparency false in
theorem markedBirthValuePhase_orthogonality (p q : Option Nat.Primes) :
    (∫ θ : AddCircle (1:ℝ), markedBirthValuePhase θ p*star (markedBirthValuePhase θ q)
      ∂AddCircle.haarAddCircle) = if p ≠ none ∧ p = q then 1 else 0 := by
  cases p with
  | none => simp [markedBirthValuePhase]
  | some p =>
    cases q with
    | none => simp [markedBirthValuePhase]
    | some q =>
      simp only [markedBirthValuePhase,Complex.star_def,← fourier_neg,← fourier_add]
      rw [markedBirth_fourier_integral]
      have h : (p.1:ℤ)+ -(q.1:ℤ) = 0 ↔ p = q := by
        rw [← sub_eq_add_neg,sub_eq_zero]
        constructor
        · intro h
          apply Subtype.ext
          exact_mod_cast h
        · intro h
          exact congrArg (fun p : Nat.Primes => (p.1:ℤ)) h
      simp only [h,Option.some_ne_none,ne_eq,not_false_eq_true,true_and,Option.some.injEq]

def markedBirthPermutationPhase {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → Option Nat.Primes) (σ : Equiv.Perm A) (θ : A → AddCircle (1:ℝ)) : ℂ :=
  ∏ a, if σ a = a then 1 else
    markedBirthValuePhase (θ a) (p (σ a))*star (markedBirthValuePhase (θ a) (p a))

theorem markedBirthPermutationPhase_integral {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → Option Nat.Primes) (σ : Equiv.Perm A) :
    (∫ θ : A → AddCircle (1:ℝ), markedBirthPermutationPhase p σ θ
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
        if MarkedBirthPermutationEvent p σ then 1 else 0 := by
  unfold markedBirthPermutationPhase
  have hf := integral_fintype_prod_eq_prod
    (μ := fun _ : A => AddCircle.haarAddCircle)
    (fun a (θ : AddCircle (1:ℝ)) => if σ a = a then (1:ℂ) else
      markedBirthValuePhase θ (p (σ a))*star (markedBirthValuePhase θ (p a)))
  rw [hf]
  have hi (a : A) :
      (∫ θ : AddCircle (1:ℝ), if σ a = a then (1:ℂ) else
        markedBirthValuePhase θ (p (σ a))*star (markedBirthValuePhase θ (p a))
          ∂AddCircle.haarAddCircle) =
      if σ a = a ∨ p (σ a) ≠ none ∧ p (σ a) = p a then 1 else 0 := by
    by_cases ha : σ a = a
    · simp [ha]
    · simp only [ha,ite_false,false_or,markedBirthValuePhase_orthogonality]
  simp_rw [hi]
  by_cases hσ : MarkedBirthPermutationEvent p σ
  · rw [ite_eq_left hσ]
    exact Finset.prod_eq_one (fun a _ => ite_eq_left (hσ a))
  · rw [ite_eq_right hσ]
    obtain ⟨a,ha⟩ := not_forall.mp hσ
    exact Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right ha)

def markedBirthLocalMultiplier {A : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) (θ : A → AddCircle (1:ℝ)) (a : A) (p : Option Nat.Primes) : ℂ :=
  if a ∈ σ.support then
    markedBirthValuePhase (θ (σ.symm a)) p*star (markedBirthValuePhase (θ a) p)
  else 1

theorem markedBirthLocalMultiplier_norm_le {A : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) (θ : A → AddCircle (1:ℝ)) (a : A) (p : Option Nat.Primes) :
    ‖markedBirthLocalMultiplier σ θ a p‖ ≤ 1 := by
  unfold markedBirthLocalMultiplier
  split_ifs
  · rw [norm_mul,norm_star]
    exact (mul_le_mul_of_nonneg_right (markedBirthValuePhase_norm_le _ _)
      (norm_nonneg _)).trans (by simpa only [one_mul] using markedBirthValuePhase_norm_le _ _)
  · simp

theorem markedBirthPermutationPhase_local {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → Option Nat.Primes) (σ : Equiv.Perm A) (θ : A → AddCircle (1:ℝ)) :
    markedBirthPermutationPhase p σ θ = ∏ a, markedBirthLocalMultiplier σ θ a (p a) := by
  let L := fun a => if a ∈ σ.support then markedBirthValuePhase (θ (σ.symm a)) (p a) else 1
  let R := fun a => if a ∈ σ.support then star (markedBirthValuePhase (θ a) (p a)) else 1
  have hlocal (a : A) : markedBirthLocalMultiplier σ θ a (p a) = L a*R a := by
    dsimp [markedBirthLocalMultiplier,L,R]
    split_ifs <;> simp only [one_mul]
  have hphase (a : A) :
      (if σ a = a then (1:ℂ) else markedBirthValuePhase (θ a) (p (σ a))*
        star (markedBirthValuePhase (θ a) (p a))) = L (σ a)*R a := by
    dsimp [L,R]
    simp only [Equiv.Perm.apply_mem_support,Equiv.symm_apply_apply]
    by_cases ha : σ a = a
    · simp [ha,Equiv.Perm.mem_support]
    · simp [ha,Equiv.Perm.mem_support]
  unfold markedBirthPermutationPhase
  simp_rw [hphase,hlocal]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Equiv.prod_comp σ L]

theorem markedBirthLocalMultiplier_unmodified {A O : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq O] (operation : A → O) (σ : Equiv.Perm A)
    (θ : A → AddCircle (1:ℝ)) (o : O) (ho : o ∉ σ.support.image operation)
    (a : A) (ha : operation a = o) (p : Option Nat.Primes) :
    markedBirthLocalMultiplier σ θ a p = 1 := by
  have hn : a ∉ σ.support := fun h => ho (Finset.mem_image.mpr ⟨a,h,ha⟩)
  exact ite_eq_right hn

end ArtinMatthews
