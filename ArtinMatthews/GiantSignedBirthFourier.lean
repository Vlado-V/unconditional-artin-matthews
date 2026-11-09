module

public import ArtinMatthews.GiantSignedBirthRank
public import ArtinMatthews.MarkedBirthLocalPhases


set_option backward.privateInPublic true
@[expose] public section

/-! Equality constraints on actual birth values have finite Fourier
representations. Their factors are attached only to the birth operation. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] giantSignedBirthPermutationFintype

def giantSignedBirthValuePhase (θ : AddCircle (1 : ℝ)) : Option ℕ → ℂ
  | none => 0
  | some p => fourier (p : ℤ) θ

theorem giantSignedBirthValuePhase_norm_le (θ : AddCircle (1 : ℝ)) (p : Option ℕ) :
    ‖giantSignedBirthValuePhase θ p‖ ≤ 1 := by
  cases p with
  | none => simp [giantSignedBirthValuePhase]
  | some p => exact (Circle.norm_coe _).le

theorem giantSignedBirthValuePhase_orthogonality (p q : Option ℕ) :
    (∫ θ : AddCircle (1 : ℝ), giantSignedBirthValuePhase θ p *
      star (giantSignedBirthValuePhase θ q) ∂AddCircle.haarAddCircle) =
        if p ≠ none ∧ p = q then 1 else 0 := by
  cases p with
  | none => simp [giantSignedBirthValuePhase]
  | some p =>
    cases q with
    | none => simp [giantSignedBirthValuePhase]
    | some q =>
      simp only [giantSignedBirthValuePhase, Complex.star_def, ← fourier_neg, ← fourier_add]
      rw [markedBirth_fourier_integral]
      have h : (p : ℤ) + -(q : ℤ) = 0 ↔ p = q := by omega
      simp only [h, Option.some_ne_none, ne_eq, not_false_eq_true, true_and,
        Option.some.injEq]

def giantSignedBirthPermutationPhase {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → Option ℕ) (σ : Equiv.Perm A) (θ : A → AddCircle (1 : ℝ)) : ℂ :=
  ∏ a, if σ a = a then 1 else
    giantSignedBirthValuePhase (θ a) (p (σ a)) *
      star (giantSignedBirthValuePhase (θ a) (p a))

theorem giantSignedBirthPermutationPhase_integral
    {A : Type*} [Fintype A] [DecidableEq A] (p : A → Option ℕ) (σ : Equiv.Perm A) :
    (∫ θ : A → AddCircle (1 : ℝ), giantSignedBirthPermutationPhase p σ θ
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
        if MarkedBirthPermutationEvent p σ then 1 else 0 := by
  unfold giantSignedBirthPermutationPhase
  have hF := integral_fintype_prod_eq_prod
    (μ := fun _ : A => AddCircle.haarAddCircle)
    (fun a (θ : AddCircle (1 : ℝ)) => if σ a = a then (1 : ℂ) else
      giantSignedBirthValuePhase θ (p (σ a)) * star (giantSignedBirthValuePhase θ (p a)))
  rw [hF]
  have hi (a : A) :
      (∫ θ : AddCircle (1 : ℝ), if σ a = a then (1 : ℂ) else
        giantSignedBirthValuePhase θ (p (σ a)) * star (giantSignedBirthValuePhase θ (p a))
          ∂AddCircle.haarAddCircle) =
        if σ a = a ∨ p (σ a) ≠ none ∧ p (σ a) = p a then 1 else 0 := by
    by_cases ha : σ a = a
    · simp [ha]
    · simp only [ha, ite_false, false_or, giantSignedBirthValuePhase_orthogonality]
  simp_rw [hi]
  by_cases hσ : MarkedBirthPermutationEvent p σ
  · rw [ite_eq_left hσ]
    exact Finset.prod_eq_one (fun a _ => ite_eq_left (hσ a))
  · rw [ite_eq_right hσ]
    obtain ⟨a, ha⟩ := not_forall.mp hσ
    exact Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right ha)

def giantSignedBirthLocalMultiplier {A : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) (θ : A → AddCircle (1 : ℝ)) (a : A) (p : Option ℕ) : ℂ :=
  if a ∈ σ.support then
    giantSignedBirthValuePhase (θ (σ.symm a)) p * star (giantSignedBirthValuePhase (θ a) p)
  else 1

theorem giantSignedBirthLocalMultiplier_norm_le
    {A : Type*} [Fintype A] [DecidableEq A] (σ : Equiv.Perm A)
    (θ : A → AddCircle (1 : ℝ)) (a : A) (p : Option ℕ) :
    ‖giantSignedBirthLocalMultiplier σ θ a p‖ ≤ 1 := by
  unfold giantSignedBirthLocalMultiplier
  split_ifs
  · rw [norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right (giantSignedBirthValuePhase_norm_le _ _)
      (norm_nonneg _)).trans (by simpa using giantSignedBirthValuePhase_norm_le (θ a) p)
  · simp

theorem giantSignedBirthPermutationPhase_local
    {A : Type*} [Fintype A] [DecidableEq A] (p : A → Option ℕ) (σ : Equiv.Perm A)
    (θ : A → AddCircle (1 : ℝ)) :
    giantSignedBirthPermutationPhase p σ θ =
      ∏ a, giantSignedBirthLocalMultiplier σ θ a (p a) := by
  let L := fun a => if a ∈ σ.support then giantSignedBirthValuePhase (θ (σ.symm a)) (p a) else 1
  let R := fun a => if a ∈ σ.support then star (giantSignedBirthValuePhase (θ a) (p a)) else 1
  have hl (a : A) : giantSignedBirthLocalMultiplier σ θ a (p a) = L a * R a := by
    dsimp [giantSignedBirthLocalMultiplier, L, R]
    split_ifs <;> simp only [one_mul]
  have hp (a : A) :
      (if σ a = a then (1 : ℂ) else giantSignedBirthValuePhase (θ a) (p (σ a)) *
        star (giantSignedBirthValuePhase (θ a) (p a))) = L (σ a) * R a := by
    dsimp [L, R]
    simp only [Equiv.Perm.apply_mem_support, Equiv.symm_apply_apply]
    by_cases ha : σ a = a <;> simp [ha, Equiv.Perm.mem_support]
  unfold giantSignedBirthPermutationPhase
  simp_rw [hp, hl]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Equiv.prod_comp σ L]

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}
    {k ell n : ℕ} {C : Fin n → B → Finset (Fin k)}
    {batch : Fin (n+1) → B → ℕ}

def giantSignedBirthOperationMultiplier (d : GiantSignedBirthData P ell C batch)
    (σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch))
    (θ : GiantSignedBirthAddress B ell C batch → AddCircle (1 : ℝ))
    (o : GiantSignedBirthOperation n) : ℂ :=
  ∏ a : GiantSignedBirthAddress B ell C batch,
    if giantSignedBirthOperation ell C batch a = o then
      giantSignedBirthLocalMultiplier σ θ a (giantSignedBirthValue d a) else 1

theorem giantSignedBirthOperationMultiplier_norm_le (d : GiantSignedBirthData P ell C batch)
    (σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch))
    (θ : GiantSignedBirthAddress B ell C batch → AddCircle (1 : ℝ))
    (o : GiantSignedBirthOperation n) : ‖giantSignedBirthOperationMultiplier d σ θ o‖ ≤ 1 := by
  rw [giantSignedBirthOperationMultiplier, norm_prod]
  apply Finset.prod_le_one₀
  · intro a _
    exact norm_nonneg _
  · intro a _
    split_ifs
    · exact giantSignedBirthLocalMultiplier_norm_le _ _ _ _
    · simp

theorem giantSignedBirthOperationMultiplier_unaffected (d : GiantSignedBirthData P ell C batch)
    (σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch))
    (θ : GiantSignedBirthAddress B ell C batch → AddCircle (1 : ℝ))
    (o : GiantSignedBirthOperation n)
    (ho : o ∉ σ.support.image (giantSignedBirthOperation ell C batch)) :
    giantSignedBirthOperationMultiplier d σ θ o = 1 := by
  apply Finset.prod_eq_one
  intro a _
  split_ifs with ha
  · have hn : a ∉ σ.support := fun h => ho (Finset.mem_image.mpr ⟨a, h, ha⟩)
    exact ite_eq_right hn
  · rfl

theorem giantSignedBirthPermutationPhase_operations (d : GiantSignedBirthData P ell C batch)
    (σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch))
    (θ : GiantSignedBirthAddress B ell C batch → AddCircle (1 : ℝ)) :
    giantSignedBirthPermutationPhase (giantSignedBirthValue d) σ θ =
      ∏ o : GiantSignedBirthOperation n, giantSignedBirthOperationMultiplier d σ θ o := by
  rw [giantSignedBirthPermutationPhase_local]
  unfold giantSignedBirthOperationMultiplier
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro a _
  simp

end
end ArtinMatthews
