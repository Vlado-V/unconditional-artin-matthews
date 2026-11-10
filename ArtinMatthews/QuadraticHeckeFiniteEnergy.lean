module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The least squared operator bound of a literal finite character matrix.
The zero-column case is included, so the bound is attained as an infimum
without any nonemptiness assumption on the matrix. -/
namespace ArtinMatthews.QuadraticScale

open scoped BigOperators

noncomputable section
variable {ι κ : Type*}

def coeffMass (cols : Finset κ) (a : κ → ℂ) : ℝ :=
  ∑ c ∈ cols, ‖a c‖ ^ 2

def rowValue (cols : Finset κ) (K : ι → κ → ℂ) (a : κ → ℂ) (r : ι) : ℂ :=
  ∑ c ∈ cols, K r c * a c

def finiteEnergy (rows : Finset ι) (cols : Finset κ) (K : ι → κ → ℂ) (a : κ → ℂ) : ℝ :=
  ∑ r ∈ rows, ‖rowValue cols K a r‖ ^ 2

def IsEnergyBound (rows : Finset ι) (cols : Finset κ) (K : ι → κ → ℂ) (B : ℝ) : Prop :=
  ∀ a : κ → ℂ, finiteEnergy rows cols K a ≤ B * coeffMass cols a

def energyBoundSet (rows : Finset ι) (cols : Finset κ) (K : ι → κ → ℂ) : Set ℝ :=
  {B | 0 ≤ B ∧ IsEnergyBound rows cols K B}

def bestEnergyBound (rows : Finset ι) (cols : Finset κ) (K : ι → κ → ℂ) : ℝ :=
  sInf (energyBoundSet rows cols K)

theorem coeffMass_nonneg (cols : Finset κ) (a : κ → ℂ) : 0 ≤ coeffMass cols a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem finiteEnergy_nonneg (rows : Finset ι) (cols : Finset κ)
    (K : ι → κ → ℂ) (a : κ → ℂ) : 0 ≤ finiteEnergy rows cols K a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem finiteEnergy_le_of_subset (rows rows' : Finset ι) (h : rows ⊆ rows')
    (cols : Finset κ) (K : ι → κ → ℂ) (a : κ → ℂ) :
    finiteEnergy rows cols K a ≤ finiteEnergy rows' cols K a :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)

theorem isEnergyBound_card (rows : Finset ι) (cols : Finset κ) (K : ι → κ → ℂ)
    (hK : ∀ r ∈ rows, ∀ c ∈ cols, ‖K r c‖ ≤ 1) :
    IsEnergyBound rows cols K ((rows.card : ℝ) * cols.card) := by
  intro a
  have hrow (r : ι) (hr : r ∈ rows) : ‖rowValue cols K a r‖ ^ 2 ≤ cols.card * coeffMass cols a := by
    have hsum : ‖rowValue cols K a r‖ ≤ ∑ c ∈ cols, ‖a c‖ :=
      (norm_sum_le cols (fun c => K r c * a c)).trans <|
        Finset.sum_le_sum (fun c hc => by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hK r hr c hc))
    refine (pow_le_pow_left₀ (norm_nonneg _) hsum 2).trans ?_
    simpa [coeffMass] using
      (Finset.sum_mul_sq_le_sq_mul_sq cols (fun _ : κ => (1 : ℝ)) (fun c => ‖a c‖))
  calc
    _ ≤ ∑ _r ∈ rows, (cols.card : ℝ) * coeffMass cols a :=
      Finset.sum_le_sum (fun r hr => hrow r hr)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

theorem bestEnergyBound_le (rows : Finset ι) (cols : Finset κ) (K : ι → κ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (h : IsEnergyBound rows cols K B) :
    bestEnergyBound rows cols K ≤ B :=
  csInf_le ⟨0, fun _ hb => hb.1⟩ ⟨hB, h⟩

theorem bestEnergyBound_spec (rows : Finset ι) (cols : Finset κ) (K : ι → κ → ℂ)
    (hex : (energyBoundSet rows cols K).Nonempty) :
    0 ≤ bestEnergyBound rows cols K ∧ IsEnergyBound rows cols K (bestEnergyBound rows cols K) := by
  refine ⟨le_csInf hex (fun _ hb => hb.1), ?_⟩
  intro a
  have hm := coeffMass_nonneg cols a
  rcases hm.eq_or_lt with hm | hm
  · obtain ⟨B, hB⟩ := hex
    have h := hB.2 a
    rw [← hm, mul_zero] at h ⊢
    exact h
  · apply (div_le_iff₀ hm).mp
    exact le_csInf hex (fun _ h => (div_le_iff₀ hm).mpr (h.2 a))

end
end ArtinMatthews.QuadraticScale
