module

public import ArtinMatthews.MarkedPhysicalEndpointNormPositions


set_option backward.privateInPublic true
@[expose] public section

/-! The original physical endpoint Hilbert energy. Exact coefficient norm
sums are retained before applying scalar bounds, and the reciprocal-list
normalization contributes at most one, uniformly in the full-list length. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedPhysicalEndpointEnergy {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ) (α β : ℕ → ℂ) : ℝ :=
  ∑ s : MarkedPhysicalState P M Z,
    markedPhysicalMass V M * ‖markedPhysicalEndpointVector P M α β s.1.1.1‖ ^ 2

def markedPhysicalEndpointNorm {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ) (α β : ℕ → ℂ) : ℝ :=
  Real.sqrt (markedPhysicalEndpointEnergy P M Z V α β)

theorem markedPhysicalMass_nonneg {J : Type*} [Fintype J]
    (V : J → ℝ) (M : ℕ) (hV : ∀ j, 0 ≤ V j) : 0 ≤ markedPhysicalMass V M :=
  Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hV j)) M)

theorem markedPhysicalEndpointEnergy_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ)
    (hV : ∀ j, 0 ≤ V j) (α β : ℕ → ℂ) : 0 ≤ markedPhysicalEndpointEnergy P M Z V α β :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (markedPhysicalMass_nonneg V M hV) (sq_nonneg _))

theorem markedPhysicalEndpointEnergy_eq_positions {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ) (α β : ℕ → ℂ) :
    markedPhysicalEndpointEnergy P M Z V α β =
      ∑ a : MarkedPhysicalMarking P M, markedPhysicalMass V M *
        ∑ z : MarkedPhysicalPositions Z a, ‖markedPhysicalEndpointVector P M α β z.1.1‖ ^ 2 := by
  classical
  unfold markedPhysicalEndpointEnergy
  have he := (markedPhysicalStatePositionsEquiv P M Z).sum_comp
    (fun t : Σ a : MarkedPhysicalMarking P M, MarkedPhysicalPositions Z a =>
      markedPhysicalMass V M * ‖markedPhysicalEndpointVector P M α β t.2.1.1‖ ^ 2)
  simpa only [markedPhysicalStatePositionsEquiv, Equiv.coe_fn_mk, Fintype.sum_sigma,
    ← Finset.mul_sum] using he

/-- The original physical norm is bounded with the original scalar
coefficients still present inside exact finite norm sums. In particular
zeros, interval supports, and roughness supports are retained. -/
theorem markedPhysicalEndpointEnergy_le_coefficients {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {A B : ℕ} (hZ : ∀ z ∈ Z, 0 < z.1 ∧ z.1 ≤ (A : ℤ) ∧ 0 < z.2 ∧ z.2 ≤ (B : ℤ))
    (α β : ℕ → ℂ) :
    markedPhysicalEndpointEnergy P M Z V α β ≤
      ∑ a : MarkedPhysicalMarking P M, if MarkedPhysicalMarkingDistinct a then
        markedPhysicalMass V M *
          ((∑ m ∈ Finset.Ioc 0 (A / markedPhysicalMarkingProduct a), ‖α m‖ ^ 2) *
            ∑ s ∈ Finset.Ioc 0 B, ‖β s‖ ^ 2) else 0 := by
  classical
  rw [markedPhysicalEndpointEnergy_eq_positions]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : MarkedPhysicalMarkingDistinct a
  · rw [ite_eq_left ha]
    exact mul_le_mul_of_nonneg_left (markedPhysicalPositions_energy_le_coefficients hP hdis hZ a α β)
      (markedPhysicalMass_nonneg V M hV)
  · have : IsEmpty (MarkedPhysicalPositions Z a) := ⟨fun z => ha z.2.2.1⟩
    simp [ha]

/-- A mean-square bound for alpha alone suffices. Beta retains its actual
finite L² norm; no pointwise bound on beta is a premise. -/
theorem markedPhysicalEndpointEnergy_le_alpha_mean_square {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (hV : ∀ j, 0 < bandReciprocalMass (P j))
    {A B : ℕ} (hZ : ∀ z ∈ Z, 0 < z.1 ∧ z.1 ≤ (A : ℤ) ∧ 0 < z.2 ∧ z.2 ≤ (B : ℤ))
    (α β : ℕ → ℂ) {Cα : ℝ} (hCα : 0 ≤ Cα)
    (hα : ∀ N : ℕ, N ≤ A → (∑ m ∈ Finset.Ioc 0 N, ‖α m‖ ^ 2) ≤ Cα * N) :
    markedPhysicalEndpointEnergy P M Z (fun j => bandReciprocalMass (P j)) α β ≤
      (A : ℝ) * Cα * ∑ s ∈ Finset.Ioc 0 B, ‖β s‖ ^ 2 := by
  classical
  let T : ℝ := ∑ s ∈ Finset.Ioc 0 B, ‖β s‖ ^ 2
  have hT : 0 ≤ T := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let σ : ℝ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) M
  have hσ : 0 ≤ σ := markedPhysicalMass_nonneg _ M (fun j => (hV j).le)
  apply (markedPhysicalEndpointEnergy_le_coefficients P hP hdis M Z _ (fun j => (hV j).le) hZ α β).trans
  calc
    _ ≤ ∑ a : MarkedPhysicalMarking P M,
        (A * Cα * T) * (if MarkedPhysicalMarkingDistinct a then σ * markedPhysicalReciprocalProduct a else 0) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : MarkedPhysicalMarkingDistinct a
      · rw [ite_eq_left ha, ite_eq_left ha]
        have hαa := hα (A / markedPhysicalMarkingProduct a) (Nat.div_le_self _ _)
        have hdiv : ((A / markedPhysicalMarkingProduct a : ℕ) : ℝ) ≤
            (A : ℝ) / markedPhysicalMarkingProduct a := Nat.cast_div_le
        calc
          _ ≤ σ * ((Cα * ((A / markedPhysicalMarkingProduct a : ℕ) : ℝ)) * T) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hαa hT) hσ
          _ ≤ σ * ((Cα * ((A : ℝ) / markedPhysicalMarkingProduct a)) * T) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdiv hCα) hT) hσ
          _ = _ := by rw [markedPhysicalReciprocalProduct_eq]; ring
      · simp only [ite_eq_right ha, mul_zero, le_refl]
    _ = (A * Cα * T) * ∑ a : MarkedPhysicalMarking P M,
        if MarkedPhysicalMarkingDistinct a then σ * markedPhysicalReciprocalProduct a else 0 := by
      exact (Finset.mul_sum Finset.univ
        (fun a : MarkedPhysicalMarking P M => if MarkedPhysicalMarkingDistinct a then
          σ * markedPhysicalReciprocalProduct a else 0) (A * Cα * T)).symm
    _ ≤ A * Cα * T := by
      exact mul_le_of_le_one_right (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCα) hT)
        (markedPhysicalMarking_distinct_normalized_sum_le_one P M hV)

theorem markedPhysical_scalar_norm_sum_le {α : ℕ → ℂ} {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hα : ∀ m ∈ Finset.Ioc 0 A, ‖α m‖ ≤ C) {N : ℕ} (hN : N ≤ A) :
    (∑ m ∈ Finset.Ioc 0 N, ‖α m‖ ^ 2) ≤ C ^ 2 * N := by
  calc
    _ ≤ ∑ _m ∈ Finset.Ioc 0 N, C ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      have hb := hα m (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hm).1, (Finset.mem_Ioc.mp hm).2.trans hN⟩)
      simpa only [pow_two] using mul_le_mul hb hb (norm_nonneg _) hC
    _ = _ := by simp; ring

/-- The pointwise alpha corollary still keeps the full original beta L²
sum, without replacing it by a maximum or dropping its support. -/
theorem markedPhysicalEndpointEnergy_le_alpha_bound {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (hV : ∀ j, 0 < bandReciprocalMass (P j))
    {A B : ℕ} (hZ : ∀ z ∈ Z, 0 < z.1 ∧ z.1 ≤ (A : ℤ) ∧ 0 < z.2 ∧ z.2 ≤ (B : ℤ))
    (α β : ℕ → ℂ) {Cα : ℝ} (hCα : 0 ≤ Cα)
    (hα : ∀ m ∈ Finset.Ioc 0 A, ‖α m‖ ≤ Cα) :
    markedPhysicalEndpointEnergy P M Z (fun j => bandReciprocalMass (P j)) α β ≤
      (A : ℝ) * Cα ^ 2 * ∑ s ∈ Finset.Ioc 0 B, ‖β s‖ ^ 2 :=
  markedPhysicalEndpointEnergy_le_alpha_mean_square P hP hdis M Z hV hZ α β (sq_nonneg _)
    (fun _ hN => markedPhysical_scalar_norm_sum_le hCα hα hN)

/-- The usual endpoint estimate, with constants independent of the number
of groups and the growing ordered-list length. -/
theorem markedPhysicalEndpointEnergy_le_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (hV : ∀ j, 0 < bandReciprocalMass (P j))
    {A B : ℕ} (hZ : ∀ z ∈ Z, 0 < z.1 ∧ z.1 ≤ (A : ℤ) ∧ 0 < z.2 ∧ z.2 ≤ (B : ℤ))
    (α β : ℕ → ℂ) {Cα Cβ : ℝ} (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ)
    (hα : ∀ m ∈ Finset.Ioc 0 A, ‖α m‖ ≤ Cα) (hβ : ∀ s ∈ Finset.Ioc 0 B, ‖β s‖ ≤ Cβ) :
    markedPhysicalEndpointEnergy P M Z (fun j => bandReciprocalMass (P j)) α β ≤
      (A : ℝ) * B * (Cα * Cβ) ^ 2 := by
  calc
    _ ≤ (A : ℝ) * Cα ^ 2 * ∑ s ∈ Finset.Ioc 0 B, ‖β s‖ ^ 2 :=
      markedPhysicalEndpointEnergy_le_alpha_bound P hP hdis M Z hV hZ α β hCα hα
    _ ≤ (A : ℝ) * Cα ^ 2 * (Cβ ^ 2 * B) :=
      mul_le_mul_of_nonneg_left (markedPhysical_scalar_norm_sum_le hCβ hβ le_rfl)
        (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    _ = _ := by ring

end ArtinMatthews
