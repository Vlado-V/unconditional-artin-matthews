module

public import ArtinMatthews.MarkedMinorArcRawGhostChoiceCauchy
public import ArtinMatthews.MarkedMinorArcRawGhostAbsoluteSchur


set_option backward.privateInPublic true
@[expose] public section

/-! Exact reweighting of the genuine reverse ghost energy. The identity retains
all actual indexed choices and factorial masses and prepares the full transpose
argument on the pending-symmetric space. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

/-- The Cauchy reverse energy is exactly the literal absolute ghost applied to
norm-square divided by the target Schur weight, times the source weight. -/
theorem markedRawGhostChoiceReverseEnergy_eq_absApply
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ v₀ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ) (s : MarkedRawState P M B Z) :
    (markedRawGhostChoiceReverseEnergy ν V qStage ρ v₀ hZ f s : ℂ) =
      (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) *
        markedRawGhostAbsApply ν V qStage ρ hZ
          (fun t => ((‖f t‖^2 / markedRawMemorySchurWeight v₀ t.2.2 : ℝ) : ℂ)) s := by
  classical
  rw [markedRawGhostChoiceReverseEnergy_eq]
  unfold markedRawGhostAbsApply
  simp only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero,
    Complex.ofReal_mul, Complex.ofReal_div, Finset.mul_sum, mul_zero]
  apply Finset.sum_congr rfl
  intro del _
  split_ifs
  · apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro births _
    dsimp only [markedRawGhostTargetState]
    ring
  · rfl

/-- The literal Schur weight is pending-symmetric, without any value distinctness. -/
theorem markedRawMemorySchurWeight_symmetric {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (v₀ : ℝ) :
    MarkedRawMemorySymmetric (fun m : MarkedRawMemory P B =>
      (markedRawMemorySchurWeight v₀ m : ℂ)) := fun _ _ => rfl

/-- The exact norm-square reweighting needed by the transpose stays in the
same genuine symmetric-memory domain as the original observable. -/
theorem markedRawGhostEnergyReweight_symmetric {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (v₀ : ℝ) (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z, (a, m))))
    (z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun m =>
      ((‖f (z, (a, m))‖^2 / markedRawMemorySchurWeight v₀ m : ℝ) : ℂ)) := by
  intro m σ
  have hh : f (z, (a, markedRawMemoryPermute m σ)) = f (z, (a, m)) := hf z a m σ
  dsimp only
  rw [hh, markedRawMemorySchurWeight_permute]

/-- Exact cancellation of the positive Schur weight in the swapped action.
This uses the actual row identity and does not assume a column estimate. -/
theorem markedRawGhostEnergyReweight_swapped_schur
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {v₀ : ℝ} (hv₀ : 0 < v₀) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) :
    ((‖f s‖^2 / markedRawMemorySchurWeight v₀ s.2.2 : ℝ) : ℂ) *
      markedRawGhostSwappedAbsApply ν V qStage ρ hZ
        (fun t => (markedRawMemorySchurWeight v₀ t.2.2 : ℂ)) s =
      ((‖f s‖^2 * markedRawGhostSwappedWeightedAbsRow ν V qStage ρ v₀
        s.2.2 s.1.1 (hZ _ s.1.2) : ℝ) : ℂ) := by
  rw [markedRawGhostSwappedAbsApply_schur ν V qStage ρ hv₀ hZ s]
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  have hw : (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) ≠ 0 := by
    exact_mod_cast (markedRawMemorySchurWeight_pos hv₀ s.2.2).ne'
  field_simp

/-- Sum the proved pointwise Cauchy estimate against the actual state mass.
The remaining reverse sum is a concrete choice sum, not an assumed norm bound. -/
theorem markedRawGhostApply_actual_energy_le_reverse_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (qStage : ℝ), 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (M B : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
        (f : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ),
      (∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        ‖markedRawGhostApply (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ hZ f s‖^2) ≤
      Real.exp ((Fintype.card J : ℝ) * (2 * markedRawGhostSchurParameter q ρ / ρ)) *
        ∑ s, markedRawStateMass (markedRawActualPrimeAtom e q x) s *
          markedRawGhostChoiceReverseEnergy (markedRawActualPrimeAtom e q x)
            (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ
            (markedRawGhostSchurParameter q ρ) hZ f s := by
  classical
  filter_upwards [markedRawGhostApply_actual_choice_cauchy_eventually e he hq₀ hq₁ hρ hgap,
    marked_actual_tilted_atom_comparison_eventually e he] with x hx hν
  intro qStage hqs₀ hqs M B Z hZ f
  have hνpos : ∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p := by
    intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (hν q hq₀ hq₁ j _).1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    _ ≤ markedRawStateMass (markedRawActualPrimeAtom e q x) s *
        (Real.exp ((Fintype.card J : ℝ) * (2 * markedRawGhostSchurParameter q ρ / ρ)) *
          markedRawGhostChoiceReverseEnergy (markedRawActualPrimeAtom e q x)
            (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ
            (markedRawGhostSchurParameter q ρ) hZ f s) :=
      mul_le_mul_of_nonneg_left (hx qStage hqs₀ hqs M B Z hZ f s)
        (markedRawStateMass_nonneg _ hνpos s)
    _ = _ := by ring

end
end ArtinMatthews
