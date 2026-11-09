module

public import ArtinMatthews.MarkedMemoryHistoryGhostSum
public import ArtinMatthews.MarkedMinorArcRawGhostActualRow


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise weighted Cauchy for the literal signed ghost choices. The
reverse energy retains every indexed deletion and ordered birth factorial. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

theorem markedGhostChoice_finite_cauchy {ι : Type*} [Fintype ι]
    (c f : ι → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    ‖∑ i, c i*f i‖^2 ≤ (∑ i, ‖c i‖*w i)*(∑ i, ‖c i‖/w i*‖f i‖^2) := by
  have hs : (∑ i, ‖c i‖*‖f i‖)^2 ≤
      (∑ i, ‖c i‖*w i)*(∑ i, ‖c i‖/w i*‖f i‖^2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _
      exact mul_nonneg (norm_nonneg _) (hw i).le
    · intro i _
      exact mul_nonneg (div_nonneg (norm_nonneg _) (hw i).le) (sq_nonneg _)
    · intro i _
      apply le_of_eq
      field_simp [(hw i).ne']
  have hn : ‖∑ i, c i*f i‖ ≤ ∑ i, ‖c i‖*‖f i‖ := by
    simpa only [norm_mul] using norm_sum_le (Finset.univ) (fun i => c i*f i)
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => by positivity))).mpr hn).trans hs

theorem markedMemoryGhostChoice_abs_weighted_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ v₀ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z) :
    (∑ choice : MarkedMemoryGhostChoice hZ s,
      ‖markedMemoryGhostChoiceWeight ν V qStage ρ hZ s choice‖ *
        (markedRawMemorySchurWeight v₀ (markedMemoryGhostChoiceTarget hZ s choice).2.2 /
          markedRawMemorySchurWeight v₀ s.2.2)) =
      markedRawGhostWeightedAbsRow ν V qStage ρ v₀ s.2.2 s.1.1 (hZ _ s.1.2) := by
  classical
  simpa only [markedMemoryGhostChoiceWeight,Complex.norm_real,Real.norm_eq_abs,
    markedMemoryGhostChoiceTarget,markedRawGhostTargetState,markedRawGhostWeightedAbsRow] using
    markedMemoryGhostChoice_sum_deletion hZ s
      (fun del l births =>
        |markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l *
          markedRawGhostBirthMass ν l births| *
          (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2) del l births)/
            markedRawMemorySchurWeight v₀ s.2.2))

def markedRawGhostChoiceReverseEnergy {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ v₀ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) : ℝ :=
  ∑ choice : MarkedMemoryGhostChoice hZ s,
    ‖markedMemoryGhostChoiceWeight ν V qStage ρ hZ s choice‖ *
      (markedRawMemorySchurWeight v₀ s.2.2 /
        markedRawMemorySchurWeight v₀ (markedMemoryGhostChoiceTarget hZ s choice).2.2) *
      ‖f (markedMemoryGhostChoiceTarget hZ s choice)‖^2

theorem markedRawGhostChoiceReverseEnergy_eq {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ v₀ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) :
    markedRawGhostChoiceReverseEnergy ν V qStage ρ v₀ hZ f s =
      ∑ del : MarkedRawGhostDeletion s.2.2,
        if MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2) del then
          ∑ l : MarkedRawGhostBirthSizes s.2.2 del, ∑ births : MarkedRawGhostBirthLabels l,
            |markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l*
              markedRawGhostBirthMass ν l births| *
              (markedRawMemorySchurWeight v₀ s.2.2 /
                markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2) del l births))*
              ‖f (markedRawGhostTargetState hZ s del l births)‖^2
        else 0 := by
  classical
  simpa only [markedRawGhostChoiceReverseEnergy,markedMemoryGhostChoiceWeight,Complex.norm_real,
    Real.norm_eq_abs,markedMemoryGhostChoiceTarget,markedRawGhostTargetState] using
    markedMemoryGhostChoice_sum_deletion hZ s
      (fun del l births =>
        |markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l*
          markedRawGhostBirthMass ν l births| *
          (markedRawMemorySchurWeight v₀ s.2.2 /
            markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2) del l births))*
          ‖f (markedRawGhostTargetState hZ s del l births)‖^2)

theorem markedRawGhostChoiceReverseEnergy_nonneg {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) :
    0 ≤ markedRawGhostChoiceReverseEnergy ν V qStage ρ v₀ hZ f s := by
  unfold markedRawGhostChoiceReverseEnergy
  exact Finset.sum_nonneg (fun choice _ => mul_nonneg
    (mul_nonneg (norm_nonneg _) (div_nonneg
      (markedRawMemorySchurWeight_pos hv₀ _).le (markedRawMemorySchurWeight_pos hv₀ _).le))
    (sq_nonneg _))

theorem markedRawGhostApply_choice_cauchy {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) :
    ‖markedRawGhostApply ν V qStage ρ hZ f s‖^2 ≤
      markedRawGhostWeightedAbsRow ν V qStage ρ v₀ s.2.2 s.1.1 (hZ _ s.1.2)*
        markedRawGhostChoiceReverseEnergy ν V qStage ρ v₀ hZ f s := by
  classical
  have hs := markedGhostChoice_finite_cauchy
    (markedMemoryGhostChoiceWeight ν V qStage ρ hZ s)
    (fun choice => f (markedMemoryGhostChoiceTarget hZ s choice))
    (fun choice => markedRawMemorySchurWeight v₀ (markedMemoryGhostChoiceTarget hZ s choice).2.2 /
      markedRawMemorySchurWeight v₀ s.2.2)
    (fun choice => div_pos (markedRawMemorySchurWeight_pos hv₀ _) (markedRawMemorySchurWeight_pos hv₀ _))
  rw [markedMemoryGhostChoice_sum,markedMemoryGhostChoice_abs_weighted_sum] at hs
  convert hs using 1
  congr 1
  unfold markedRawGhostChoiceReverseEnergy
  apply Finset.sum_congr rfl
  intro choice _
  field_simp [(markedRawMemorySchurWeight_pos hv₀ s.2.2).ne',
    (markedRawMemorySchurWeight_pos hv₀ (markedMemoryGhostChoiceTarget hZ s choice).2.2).ne']

theorem markedRawGhostApply_actual_choice_cauchy_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (qStage : ℝ), 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (M B : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
        (f : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ)
        (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z),
        ‖markedRawGhostApply (markedRawActualPrimeAtom e q x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ hZ f s‖^2 ≤
          Real.exp ((Fintype.card J : ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ))*
            markedRawGhostChoiceReverseEnergy (markedRawActualPrimeAtom e q x)
              (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ
              (markedRawGhostSchurParameter q ρ) hZ f s := by
  have hv₀ : 0 < markedRawGhostSchurParameter q ρ :=
    (by norm_num : (0:ℝ)<1).trans_le (markedRawGhostSchurParameter_ge_one q ρ)
  filter_upwards [markedRawGhost_actual_weighted_row_eventually e he hq₀ hq₁ hρ hgap] with x hx
  intro qStage hqs₀ hqs M B Z hZ f s
  exact (markedRawGhostApply_choice_cauchy _ _ qStage ρ hv₀ hZ f s).trans
    (mul_le_mul_of_nonneg_right (hx qStage hqs₀ hqs B s.2.2 s.1.1 (hZ _ s.1.2))
      (markedRawGhostChoiceReverseEnergy_nonneg _ _ qStage ρ hv₀ hZ f s))

end ArtinMatthews
