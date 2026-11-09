module

public import ArtinMatthews.MarkedMinorArcRawGhostWeight


set_option backward.privateInPublic true
@[expose] public section

/-! Actual signed ghost coefficients under the positive pending Schur
weight. Signs are removed by absolute values only in this estimate, while
the target state and its exact birth/deletion weight ratio are retained. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The literal one-group absolute weighted factor of a ghost choice. -/
noncomputable def markedRawGhostAbsoluteFactor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (qStage ρ v₀ : ℝ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) (j : J) : ℝ :=
  ((1-qStage)/(ρ*v₀))^(del j).card*
    (qStage/ρ^2)^((markedRawGroupHitIndices m j z hz \ del j).card)*
    (v₀*(1-qStage)*V j/ρ)^(l.1 j : ℕ)

/-- Exact absolute signed coefficient times the actual source weight ratio,
including every repeated old index and every ordered birth. -/
theorem markedRawGhost_signed_absolute_weight {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {qStage ρ v₀ : ℝ} (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del)
    (births : MarkedRawGhostBirthLabels l) :
    |markedRawGhostSignedCoefficient V qStage ρ m z hz del l| *
      (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory m z hz del l births)/
        markedRawMemorySchurWeight v₀ m)=
      ∏ j, markedRawGhostAbsoluteFactor V qStage ρ v₀ m z hz del l j := by
  rw [markedRawGhost_target_weight_ratio hv₀.ne',markedRawGhostSignedCoefficient,Finset.abs_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hη : 0 ≤ 1-qStage := sub_nonneg.mpr hq₁
  have hd : |-(1-qStage)/ρ|=(1-qStage)/ρ := by
    rw [abs_div,abs_neg,abs_of_nonneg hη,abs_of_pos hρ]
  have hs : |qStage/ρ^2|=qStage/ρ^2 := abs_of_nonneg (div_nonneg hq₀ (sq_nonneg _))
  have hb : |-(1-qStage)*V j/ρ|=(1-qStage)*V j/ρ := by
    rw [show -(1-qStage)*V j/ρ=-((1-qStage)*V j/ρ) by ring,abs_neg,
      abs_of_nonneg (div_nonneg (mul_nonneg hη (hV j)) hρ.le)]
  rw [abs_mul,abs_mul,abs_pow,hd,abs_pow,hs,abs_pow,hb]
  unfold markedRawGhostAbsoluteFactor
  simp only [div_pow,mul_pow]
  field_simp [pow_ne_zero _ hρ.ne',pow_ne_zero _ hv₀.ne']

/-- The literal choice coefficient, prime birth mass and target Schur ratio
factor exactly into nonnegative actual birth integration and group factors. -/
theorem markedRawGhost_choice_absolute_weight {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    {B : ℕ} (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {qStage ρ v₀ : ℝ} (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del)
    (births : MarkedRawGhostBirthLabels l) :
    |markedRawGhostSignedCoefficient V qStage ρ m z hz del l*markedRawGhostBirthMass ν l births| *
      (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory m z hz del l births)/
        markedRawMemorySchurWeight v₀ m)=
      markedRawGhostBirthMass ν l births*
        ∏ j, markedRawGhostAbsoluteFactor V qStage ρ v₀ m z hz del l j := by
  rw [abs_mul,abs_of_nonneg (markedRawGhostBirthMass_nonneg ν hν l births)]
  rw [mul_right_comm _ (markedRawGhostBirthMass ν l births)]
  rw [markedRawGhost_signed_absolute_weight V hV hq₀ hq₁ hρ hv₀]
  ring

end ArtinMatthews
