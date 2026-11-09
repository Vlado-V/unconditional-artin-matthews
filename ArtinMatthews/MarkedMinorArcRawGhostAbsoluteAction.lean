module

public import ArtinMatthews.MarkedMinorArcRawGhostSwapped
public import ArtinMatthews.MarkedMinorArcRawGhostSymmetry


set_option backward.privateInPublic true
@[expose] public section

/-! Literal absolute ghost actions and the actual swapped-charge action.
In the positive source parameter range the absolute action is exactly the
signed ghost with rho replaced by -rho.  Thus its pending symmetry follows
from the actual indexed-choice symmetry, without an assumed column bound. -/
namespace ArtinMatthews
open scoped BigOperators

noncomputable def markedRawGhostSwappedApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ) (s : MarkedRawState P M B Z) : ℂ := by
  classical
  exact ∑ del : MarkedRawGhostDeletion s.2.2,
    if MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2) del then
      ∑ l : MarkedRawGhostBirthSizes s.2.2 del, ∑ births : MarkedRawGhostBirthLabels l,
        ((markedRawGhostSwappedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l*
          markedRawGhostBirthMass ν l births : ℝ) : ℂ)*
          f (markedRawGhostTargetState hZ s del l births)
    else 0

noncomputable def markedRawGhostAbsApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ) (s : MarkedRawState P M B Z) : ℂ := by
  classical
  exact ∑ del : MarkedRawGhostDeletion s.2.2,
    if MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2) del then
      ∑ l : MarkedRawGhostBirthSizes s.2.2 del, ∑ births : MarkedRawGhostBirthLabels l,
        ((|markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l*
          markedRawGhostBirthMass ν l births| : ℝ) : ℂ)*
          f (markedRawGhostTargetState hZ s del l births)
    else 0

noncomputable def markedRawGhostSwappedAbsApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ) (s : MarkedRawState P M B Z) : ℂ := by
  classical
  exact ∑ del : MarkedRawGhostDeletion s.2.2,
    if MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2) del then
      ∑ l : MarkedRawGhostBirthSizes s.2.2 del, ∑ births : MarkedRawGhostBirthLabels l,
        ((|markedRawGhostSwappedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l*
          markedRawGhostBirthMass ν l births| : ℝ) : ℂ)*
          f (markedRawGhostTargetState hZ s del l births)
    else 0

theorem markedRawGhostSignedCoefficient_neg_rho_eq_abs
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {B : ℕ}
    (V : J → ℝ) (hV : ∀ j,0 ≤ V j) {qStage ρ : ℝ}
    (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) :
    markedRawGhostSignedCoefficient V qStage (-ρ) m z hz del l=
      |markedRawGhostSignedCoefficient V qStage ρ m z hz del l| := by
  unfold markedRawGhostSignedCoefficient
  rw [Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro j _
  have hd : |-(1-qStage)/ρ|=-(1-qStage)/(-ρ) := by
    rw [abs_div,abs_neg,abs_of_nonneg (sub_nonneg.mpr hq₁),abs_of_pos hρ]
    ring
  have hb : |-(1-qStage)*V j/ρ|=-(1-qStage)*V j/(-ρ) := by
    rw [abs_div,abs_mul,abs_neg,abs_of_nonneg (sub_nonneg.mpr hq₁),
      abs_of_nonneg (hV j),abs_of_pos hρ]
    ring
  have hs : |qStage/ρ^2|=qStage/(-ρ)^2 := by
    rw [abs_of_nonneg (div_nonneg hq₀ (sq_nonneg _)),neg_sq]
  simp only [abs_mul,abs_pow,hd,hb,hs]

theorem markedRawGhostSwappedCoefficient_neg_rho_eq_abs
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {B : ℕ}
    (V : J → ℝ) (hV : ∀ j,0 ≤ V j) {qStage ρ : ℝ}
    (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) :
    markedRawGhostSwappedCoefficient V qStage (-ρ) m z hz del l=
      |markedRawGhostSwappedCoefficient V qStage ρ m z hz del l| := by
  unfold markedRawGhostSwappedCoefficient
  rw [Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro j _
  have hd : |-(1-qStage)/ρ|=-(1-qStage)/(-ρ) := by
    rw [abs_div,abs_neg,abs_of_nonneg (sub_nonneg.mpr hq₁),abs_of_pos hρ]
    ring
  have hb : |-(1-qStage)*V j/ρ|=-(1-qStage)*V j/(-ρ) := by
    rw [abs_div,abs_mul,abs_neg,abs_of_nonneg (sub_nonneg.mpr hq₁),
      abs_of_nonneg (hV j),abs_of_pos hρ]
    ring
  have hs : |qStage/ρ^2|=qStage/(-ρ)^2 := by
    rw [abs_of_nonneg (div_nonneg hq₀ (sq_nonneg _)),neg_sq]
  simp only [abs_mul,abs_pow,hd,hb,hs]

/-- The actual absolute ghost action is another literal signed action;
no abstract positive-kernel domination is inserted as a premise. -/
theorem markedRawGhostAbsApply_eq_neg_rho
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j,0 ≤ V j) {qStage ρ : ℝ}
    (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ) :
    markedRawGhostAbsApply ν V qStage ρ hZ f=markedRawGhostApply ν V qStage (-ρ) hZ f := by
  classical
  funext s
  unfold markedRawGhostAbsApply markedRawGhostApply
  apply Finset.sum_congr rfl
  intro del _
  split_ifs
  · apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro births _
    rw [abs_mul,abs_of_nonneg (markedRawGhostBirthMass_nonneg ν hν l births),
      ← markedRawGhostSignedCoefficient_neg_rho_eq_abs V hV hq₀ hq₁ hρ]
  · rfl

theorem markedRawGhostSwappedAbsApply_eq_neg_rho
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j,0 ≤ V j) {qStage ρ : ℝ}
    (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ) :
    markedRawGhostSwappedAbsApply ν V qStage ρ hZ f=
      markedRawGhostSwappedApply ν V qStage (-ρ) hZ f := by
  classical
  funext s
  unfold markedRawGhostSwappedAbsApply markedRawGhostSwappedApply
  apply Finset.sum_congr rfl
  intro del _
  split_ifs
  · apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro births _
    rw [abs_mul,abs_of_nonneg (markedRawGhostBirthMass_nonneg ν hν l births),
      ← markedRawGhostSwappedCoefficient_neg_rho_eq_abs V hV hq₀ hq₁ hρ]
  · rfl

/-- Actual absolute ghost action preserves the same pending-symmetric
space as the original signed operation. -/
theorem markedRawGhostAbsApply_symmetric
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j,0 ≤ V j) {qStage ρ : ℝ}
    (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a,MarkedRawMemorySymmetric (fun m => f (z,(a,m)))) (z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun m => markedRawGhostAbsApply ν V qStage ρ hZ f (z,(a,m))) := by
  rw [markedRawGhostAbsApply_eq_neg_rho ν hν V hV hq₀ hq₁ hρ]
  exact markedRawGhostApply_symmetric ν V qStage (-ρ) hZ f hf z a

end ArtinMatthews
