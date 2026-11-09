module

public import ArtinMatthews.MarkedMemoryTiltPrimewiseGhost


set_option backward.privateInPublic true
@[expose] public section

/-! Primewise identities on the actual projective line over F_p, using
the literal primitive integer positions and q_j=sqrt(q),q,...,sqrt(q).
The line probability 1/(p+1) is the genuine uniform-root probability. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedMemoryPositionLines (p : Nat.Primes) {N : ℕ} (z : Fin (N+1) → ℤ × ℤ)
    (hz : ∀ j, IsCoprime (z j).1 (z j).2) : Fin (N+1) → MarkedRawPrimeLine p :=
  fun j => markedPrimePositionLine (p : ℕ) (z j) (hz j)

theorem markedMemoryPrimeLine_card (p : Nat.Primes) :
    Fintype.card (MarkedRawPrimeLine p) = (p : ℕ)+1 := by
  rw [Fintype.card_eq_nat_card]
  exact markedProjectiveLine_card (p : ℕ)

def markedMemoryProjectiveFactor (p : Nat.Primes) {N : ℕ} (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ j, IsCoprime (z j).1 (z j).2)
    (A : Finset (Fin (N+1))) : ℝ :=
  markedMemoryPrimeFactor A (markedMemoryEta q N) (markedMemoryPositionLines p z hz)

def markedMemoryOrphanGhostSum {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) : ℝ :=
  ∑ a : Fin (N+1), ∑ c ∈ Finset.univ.filter (fun c => a<c),
    if line a = line c then η a*η c *
      ∏ j ∈ Finset.univ.filter (fun j => a<j ∧ j<c), (1-η j*markedLineHit line j (line a))
    else 0

/-- The actual prime's empty-active factor, with precisely the singleton
baseline extracted and no single-ghost lifespan inserted. -/
theorem markedMemoryProjectiveFactor_empty (p : Nat.Primes) {N : ℕ} (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ j, IsCoprime (z j).1 (z j).2) :
    markedMemoryProjectiveFactor p q z hz ∅ = markedMemoryBaseline q N p +
      (1 / ((p : ℝ)+1))*markedMemoryOrphanGhostSum (markedMemoryEta q N) (markedMemoryPositionLines p z hz) := by
  classical
  have : Nonempty (MarkedRawPrimeLine p) := ⟨markedMemoryPositionLines p z hz 0⟩
  have hh := marked_memory_orphan_line_average (Finset.univ : Finset (Fin (N+1)))
    (markedMemoryEta q N) (markedMemoryPositionLines p z hz)
  simpa only [markedMemoryProjectiveFactor, markedMemoryPrimeFactor, Finset.prod_empty,
    Finset.sdiff_empty, one_mul, markedMemoryPrimeLine_card, Nat.cast_add, Nat.cast_one,
    markedMemoryBaseline, markedMemoryOrphanGhostSum] using hh

/-- The actual nonempty-active factor: the line-coincidence condition is
retained, and the first and last active visits are genuine finite minima
and maxima, rather than assumed endpoints. -/
theorem markedMemoryProjectiveFactor_active (p : Nat.Primes) {N : ℕ} (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ j, IsCoprime (z j).1 (z j).2)
    (A : Finset (Fin (N+1))) (hA : A.Nonempty) :
    markedMemoryProjectiveFactor p q z hz A = (1 / ((p : ℝ)+1))*
      (if MarkedMemoryActiveCoherent A (markedMemoryPositionLines p z hz) (A.min' hA) then
        markedMemoryPrefixGhost (markedMemoryEta q N) (markedMemoryPositionLines p z hz) (A.min' hA) *
        markedMemoryInternalDamping A (markedMemoryEta q N) (markedMemoryPositionLines p z hz) (A.min' hA) (A.max' hA) *
        markedMemorySuffixGhost (markedMemoryEta q N) (markedMemoryPositionLines p z hz) (A.min' hA) (A.max' hA)
      else 0) := by
  simpa only [markedMemoryProjectiveFactor, markedMemoryPrimeLine_card, Nat.cast_add, Nat.cast_one] using
    markedMemoryPrimeFactor_active_ghosts A hA (markedMemoryEta q N) (markedMemoryPositionLines p z hz)

/-- Normalization of the nonempty active factor gives precisely one
tilted birth factor V*nu before the active-run V⁻¹ charges are included. -/
theorem markedMemoryProjectiveFactor_active_normalized (p : Nat.Primes) {N : ℕ} (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ j, IsCoprime (z j).1 (z j).2)
    (A : Finset (Fin (N+1))) (hA : A.Nonempty) {V : ℝ} (hV : V ≠ 0)
    (hb : markedMemoryBaseline q N p ≠ 0) :
    markedMemoryProjectiveFactor p q z hz A / markedMemoryBaseline q N p =
      (V*markedMemoryPrimeAtom V q N p)*
      (if MarkedMemoryActiveCoherent A (markedMemoryPositionLines p z hz) (A.min' hA) then
        markedMemoryPrefixGhost (markedMemoryEta q N) (markedMemoryPositionLines p z hz) (A.min' hA) *
        markedMemoryInternalDamping A (markedMemoryEta q N) (markedMemoryPositionLines p z hz) (A.min' hA) (A.max' hA) *
        markedMemorySuffixGhost (markedMemoryEta q N) (markedMemoryPositionLines p z hz) (A.min' hA) (A.max' hA)
      else 0) := by
  rw [markedMemoryProjectiveFactor_active p q z hz A hA]
  unfold markedMemoryPrimeAtom
  field_simp

theorem markedMemoryProjectiveFactor_empty_normalized (p : Nat.Primes) {N : ℕ} (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ j, IsCoprime (z j).1 (z j).2)
    {V : ℝ} (hV : V ≠ 0) (hb : markedMemoryBaseline q N p ≠ 0) :
    markedMemoryProjectiveFactor p q z hz ∅ / markedMemoryBaseline q N p =
      1+(V*markedMemoryPrimeAtom V q N p)*
        markedMemoryOrphanGhostSum (markedMemoryEta q N) (markedMemoryPositionLines p z hz) := by
  rw [markedMemoryProjectiveFactor_empty]
  unfold markedMemoryPrimeAtom
  field_simp

/-- The active set in the source is the literal occurrence set of p in
the path's actual typed active lists. This specialization introduces no
independent active-set or source-factor identity hypothesis. -/
theorem markedMemoryProjectiveFactor_active_slots {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M N : ℕ} (slots : Fin (N+1) → MarkedRawActive P M)
    (p : Nat.Primes) (q : ℝ) (z : Fin (N+1) → ℤ × ℤ)
    (hz : ∀ j, IsCoprime (z j).1 (z j).2) (hA : (markedMemoryActiveVisits slots p).Nonempty) :
    markedMemoryProjectiveFactor p q z hz (markedMemoryActiveVisits slots p) =
      (1 / ((p : ℝ)+1))*
      (if MarkedMemoryActiveCoherent (markedMemoryActiveVisits slots p) (markedMemoryPositionLines p z hz)
          ((markedMemoryActiveVisits slots p).min' hA) then
        markedMemoryPrefixGhost (markedMemoryEta q N) (markedMemoryPositionLines p z hz)
          ((markedMemoryActiveVisits slots p).min' hA) *
        markedMemoryInternalDamping (markedMemoryActiveVisits slots p) (markedMemoryEta q N)
          (markedMemoryPositionLines p z hz) ((markedMemoryActiveVisits slots p).min' hA)
          ((markedMemoryActiveVisits slots p).max' hA) *
        markedMemorySuffixGhost (markedMemoryEta q N) (markedMemoryPositionLines p z hz)
          ((markedMemoryActiveVisits slots p).min' hA) ((markedMemoryActiveVisits slots p).max' hA)
      else 0) := markedMemoryProjectiveFactor_active p q z hz _ hA

end ArtinMatthews
