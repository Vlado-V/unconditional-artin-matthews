module

public import ArtinMatthews.MarkedMinorArcShearOperator
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.RingTheory.Coprime.Lemmas


set_option backward.privateInPublic true
@[expose] public section

/-! Actual projective-line congruences and the shared squarefree lattice in
PD's good-state geometric reduction. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Literal determinant of two integer position vectors. -/
def markedMinorIntegerDet (z v : ℤ × ℤ) : ℤ := z.1*v.2-z.2*v.1

/-- Equality of nonzero projective lines modulo p, expressed by an actual
nonzero scalar in the residue field. -/
def MarkedMinorSamePrimeLine (p : ℕ) (z v : ℤ × ℤ) : Prop :=
  ∃ c : ZMod p, c ≠ 0 ∧ (v.1 : ZMod p)=c*(z.1 : ZMod p) ∧
    (v.2 : ZMod p)=c*(z.2 : ZMod p)

/-- The actual projective-line condition forces determinant divisibility. -/
theorem markedMinorSamePrimeLine_dvd (p : ℕ) (z v : ℤ × ℤ)
    (h : MarkedMinorSamePrimeLine p z v) : (p : ℤ) ∣ markedMinorIntegerDet z v := by
  obtain ⟨c,_,h₁,h₂⟩ := h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [markedMinorIntegerDet,Int.cast_sub,Int.cast_mul,h₁,h₂]
  ring

/-- Preserving every projective line at a squarefree shared product forces
membership in the corresponding determinant-divisibility lattice. -/
theorem markedMinorSamePrimeLines_dvd {D : ℕ} (hD : Squarefree D) (z v : ℤ × ℤ)
    (hline : ∀ p ∈ D.primeFactors, MarkedMinorSamePrimeLine p z v) :
    (D : ℤ) ∣ markedMinorIntegerDet z v := by
  have hprod : (∏ p ∈ D.primeFactors, (p : ℤ)) ∣ markedMinorIntegerDet z v := by
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      have hpc := (Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1
        (Nat.mem_primeFactors.mp hq).1).mpr hpq
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      simpa only [Int.gcd_def,Int.natAbs_natCast] using hpc.gcd_eq_one
    · exact fun p hp => markedMinorSamePrimeLine_dvd p z v (hline p hp)
  have he : (∏ p ∈ D.primeFactors, (p : ℤ)) = (D : ℤ) := by
    exact (map_prod (Nat.castRingHom ℤ) (fun p : ℕ => p) D.primeFactors).symm.trans
      (congrArg (Nat.castRingHom ℤ) (Nat.prod_primeFactors_of_squarefree hD))
  rwa [he] at hprod

/-- A literal determinant-one integer basis gives exact integer coordinates. -/
theorem markedMinorIntegerBasis_decompose (z w v : ℤ × ℤ)
    (hd : markedMinorIntegerDet z w=1) :
    v.1=markedMinorIntegerDet v w*z.1+markedMinorIntegerDet z v*w.1 ∧
    v.2=markedMinorIntegerDet v w*z.2+markedMinorIntegerDet z v*w.2 := by
  unfold markedMinorIntegerDet at hd ⊢
  constructor
  · linear_combination -v.1*hd
  · linear_combination -v.2*hd

/-- This is the actual shared lattice Z*z+Z*D*w, derived from the preserved
prime-line tuple and squarefreeness, not assumed as a support conclusion. -/
theorem markedMinorSharedLattice_of_primeLines {D : ℕ} (hD : Squarefree D)
    (z w v : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hline : ∀ p ∈ D.primeFactors, MarkedMinorSamePrimeLine p z v) :
    ∃ h l : ℤ, v.1=h*z.1+(D : ℤ)*l*w.1 ∧ v.2=h*z.2+(D : ℤ)*l*w.2 := by
  obtain ⟨l,hl⟩ := markedMinorSamePrimeLines_dvd hD z v hline
  have hv := markedMinorIntegerBasis_decompose z w v hd
  rw [hl] at hv
  exact ⟨markedMinorIntegerDet v w,l,hv⟩

end ArtinMatthews
