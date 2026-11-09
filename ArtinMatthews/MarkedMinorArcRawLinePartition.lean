module

public import ArtinMatthews.MarkedRootProjectiveRootLift
public import ArtinMatthews.MarkedMinorArcProjectiveLine


set_option backward.privateInPublic true
@[expose] public section

/-! The literal shared-determinant restriction in the raw edge is exactly
partition by the actual projective line tuple of primitive positions. -/
namespace ArtinMatthews

/-- Equality of actual primitive projective residues is precisely the literal
nonzero scalar relation used in the shared-lattice arithmetic. -/
theorem markedPrimePositionLine_eq_iff_same (p : ℕ) [Fact p.Prime]
    (z v : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (hv : IsCoprime v.1 v.2) :
    markedPrimePositionLine p z hz=markedPrimePositionLine p v hv ↔
      MarkedMinorSamePrimeLine p z v := by
  rw [eq_comm]
  unfold markedPrimePositionLine
  rw [Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,Units.ne_zero a,?_,?_⟩
    · have hh := congrFun ha 0
      simpa [Units.smul_def,smul_eq_mul] using hh.symm
    · have hh := congrFun ha 1
      simpa [Units.smul_def,smul_eq_mul] using hh.symm
  · rintro ⟨a,ha,h₀,h₁⟩
    refine ⟨Units.mk0 a ha,?_⟩
    ext i
    fin_cases i
    · simpa [Units.smul_def,smul_eq_mul] using h₀.symm
    · simpa [Units.smul_def,smul_eq_mul] using h₁.symm

/-- Every actual primitive integer source position has a determinant-one
integer complement, as required by the source shared-line argument. -/
theorem markedPrimitivePosition_completion (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    ∃ w : ℤ × ℤ, markedMinorIntegerDet z w=1 := by
  obtain ⟨a,b,hab⟩ := hz
  refine ⟨(-b,a),?_⟩
  unfold markedMinorIntegerDet
  dsimp
  linear_combination hab

/-- The actual tuple of projective residues of one primitive position. -/
def markedRawPositionLineTuple (D : ℕ) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) : MarkedRootLineTuple D :=
  fun p => markedPrimePositionLine (p : ℕ) z hz

/-- The shared-product divisibility gate is exactly a diagonal block gate in
the actual position-line tuple. No congruence independence is assumed. -/
theorem markedRawPositionLineTuple_eq_iff {D : ℕ} (hD : Squarefree D)
    (z v : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (hv : IsCoprime v.1 v.2) :
    markedRawPositionLineTuple D z hz=markedRawPositionLineTuple D v hv ↔
      (D : ℤ) ∣ markedMinorIntegerDet z v := by
  constructor
  · intro he
    apply markedMinorSamePrimeLines_dvd hD z v
    intro p hp
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    apply (markedPrimePositionLine_eq_iff_same p z v hz hv).mp
    exact congrFun he ⟨p,hp⟩
  · intro hd
    obtain ⟨w,hw⟩ := markedPrimitivePosition_completion z hz
    funext p
    apply (markedPrimePositionLine_eq_iff_same (p : ℕ) z v hz hv).mpr
    apply (markedMinorSamePrimeLine_iff_dvd (Nat.prime_of_mem_primeFactors p.2) z w v hw hv).mpr
    exact (by exact_mod_cast Nat.dvd_of_mem_primeFactors p.2 : ((p : ℕ) : ℤ) ∣ (D : ℤ)).trans hd

end ArtinMatthews
