module

public import ArtinMatthews.MarkedRootProjectiveCRT
public import ArtinMatthews.MarkedRootProjectiveIncidence


set_option backward.privateInPublic true
@[expose] public section

/-! Compatibility of the actual integral root matrix, squarefree CRT,
and literal prime-hit projective incidence. -/
namespace ArtinMatthews
open scoped LinearAlgebra.Projectivization

/-- The CRT component of the actual reduced integral root is its actual
reduction at that prime, retaining every matrix entry. -/
theorem markedRootCRT_integer_reduction {S : ℕ} (hS : Squarefree S)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (p : S.primeFactors) :
    (markedSquarefreeRootCRT hS
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) g)) p =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (p : ℕ))) g := by
  ext i j
  change (squarefreeZModPrimeEquiv hS (g i j : ZMod S)) p=(g i j : ZMod (p : ℕ))
  rw [map_intCast]
  rfl

/-- Every actual prime-hit indicator in the integral root lift is evaluation
of the corresponding independent kernel-line coordinate. -/
theorem markedRootKernelTuple_prime_hit_iff {S : ℕ} (hS : Squarefree S)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (p : S.primeFactors)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    ((p : ℕ) : ℤ) ∣ g 0 0*z.1+g 0 1*z.2 ↔
      markedPrimePositionLine (p : ℕ) z hz =
        markedRootKernelTuple hS (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) g) p := by
  unfold markedRootKernelTuple
  rw [markedRootCRT_integer_reduction]
  exact markedIntegerRoot_prime_hit_iff (p : ℕ) g z hz

end ArtinMatthews
