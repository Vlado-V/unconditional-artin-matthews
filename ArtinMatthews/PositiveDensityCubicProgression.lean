module

public import ArtinMatthews.PositiveDensityCandidateCRT
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! The actual enlarged unit classes themselves satisfy the reduction
modulo three required in the split Frobenius branch of Theorem 1.2. -/

noncomputable section
namespace ArtinMatthews

theorem giantSieve_three_dvd_quadraticModulus (S : Finset ℤ) :
    3 ∣ quadraticModulus S :=
  (Finset.dvd_prod_of_mem (fun q : ℕ => q)
    (Finset.mem_insert_self 3 ((∏ a ∈ S, a.natAbs).primeFactors.erase 2))).trans
      (dvd_mul_left _ 8)

theorem giantSieve_three_dvd_enlargedModulus (S : Finset ℤ) (Y : ℕ) :
    3 ∣ enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y) :=
  (giantSieve_three_dvd_quadraticModulus S).trans (dvd_mul_right _ _)

theorem giantSieve_quadratic_class_mod_three {S : Finset ℤ} {u r₃ : ℕ}
    (hprog : IsQuadraticProgressionFor S u r₃) : u % 3 = r₃ := by
  have hM : 0 < quadraticModulus S :=
    Nat.mul_pos (by decide) (Finset.prod_pos fun _ hq => (quadraticPrimeSupport_prime hq).1.pos)
  obtain ⟨p, _, hp, hpu⟩ := Nat.forall_exists_prime_gt_and_modEq 0 hM.ne' hprog.2.1
  let : Fact p.Prime := ⟨hp⟩
  have hmod : p % 3 = u % 3 := hpu.of_dvd (giantSieve_three_dvd_quadraticModulus S)
  exact hmod.symm.trans (hprog.2.2 p hpu).2.1

theorem giantSieve_enlarged_unit_mod_three {S : Finset ℤ} {u r₃ : ℕ}
    (hprog : IsQuadraticProgressionFor S u r₃) (Y : ℕ)
    {v : (ZMod (enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y)))ˣ}
    (hv : v ∈ giantSieveEnlargedUnits hprog Y) :
    ZMod.castHom (giantSieve_three_dvd_enlargedModulus S Y) (ZMod 3) ↑v = (r₃ : ZMod 3) := by
  let P := giantSieveNewPrimes S Y
  let M₀ := quadraticModulus S
  let M := enlargedModulus M₀ P
  let : NeZero M := ⟨(giantSieveEnlargedModulus_pos S Y).ne'⟩
  have hd : M₀ ∣ M := dvd_mul_right _ _
  have h₃ : 3 ∣ M₀ := giantSieve_three_dvd_quadraticModulus S
  have h := (mem_enlargedProgressionUnits_iff (giantSieveNewPrimes_data S Y)
    (ZMod.unitOfCoprime u hprog.2.1) v).mp hv
  have hbase := congrArg Units.val h.1
  change ZMod.castHom hd (ZMod M₀) (v : ZMod M) =
    (ZMod.unitOfCoprime u hprog.2.1 : ZMod M₀) at hbase
  rw [ZMod.coe_unitOfCoprime] at hbase
  have hu := giantSieve_quadratic_class_mod_three hprog
  calc
    _ = ZMod.castHom h₃ (ZMod 3) (ZMod.castHom hd (ZMod M₀) (v : ZMod M)) := by
      exact congrArg (fun f : ZMod M →+* ZMod 3 => f (v : ZMod M))
        (ZMod.castHom_comp h₃ hd).symm
    _ = (u : ZMod 3) := by rw [hbase, map_natCast]
    _ = _ := by
      rw [← ZMod.natCast_zmod_val (u : ZMod 3), ZMod.val_natCast, hu]

end ArtinMatthews
