module

public import ArtinMatthews.PositiveDensityCandidates
public import ArtinMatthews.QuadraticProgressionBranches
public import ArtinMatthews.EnlargedProgressionCounting
public import ArtinMatthews.FinalIndexExclusions
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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

/-! Pulling back the actual enlarged unit classes to the old quadratic
class and the new prime coordinates gives all small-index exclusions. -/

noncomputable section
namespace ArtinMatthews

def giantSieveNewPrimes (S : Finset ℤ) (Y : ℕ) : Finset ℕ :=
  (Nat.primesLE Y).filter fun q => 3 < q ∧ ¬ q ∣ quadraticModulus S

theorem giantSieveNewPrimes_data (S : Finset ℤ) (Y : ℕ) :
    ∀ q ∈ giantSieveNewPrimes S Y, q.Prime ∧ 3 < q ∧ ¬ q ∣ quadraticModulus S := by
  intro q hq
  obtain ⟨hprime, hnew⟩ := Finset.mem_filter.mp hq
  exact ⟨Nat.prime_of_mem_primesLE hprime, hnew⟩

theorem giantSieveEnlargedModulus_pos (S : Finset ℤ) (Y : ℕ) :
    0 < enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y) := by
  rw [enlargedModulus, quadraticModulus]
  exact Nat.mul_pos (Nat.mul_pos (by decide) (Finset.prod_pos fun _ hq =>
    (quadraticPrimeSupport_prime hq).1.pos)) (Finset.prod_pos fun q hq =>
    (giantSieveNewPrimes_data S Y q hq).1.pos)

def giantSieveEnlargedUnits {S : Finset ℤ} {u r₃ : ℕ}
    (hprog : IsQuadraticProgressionFor S u r₃) (Y : ℕ) :
    Finset (ZMod (enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y)))ˣ := by
  letI : NeZero (enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y)) :=
    ⟨(giantSieveEnlargedModulus_pos S Y).ne'⟩
  exact enlargedProgressionUnits (giantSieveNewPrimes_data S Y)
    (ZMod.unitOfCoprime u hprog.2.1)

theorem giantSieve_quadraticSupport_of_dvd {S : Finset ℤ} {q : ℕ}
    (hq : q.Prime) (hq₃ : 3 < q) (hd : q ∣ quadraticModulus S) :
    q ∈ quadraticPrimeSupport S := by
  rcases hq.dvd_mul.mp hd with h8 | hprod
  · have htwo := hq.dvd_of_dvd_pow (show q ∣ 2 ^ 3 by exact h8)
    have hqle := Nat.le_of_dvd (by decide : 0 < 2) htwo
    omega
  · obtain ⟨r, hr, hqr⟩ := (hq.prime.dvd_finsetProd_iff (fun r : ℕ => r)).mp hprod
    have heq := (Nat.prime_dvd_prime_iff_eq hq (quadraticPrimeSupport_prime hr).1).mp hqr
    exact heq ▸ hr

theorem giantSieve_enlarged_prime_conditions {S : Finset ℤ} {u r₃ Y p : ℕ}
    (hprog : IsQuadraticProgressionFor S u r₃) (hp : p.Prime)
    (hU : ∃ v ∈ giantSieveEnlargedUnits hprog Y,
      (v : ZMod (enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y))) = p) :
    p ≠ 2 ∧ p % 3 = r₃ ∧ (∀ a ∈ S, @legendreSym p ⟨hp⟩ a = -1) ∧
      ∀ q : ℕ, q.Prime → 3 < q → q ≤ Y → p % q ≠ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let P := giantSieveNewPrimes S Y
  let M₀ := quadraticModulus S
  let : NeZero (enlargedModulus M₀ P) := ⟨(giantSieveEnlargedModulus_pos S Y).ne'⟩
  obtain ⟨v, hv, hvp⟩ := hU
  have h := (mem_enlargedProgressionUnits_iff (giantSieveNewPrimes_data S Y)
    (ZMod.unitOfCoprime u hprog.2.1) v).mp hv
  have hproj := congrArg Units.val h.1
  change ZMod.castHom _ (ZMod M₀) (v : ZMod (enlargedModulus M₀ P)) =
    (ZMod.unitOfCoprime u hprog.2.1 : ZMod M₀) at hproj
  rw [hvp, map_natCast, ZMod.coe_unitOfCoprime] at hproj
  have hpu : p ≡ u [MOD M₀] := (ZMod.natCast_eq_natCast_iff p u M₀).mp hproj
  obtain ⟨hp₂, hp₃, hquad, hold⟩ := hprog.2.2 p hpu
  refine ⟨hp₂, hp₃, hquad, ?_⟩
  intro q hq hq₃ hqY
  by_cases hd : q ∣ M₀
  · exact hold q (giantSieve_quadraticSupport_of_dvd hq hq₃ hd) hq₃
  · have hqP : q ∈ P :=
      Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hqY, hq⟩, hq₃, hd⟩
    intro hpq
    apply h.2 q hqP
    apply Units.ext
    change ZMod.castHom _ (ZMod q) (v : ZMod (enlargedModulus M₀ P)) = 1
    rw [hvp, map_natCast, ← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff' p 1 q).mpr
      (hpq.trans (Nat.mod_eq_of_lt hq.one_lt).symm)

theorem giantSieveCandidate_enlarged_no_small_index
    {S : Finset ℤ} {u r₃ Y p : ℕ} (hprog : IsQuadraticProgressionFor S u r₃)
    {select : ℕ → Prop} {ε T x : ℝ} {Φ : ℝ → ℝ}
    (hselect : ∀ p, select p → r₃ = 2 ∨ ∀ a ∈ S, ¬ IsCubeMod p a)
    (hp : p ∈ giantSieveCandidates (giantSieveEnlargedUnits hprog Y) select ε Φ T x)
    (hnonzero : ∀ a ∈ S, (a : ZMod p) ≠ 0) :
    ∀ a ∈ S, ∀ q : ℕ, q.Prime → q ≤ Y → ¬ q ∣ multiplicativeIndex p a := by
  have hprime := giantSieveCandidate_prime hp
  obtain ⟨hp₂, hp₃, hquad, havoid⟩ :=
    giantSieve_enlarged_prime_conditions hprog hprime (mem_giantSieveCandidates.mp hp).2.1
  have hcubic : p % 3 = 2 ∨ ∀ a ∈ S, ¬ IsCubeMod p a := by
    rcases hselect p (mem_giantSieveCandidates.mp hp).2.2.1 with hr | hcube
    · exact Or.inl (hp₃.trans hr)
    · exact Or.inr hcube
  exact no_small_index_prime_of_quadratic_cubic hprime hp₂ hnonzero hquad hcubic havoid

end ArtinMatthews
