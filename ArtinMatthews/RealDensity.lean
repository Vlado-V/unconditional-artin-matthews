module

public import ArtinMatthews.Density
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Set.Card


set_option backward.privateInPublic true
@[expose] public section

/-!
# Relative prime density at real cutoffs

Natural floors give exactly the count of simultaneous primitive-root primes
in the real interval `[1,x]`. The liminf at real cutoffs equals the natural
cutoff liminf. A finite simultaneous-prime set has relative density zero.
-/

open Filter
open scoped Topology Classical

namespace ArtinMatthews

/-- Number of simultaneous primitive-root primes in the real interval `[1,x]`. -/
noncomputable def realPrimeCount (S : Finset ℤ) (x : ℝ) : ℕ :=
  primeCount S ⌊x⌋₊

/-- Relative prime density at a real cutoff, as in the paper. -/
noncomputable def realRelativePrimeDensity (S : Finset ℤ) (x : ℝ) : ℝ :=
  (realPrimeCount S x : ℝ) / (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- The paper's positivity condition, using real cutoffs. -/
def PositiveRealLowerRelativePrimeDensity (S : Finset ℤ) : Prop :=
  0 < liminf (realRelativePrimeDensity S) atTop

/-- The finite set used by the floor count is exactly the set in `[1,x]`. -/
theorem mem_floor_primeCount_finset {S : Finset ℤ} {x : ℝ} {p : ℕ} :
    p ∈ (⌊x⌋₊.primesLE.filter fun q => q ∈ SimultaneousPrimitivePrimes S) ↔
      p ∈ SimultaneousPrimitivePrimes S ∧ 1 ≤ (p : ℝ) ∧ (p : ℝ) ≤ x := by
  classical
  constructor
  · intro hp
    obtain ⟨hple, hS⟩ := Finset.mem_filter.mp hp
    have hpprime := hS.1
    refine ⟨hS, ?_, ?_⟩
    · exact_mod_cast hpprime.one_lt.le
    · exact (Nat.le_floor_iff' hpprime.ne_zero).mp (Nat.mem_primesLE.mp hple).1
  · rintro ⟨hS, _, hpx⟩
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr
      ⟨Nat.le_floor hpx, hS.1⟩, hS⟩

/-- Cardinality identity for the interval formulation of the paper's count. -/
theorem realPrimeCount_eq_ncard (S : Finset ℤ) (x : ℝ) :
    realPrimeCount S x =
      {p : ℕ | p ∈ SimultaneousPrimitivePrimes S ∧
        1 ≤ (p : ℝ) ∧ (p : ℝ) ≤ x}.ncard := by
  classical
  unfold realPrimeCount primeCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  exact mem_floor_primeCount_finset

@[simp]
theorem realRelativePrimeDensity_natCast (S : Finset ℤ) (n : ℕ) :
    realRelativePrimeDensity S (n : ℝ) = relativePrimeDensity S n := by
  simp [realRelativePrimeDensity, realPrimeCount, relativePrimeDensity]

/-- Natural floor maps the real filter at infinity onto the natural filter. -/
theorem map_natFloor_atTop :
    Filter.map (fun x : ℝ => ⌊x⌋₊) atTop = atTop := by
  apply le_antisymm (tendsto_nat_floor_atTop (α := ℝ))
  calc
    (atTop : Filter ℕ) = Filter.map (fun x : ℝ => ⌊x⌋₊)
        (Filter.map (fun n : ℕ => (n : ℝ)) atTop) := by
      simp only [Filter.map_map, Function.comp_def, Nat.floor_natCast, Filter.map_id']
    _ ≤ Filter.map (fun x : ℝ => ⌊x⌋₊) atTop :=
      Filter.map_mono (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

/-- Passing from natural cutoffs to real cutoffs does not change the liminf. -/
theorem realRelativePrimeDensity_liminf_eq (S : Finset ℤ) :
    liminf (realRelativePrimeDensity S) atTop = liminf (relativePrimeDensity S) atTop := by
  change liminf (relativePrimeDensity S ∘ (fun x : ℝ => ⌊x⌋₊)) atTop = _
  rw [Filter.liminf_comp, map_natFloor_atTop]

/-- The natural and real positivity formulations are equivalent. -/
theorem positiveRealLowerRelativePrimeDensity_iff (S : Finset ℤ) :
    PositiveRealLowerRelativePrimeDensity S ↔ PositiveLowerRelativePrimeDensity S := by
  unfold PositiveRealLowerRelativePrimeDensity PositiveLowerRelativePrimeDensity
  rw [realRelativePrimeDensity_liminf_eq]

/-- A proved dyadic lower bound gives precisely the paper's real-cutoff positivity. -/
theorem PositiveDyadicLowerBound.positiveRealLowerRelativePrimeDensity
    {S : Finset ℤ} (h : PositiveDyadicLowerBound S) :
    PositiveRealLowerRelativePrimeDensity S :=
  (positiveRealLowerRelativePrimeDensity_iff S).mpr h.positiveLowerRelativePrimeDensity

/-- A finite simultaneous-prime set bounds every initial counting function. -/
theorem primeCount_le_card_of_finite {S : Finset ℤ}
    (hfinite : (SimultaneousPrimitivePrimes S).Finite) (n : ℕ) :
    primeCount S n ≤ hfinite.toFinset.card := by
  classical
  unfold primeCount
  apply Finset.card_le_card
  intro p hp
  exact hfinite.mem_toFinset.mpr (Finset.mem_filter.mp hp).2

/-- A finite simultaneous-prime set has relative density tending to zero. -/
theorem tendsto_relativePrimeDensity_zero_of_finite {S : Finset ℤ}
    (hfinite : (SimultaneousPrimitivePrimes S).Finite) :
    Tendsto (relativePrimeDensity S) atTop (𝓝 0) := by
  unfold relativePrimeDensity
  apply tendsto_bdd_div_atTop_nhds_zero
    (b := 0) (B := (hfinite.toFinset.card : ℝ))
  · exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · exact Eventually.of_forall (fun n => by exact_mod_cast primeCount_le_card_of_finite hfinite n)
  · exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
      Nat.tendsto_primeCounting

/-- The zero-density limit holds at real cutoffs as well. -/
theorem tendsto_realRelativePrimeDensity_zero_of_finite {S : Finset ℤ}
    (hfinite : (SimultaneousPrimitivePrimes S).Finite) :
    Tendsto (realRelativePrimeDensity S) atTop (𝓝 0) :=
  (tendsto_relativePrimeDensity_zero_of_finite hfinite).comp tendsto_nat_floor_atTop

/-- In particular, a finite simultaneous-prime set has lower relative density zero. -/
theorem realRelativePrimeDensity_liminf_zero_of_finite {S : Finset ℤ}
    (hfinite : (SimultaneousPrimitivePrimes S).Finite) :
    liminf (realRelativePrimeDensity S) atTop = 0 :=
  (tendsto_realRelativePrimeDensity_zero_of_finite hfinite).liminf_eq

end ArtinMatthews
