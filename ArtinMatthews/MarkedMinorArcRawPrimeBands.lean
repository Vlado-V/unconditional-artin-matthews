module

public import ArtinMatthews.MarkedMinorArcDirtyFresh
public import ArtinMatthews.MarkedMinorArcRawState
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

/-! Exact adapter from the actual natural-number prime bands to prime-typed
raw states; the atoms and factorial measure are literally the PD weights. -/
namespace ArtinMatthews
open Filter

/-- The same finite prime band, with its already proved primality in the type. -/
def markedRawPrimeBand (P : Finset ℕ) : Finset Nat.Primes := P.subtype Nat.Prime

theorem mem_markedRawPrimeBand (P : Finset ℕ) (p : Nat.Primes) :
    p ∈ markedRawPrimeBand P ↔ (p : ℕ) ∈ P := Finset.mem_subtype

/-- No prime-band element is lost or added by the typed-state representation. -/
def markedRawPrimeBandEquiv (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ↥(markedRawPrimeBand P) ≃ ↥P where
  toFun p := ⟨(p.1 : ℕ),(mem_markedRawPrimeBand P p.1).mp p.2⟩
  invFun p := ⟨⟨p.1,hP p.1 p.2⟩,(mem_markedRawPrimeBand P _).mpr p.2⟩
  left_inv _p := rfl
  right_inv _p := rfl

noncomputable def markedRawActualPrimeBand {J : Type*} (e : J → ℝ) (x : ℝ)
    (j : J) : Finset Nat.Primes := markedRawPrimeBand (markedLogPowerBand (e j) x)

noncomputable def markedRawActualPrimeAtom {J : Type*} (e : J → ℝ) (q x : ℝ)
    (j : J) (p : ↥(markedRawActualPrimeBand e x j)) : ℝ :=
  markedMemoryPrimeAtom (bandReciprocalMass (markedLogPowerBand (e j) x))
    q (markedMemoryMomentLength x) (p.1 : ℕ)

/-- The adapter preserves the exact tilted prime atom, including actualN(x)
and the original natural-band normalizer. -/
theorem markedRawActualPrimeAtom_eq_tilted {J : Type*} (e : J → ℝ) (q x : ℝ)
    (j : J) (p : ↥(markedRawActualPrimeBand e x j)) :
    markedRawActualPrimeAtom e q x j p=
      markedTiltedBandAtom (markedLogPowerBand (e j) x) q (markedMemoryMomentLength x)
        ((markedRawPrimeBandEquiv _ (fun _ hp => (mem_markedLogPowerBand.mp hp).1)) p) := rfl

/-- The literal actual raw-state measure is nonnegative for the actual
moment length and all permitted bands, uniformly in growing state sizes. -/
theorem markedRawActualStateMass_nonneg_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ (M B : ℕ) (Z : Finset (ℤ × ℤ)),
      ∀ s : MarkedRawState (markedRawActualPrimeBand e x) M B Z,
        0 ≤ markedRawStateMass (markedRawActualPrimeAtom e q x) s := by
  filter_upwards [marked_actual_tilted_atom_comparison_eventually e he] with x hx
  intro q hq0 hq1 M B Z s
  apply markedRawStateMass_nonneg
  intro j p
  rw [markedRawActualPrimeAtom_eq_tilted]
  exact (hx q hq0 hq1 j _).1

end ArtinMatthews
