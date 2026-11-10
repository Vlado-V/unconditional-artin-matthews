module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.TwoPoint.Halasz.HalaszLongShortCongruences
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovDiagonal
public import Mathlib.Tactic.Basify
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
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszEnergyDiagonal
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszEnergyImage
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszLongShortEnergy


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Splitting the complete system into long and short tuples, and the
diagonal lower bound used to absorb colliding long variables. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

def halaszTupleJoin (a b N : ℕ) :
    ((Fin a → Fin N) × (Fin b → Fin N)) ≃ (Fin (a+b) → Fin N) where
  toFun x := Fin.append x.1 x.2
  invFun y := (fun i => y (i.castAdd b),fun i => y (i.natAdd a))
  left_inv x := by
    apply Prod.ext <;> funext i <;> simp
  right_inv y := Fin.append_castAdd_natAdd

lemma halasz_join_frequency {a b k N : ℕ} (x : (Fin a → Fin N) × (Fin b → Fin N)) :
    halaszNatPowerFrequency k (halaszTupleJoin a b N x) =
      halaszNatPowerFrequency k x.1+halaszNatPowerFrequency k x.2 := by
  funext j
  unfold halaszNatPowerFrequency halaszTupleJoin
  rw [Fin.sum_univ_add]
  simp only [Equiv.coe_fn_mk,Fin.append_left,Fin.append_right,Pi.add_apply]

theorem halasz_vinogradov_product_count (a b k N : ℕ) :
    halaszFiberEnergy ((univ : Finset (Fin a → Fin N))×ˢ(univ : Finset (Fin b → Fin N)))
      (fun x => halaszNatPowerFrequency k x.1+halaszNatPowerFrequency k x.2) =
      halaszVinogradovCount (a+b) k N := by
  let e := halaszTupleJoin a b N
  have he := halasz_fiber_energy_image
    (univ : Finset ((Fin a → Fin N) × (Fin b → Fin N))) e e.injective.injOn
    (halaszNatPowerFrequency k)
  have he' : halaszFiberEnergy (univ : Finset (Fin (a+b) → Fin N))
      (halaszNatPowerFrequency k) =
      halaszFiberEnergy (univ : Finset ((Fin a → Fin N) × (Fin b → Fin N)))
        (fun x => halaszNatPowerFrequency k (e x)) := by
    convert he using 1
    congr 1
    ext y
    simp only [mem_image,mem_univ,true_and,true_iff]
    exact e.surjective y
  rw [halasz_nat_power_energy] at he'
  rw [he']
  simp only [univ_product_univ]
  apply halasz_fiber_energy_congr
  intro x _ y _
  rw [halasz_join_frequency,halasz_join_frequency]

theorem halasz_vinogradov_diagonal_extension (s k N : ℕ) :
    N^k*halaszVinogradovCount s k N ≤ halaszVinogradovCount (k+s) k N := by
  have h := halasz_energy_diagonal_lower
    (univ : Finset (Fin k → Fin N)) (univ : Finset (Fin s → Fin N))
    (halaszNatPowerFrequency k) (halaszNatPowerFrequency k)
  rw [halasz_nat_power_energy,halasz_vinogradov_product_count] at h
  simpa using h

end TwoPointCorrelations

end OAI
