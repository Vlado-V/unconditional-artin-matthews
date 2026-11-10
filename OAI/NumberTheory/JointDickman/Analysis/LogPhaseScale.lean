module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Basify


set_option backward.privateInPublic true
@[expose] public section

namespace OAI
noncomputable section

namespace JointDickman

/-- Choose a bounded derivative order placing the logarithmic phase in the
second-derivative scale after differencing. -/
theorem logarithmic_phase_order {U Z B : ℝ} (hU : 1 < U) (_hB : 1/2 ≤ B)
    (hlower : U ^ (1/2:ℝ) ≤ |Z|) (hupper : |Z| ≤ U ^ B) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ Nat.ceil B + 1 ∧
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) ∧
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) := by
  have hU0 : 0 < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hZ0 : 0 < |Z| := (Real.rpow_pos_of_pos hU0 (1/2:ℝ)).trans_le hlower
  let a : ℝ := Real.log |Z| / Real.log U
  have ha4 : 1/2 ≤ a := by
    apply (le_div_iff₀ hlogU).2
    have h := Real.log_le_log (Real.rpow_pos_of_pos hU0 (1/2:ℝ)) hlower
    simpa only [Real.log_rpow hU0] using h
  have haB : a ≤ B := by
    apply (div_le_iff₀ hlogU).2
    have h := Real.log_le_log hZ0 hupper
    rwa [Real.log_rpow hU0] at h
  let k : ℕ := Nat.floor (a + 1 / 2)
  have ha0 : 0 ≤ a + 1 / 2 := by linarith
  have hklo : (k : ℝ) ≤ a + 1 / 2 := Nat.floor_le ha0
  have hkhi : a + 1 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk4 : 1 ≤ k := (Nat.le_floor_iff ha0).2 (by norm_num; linarith)
  have hkB : k ≤ Nat.ceil B + 1 := by
    have hceil := Nat.le_ceil B
    have h : (k : ℝ) ≤ (Nat.ceil B : ℝ) + 1 := by linarith
    exact_mod_cast h
  have hZa : |Z| = U ^ a := by
    rw [Real.rpow_def_of_pos hU0]
    have heq : Real.log U * a = Real.log |Z| := by
      dsimp [a]
      field_simp
    rw [heq, Real.exp_log hZ0]
  refine ⟨k, hk4, hkB, ?_, ?_⟩ <;>
    rw [hZa, ← Real.rpow_add hU0]
  · exact Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)

/-- The product of a bounded number of short shifts costs at most `U^(1/10)`. -/
theorem logarithmic_shift_product {U : ℝ} (hU : 1 < U) {k : ℕ} (hk : 1 ≤ k)
    (hs : List ℝ) (hlen : hs.length ≤ k)
    (hhs : ∀ h ∈ hs, 1 ≤ h ∧ h ≤ U ^ (1 / (10 * (k : ℝ)))) :
    1 ≤ hs.prod ∧ hs.prod ≤ U ^ ((1 : ℝ) / 10) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hU0 : 0 < U := by linarith
  refine ⟨List.one_le_prod (fun h hh => (hhs h hh).1), ?_⟩
  have hp : hs.prod ≤ (U ^ (1 / (10 * (k : ℝ)))) ^ hs.length := by
    have h := List.prod_map_le_prod_map₀ (s := hs) (fun x : ℝ => x)
      (fun _ => U ^ (1 / (10 * (k : ℝ))))
      (fun h hh => le_trans (by norm_num) (hhs h hh).1)
      (fun h hh => (hhs h hh).2)
    simpa [List.map_const, List.prod_replicate] using h
  rw [← Real.rpow_mul_natCast hU0.le] at hp
  apply hp.trans
  apply Real.rpow_le_rpow_of_exponent_le hU.le
  have hlenR : (hs.length : ℝ) ≤ k := by exact_mod_cast hlen
  calc
    1 / (10 * (k : ℝ)) * (hs.length : ℝ) = (hs.length : ℝ) / (10 * (k : ℝ)) := by ring
    _ ≤ 1 / 10 := (div_le_iff₀ (by positivity)).2 (by nlinarith)

/-- The derivative scale after the short shifts is uniformly a small negative power. -/
theorem logarithmic_phase_shift_scale {U Z : ℝ} (hU : 1 < U) {k : ℕ} (hk : 1 ≤ k)
    (hlower : U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)))
    (hupper : |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2))
    (hs : List ℝ) (hlen : hs.length ≤ k)
    (hhs : ∀ h ∈ hs, 1 ≤ h ∧ h ≤ U ^ (1 / (10 * (k : ℝ)))) :
    U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ∧
    |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ≤ U ^ (-(2 : ℝ) / 5) := by
  have hU0 : 0 < U := by linarith
  obtain ⟨hplo, hphi⟩ := logarithmic_shift_product hU hk hs hlen hhs
  have hbase0 : 0 ≤ |Z| * U ^ (-((k : ℝ) + 1)) := by positivity
  constructor
  · exact hlower.trans (le_mul_of_one_le_right hbase0 hplo)
  · calc
      |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ≤
          U ^ (-(1 : ℝ) / 2) * U ^ ((1 : ℝ) / 10) :=
        mul_le_mul hupper hphi (by linarith) (by positivity)
      _ = U ^ (-(2 : ℝ) / 5) := by rw [← Real.rpow_add hU0]; norm_num

end JointDickman

end

end OAI
