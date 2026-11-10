module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Henselian
public import ArtinMatthews.HenselPowerUnits
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Strong Hensel power units are actual field norms, also when the power
exponent is a multiple of the local field degree. -/
noncomputable section
namespace ArtinMatthews.HenselPower
open IsLocalRing

variable {R K L : Type*} [CommRing R] [HenselianLocalRing R]
variable [Field K] [Field L] [Algebra R K] [Algebra K L] [FiniteDimensional K L]

omit [HenselianLocalRing R] in
/-- A power whose exponent is a multiple of the actual extension degree is
an actual norm, with an explicit unit witness in the extension field. -/
theorem exists_unit_norm_of_pow (n : ℕ) (hd : Module.finrank K L ∣ n)
    (u v : Rˣ) (hv : v^n = u) :
    ∃ w : Lˣ, Units.map (Algebra.norm K : L →* K) w =
      Units.map (algebraMap R K).toMonoidHom u := by
  obtain ⟨m, hm⟩ := hd
  let vK : Kˣ := Units.map (algebraMap R K).toMonoidHom v
  refine ⟨Units.map (algebraMap K L).toMonoidHom (vK^m), ?_⟩
  apply Units.ext
  simp only [Units.coe_map, Units.val_pow_eq_pow_val]
  change Algebra.norm K (algebraMap K L ((vK : K)^m)) = algebraMap R K (u : R)
  rw [Algebra.norm_algebraMap, ← pow_mul, Nat.mul_comm m, ← hm]
  change (algebraMap R K (v : R)) ^ n = algebraMap R K (u : R)
  rw [← map_pow]
  exact congrArg (fun z : Rˣ => algebraMap R K (z : R)) hv

/-- Strong Hensel power lifting implies membership in the genuine field-norm
subgroup for every finite extension of degree dividing the lifting exponent. -/
theorem exists_unit_norm_of_sub_one_mem (n : ℕ) (hn : 0 < n)
    (hd : Module.finrank K L ∣ n) (u : Rˣ)
    (hu : (u : R) - 1 ∈ Ideal.span {(n : R)^2} * maximalIdeal R) :
    ∃ w : Lˣ, Units.map (Algebra.norm K : L →* K) w =
      Units.map (algebraMap R K).toMonoidHom u := by
  obtain ⟨v, hv⟩ := exists_unit_pow_of_sub_one_mem n hn u hu
  exact exists_unit_norm_of_pow n hd u v hv

/-- The exact-degree version used at a completed finite place. -/
theorem exists_unit_norm_of_degree_sub_one_mem (u : Rˣ)
    (hu : (u : R) - 1 ∈ Ideal.span {(Module.finrank K L : R)^2} * maximalIdeal R) :
    ∃ w : Lˣ, Units.map (Algebra.norm K : L →* K) w =
      Units.map (algebraMap R K).toMonoidHom u :=
  exists_unit_norm_of_sub_one_mem (Module.finrank K L) Module.finrank_pos (dvd_refl _) u hu

/-- A congruence modulo D*n² suffices whenever D lies in the local maximal
ideal; this is the ramified-place input for the discriminant-degree modulus. -/
theorem exists_unit_norm_of_mul_congruence (n : ℕ) (hn : 0 < n)
    (hd : Module.finrank K L ∣ n) (u : Rˣ) (D : R)
    (hD : D ∈ maximalIdeal R)
    (hu : (u : R) - 1 ∈ Ideal.span {D * (n : R)^2}) :
    ∃ w : Lˣ, Units.map (Algebra.norm K : L →* K) w =
      Units.map (algebraMap R K).toMonoidHom u := by
  apply exists_unit_norm_of_sub_one_mem n hn hd u
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hu
  apply Ideal.mem_span_singleton_mul.mpr
  refine ⟨D * c, (maximalIdeal R).mul_mem_right c hD, ?_⟩
  rw [hc]
  ring

end ArtinMatthews.HenselPower
