module

public import ArtinMatthews.SourceLocalMultiplicativeShell
public import ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
public import ArtinMatthews.SourceKPRetainedTinySixth
public import ArtinMatthews.StandardLocalBall
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Local sixth-power class indicators preserve the retained profile
bounds under multiplication by a continuous unitary character. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain ClassFieldTheory SourcePhysical Filter
open scoped NumberField Classical Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "Q" => PowerClassGroup L 6
local notation "cl" => powerClass L 6

private theorem sourceKPRetainedLocalSixthPowers_isOpen :
    IsOpen (((powMonoidHom (6 : ℕ) : Lˣ →* Lˣ).range : Subgroup Lˣ) : Set Lˣ) := by
  obtain ⟨N, _, hroot⟩ := sourceKPRetained_tiny_sixth K P
  let f (z : Lˣ) : L := (z : L) - 1
  have hf : Continuous f := Units.continuous_val.sub continuous_const
  have h1 : f 1 = 0 := sub_self 1
  have h0 : f 1 ∈ sourceLocalBall K P (-(N : ℤ)) := by
    rw [h1]
    exact (sourceLocalOpenBall K P (-(N : ℤ))).zero_mem
  apply Subgroup.isOpen_of_mem_nhds (g := (1 : Lˣ))
  filter_upwards [hf.continuousAt ((sourceLocalBall_isOpen K P _).mem_nhds h0)] with z hz
  exact hroot z hz

theorem sourceKPRetainedLocalSixthClass_fiber_isClopen (r : Q) :
    IsClopen {z : Lˣ | cl z = r} := by
  let H : Subgroup Lˣ := (powMonoidHom (6 : ℕ) : Lˣ →* Lˣ).range
  let H₀ : OpenSubgroup Lˣ := ⟨H, sourceKPRetainedLocalSixthPowers_isOpen K P⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective H r
  change cl u = r at hu
  rw [← hu]
  have he : {z : Lˣ | cl z = cl u} = (fun z : Lˣ => z / u) ⁻¹' (H : Set Lˣ) := by
    ext z
    change cl z = cl u ↔ z / u ∈ H
    rw [← (QuotientGroup.eq_one_iff (z / u)), ← div_eq_one, ← map_div]
    rfl
  rw [he]
  exact H₀.isClopen.preimage (continuous_id.div_const u)

def sourceKPRetainedLocalClassIndicator (r : Q) (z : Lˣ) : ℂ :=
  {v : Lˣ | cl v = r}.indicator (fun _ => 1) z

theorem sourceKPRetainedLocalClassIndicator_apply (r : Q) (z : Lˣ) :
    sourceKPRetainedLocalClassIndicator K P r z = if cl z = r then 1 else 0 :=
  rfl

theorem sourceKPRetainedLocalClassIndicator_continuous (r : Q) :
    Continuous (sourceKPRetainedLocalClassIndicator K P r) :=
  (sourceKPRetainedLocalSixthClass_fiber_isClopen K P r).continuous_indicator continuous_const

/-- The literal local factor in a retained class tensor. -/
def sourceKPRetainedLocalClassProfile (χ : Lˣ →* ℂˣ) (r : Q) (V : Lˣ → ℂ) (z : Lˣ) : ℂ :=
  (χ z : ℂ) * sourceKPRetainedLocalClassIndicator K P r z * V z

theorem sourceKPRetainedLocalClassProfile_norm_le (χ : Lˣ →* ℂˣ) (r : Q) (V : Lˣ → ℂ)
    (hχ : ∀ z : Lˣ, ‖(χ z : ℂ)‖ = 1) (z : Lˣ) :
    ‖sourceKPRetainedLocalClassProfile K P χ r V z‖ ≤ ‖V z‖ := by
  by_cases hz : cl z = r <;>
    simp [sourceKPRetainedLocalClassProfile, sourceKPRetainedLocalClassIndicator_apply, hz,
      norm_mul, hχ]

theorem sourceKPRetainedLocalClassProfile_data (χ : Lˣ →* ℂˣ) (r : Q) (V : Lˣ → ℂ)
    (hχ : Continuous χ) (hχnorm : ∀ z : Lˣ, ‖(χ z : ℂ)‖ = 1)
    (hV : Continuous V ∧ ∃ n : ℤ, ∃ A : ℝ, 0 < A ∧
      (∀ z : Lˣ, z ∉ sourceLocalMulBall K P n → V z = 0) ∧
      ∀ z : Lˣ, z ∈ sourceLocalMulBall K P 0 → ‖V z‖ ≤ A * ‖(z : L)‖ ^ (1 / 3 : ℝ)) :
    Continuous (sourceKPRetainedLocalClassProfile K P χ r V) ∧
    ∃ n : ℤ, ∃ A : ℝ, 0 < A ∧
      (∀ z : Lˣ, z ∉ sourceLocalMulBall K P n → sourceKPRetainedLocalClassProfile K P χ r V z = 0) ∧
      ∀ z : Lˣ, z ∈ sourceLocalMulBall K P 0 →
        ‖sourceKPRetainedLocalClassProfile K P χ r V z‖ ≤ A * ‖(z : L)‖ ^ (1 / 3 : ℝ) := by
  obtain ⟨hV, n, A, hA, hcut, hsmall⟩ := hV
  refine ⟨((Units.continuous_val.comp hχ).mul
    (sourceKPRetainedLocalClassIndicator_continuous K P r)).mul hV, n, A, hA, ?_, ?_⟩
  · intro z hz
    simp only [sourceKPRetainedLocalClassProfile, hcut z hz, mul_zero]
  · intro z hz
    exact (sourceKPRetainedLocalClassProfile_norm_le K P χ r V hχnorm z).trans (hsmall z hz)

end
end ArtinMatthews
